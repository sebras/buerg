	page	75,132
	title	XONE - Make one ARC file from a member file

; usage:
;	   XONE inputname[.ARC] [filename] [outputname] [/R]
;
; remarks:
;	The 'inputname' is required. It defines the ARC archive
;	file which contains the member files that you want to extract.
;	The extension defaults to .ARC.
;
;	The 'filename' is optional. If omitted, all files in the
;	archive are extracted. If supplied, only that file in the
;	archive that matches the 'filename' is extracted.
;	Each extracted file is created in the ARC format using the
;	the original file name.
;
;	The 'outputname' is optional. If supplied, it defines the name
;	to be used for the extracted file. To use this operand, you must
;	also supply the 'filename' operand to extract a single file.
;
; restrictions:
;	XONE was written by Vernon Buerg and is for use without
;	restrictions. Please try to distribute this program as-is,
;	and without modification.

	.xlist
print	macro	name			; display a field
	mov	dx,offset name
	call	prints
	endm

printl	macro	text,ctl		; display a literal
	local	txt,nxt
	mov	dx,offset txt
	call	prints
	jmp	nxt
txt	db	cr,lf,&text
	ifnb	< ctl>
	db	cr,lf,stopper
	else
	db	stopper
	endif
nxt	equ	$
	endm

	.sall
	.list

header	struc				; archive header
mbrcode db	0			;  compression code
mbrname db	13 dup (0)		;  file name
mbrsize dw	0,0			;  file size in archive
mbrdate dw	0			;  creation date
mbrtime dw	0			;  creation time
mbrcrc	dw	0			;  cyclic redunancy check
mbrlen	dw	0,0			;  true file size, bytes
header	ends

cseg	segment public para 'CODE'
	assume	cs:cseg,ds:cseg,es:cseg
	org	100h

xone	proc	far
	jmp	start			; do our thing

version db	cr,'   ',cr,lf          ; overlay jmp above
	db	'  XONE   Make ARC file from member file(s) ',cr,lf
	db	'  ----   Version 2.3 - by Vern Buerg',cr,lf,stopper
usage	db	cr,lf,'  usage: XONE  archive[.ARC]  [filespec] [output] [/R]'
	db	cr,lf,eof
	db	stopper 		; 2.3, oops
	page
;
;	return with error

error:	mov	ax,cs			; insure seg regs
	mov	ds,ax			;  for proper exit
	mov	sp,cs:stkptr
	mov	errlvl,1		; set bad return code
;	mov	dl,7			; send bel char
;	mov	ah,2			;  to standard output
;	int	21h

;	set DOS error level and exit

exit:	mov	sp,cs:stkptr		; just in case
	mov	al,errlvl		; return code
	mov	ah,4ch			; exit function
	int	21h

	subttl	'--- constants, equates and work areas'
	page

cr	equ	13
lf	equ	10
bel	equ	7
tab	equ	9
eof	equ	26

stopper equ	255		; end of display line indicator
arcmark equ	26		; special archive marker
xoneer	equ	9		; highest compression code used      ;2.2

stkptr	dw	0		; stack pointer upon entry
errlvl	db	0		; dos error level returned
psp	dw	0		; addr of psp

prompt	db	' already exists, re-use it? (y/N) ',stopper
answer	db	'n',cr,stopper
found	db	0		; indicates if found a member
reuse	db	0		; non-zero means overwrite existing file(s)

notfnd	db	cr,'  Member file not found - '
member	db	13 dup (0),0	; selected member name
	db	cr,lf,stopper

archdl	dw	0		; ARC file handle
arcname db	76 dup (stopper)

outmsg	db	' -> '          ; tells you what is being used
outname db	76 dup (0)	; output file name

;	i/o control variables

inbufsz equ	18*1024 	; size of input buffer
inadr	dw	offset inbuf	; offset to input buffer
inptr	dw	offset inbuf	; offset to current byte
insize	dw	inbufsz 	; size of input buffer
inlen	dw	0		; bytes left in buffer
incurh	dw	0		; current file offset
incurl	dw	0		;  low word

outbufsz equ	18*1024 	; size of output buffer
outlen	dw	outbufsz	; bytes empty in output buffer
outadr	dw	offset outbuf	; offset to output buffer
outptr	dw	offset outbuf	; spot for next output char
outsize dw	outbufsz	; size of output buffer
outhdl	dw	0		; output file handle

vline	db	cr,lf
vstyle	db	'        '      ; compression method
	db	'ed: '
vname	db	12 dup (0),0
	db	stopper,0

styles	db	'     sav'      ; 1 = old, no compression
	db	'     Sav'      ; 2 = new, no compression
	db	'    Pack'      ; 3 = dle for repeat chars
	db	'  Squeez'      ; 4 = huffman encoding
	db	'  crunch'      ; 5 = lz, no crc
	db	'  crunch'      ; 6 = lz with crc
	db	'     SEA'      ; 7 = internal SEA use
	db	'  Crunch'      ; 8 = new lz with crc
	db	'  squash'      ; 9 = pk squashing

wtg	dw	0		; index into where table

where	dw	offset copy1	; offset to routines for each type
	dw	offset copy2
	dw	offset unpack3
	dw	offset unsqueez4
	dw	offset uncrunch5
	dw	offset uncrunch6
	dw	offset uncrunch7
	dw	offset uncrunch8
	dw	offset unsquash9

	subttl	'--- mainline processing'
	page
;
;	gather command line operands

start:
	mov	stkptr,sp		; save stack ptr
	mov	ax,cs
	mov	ds,ax			; set local data seg
	mov	cx,es
	mov	psp,cx			; save psp addr
	mov	es,ax

	print	version 		; display program version

	mov	si,80h			; get command line operand
	sub	cx,cx
	or	cl,byte ptr [si]	; any operand?
	jnz	parm1

parm_error:
	print	usage			; no, gotta have the ARC name
	jmp	error

;	pick off any trailing '/R' parameter

parm1:	inc	si			; point to operand
	mov	bx,si
	add	bx,cx			; point to end of command line
	cmp	word ptr -2[bx],'R/'    ; is reuse specified?
	je	parm1r
	cmp	word ptr -2[bx],'r/'
	jne	parm2
parm1r: or	reuse,1 		; indicate no checking
	mov	word ptr -2[bx],0d0dh	; stop command line here
	sub	cx,2			; remove /R from command line
	jle	parm_error		; oops, something is missing

;	get first operand - input archive file name

parm2:	lodsb				; strip leading blanks
	cmp	al,' '
	loope	parm2
	mov	di,offset arcname
	stosb

parm3:	lodsb				; copy ARC filename
	cmp	al,cr			; end of name?
	je	parm4
	cmp	al,' '                  ; delimiter?
	je	parm4
	cmp	al,tab			; delimiter?
	je	parm4
	cmp	al,','                  ; delimiter?
	je	parm4
	stosb
	cmp	al,'.'                  ; got extension now?
	je	parm5			; yup, that's nice
	loop	parm3

parm4:	mov	ax,'A.'                 ; append default ext
	stosw
	mov	ax,'CR'
	stosw
	jmp	short parm6

;	strip trailing blanks looking for second operand

parm5:	lodsb				; next ext char
	cmp	al,cr			; end of it?
	je	parm6
	cmp	al,' '                  ; delimiter?
	je	parm6
	cmp	al,tab			; another delimiter?
	je	parm6
	stosb				; copy supplied extension
	loop	parm5
parm5a: dec	di			; back up to end of ext

parm6:	mov	al,0			; append asciiz stopper
	stosb

;	copy optional second (file selection) operand

	or	cx,cx			; another operand?
	jz	parm_done		; nope, extract all files
	mov	di,offset member
parm7:	lodsb
	cmp	al,cr			; end of operand?
	je	parm20			; yes, done
	cmp	al,' '                  ; delimiter for third operand?
	je	parm10
	cmp	al,tab
	je	parm10
	cmp	al,'a'                  ; lower case?
	jb	parm8
	sub	al,32
parm8:	stosb
	loop	parm7
parm9:	mov	ax,0ff00h		; append asciiz stopper
	stosw
	jmp	short parm_done

;	get third operand, if any, as output file name

parm10: sub	cx,1			; account for delimiter
	jle	parm_done
	mov	di,offset outname	; third operand is target filename
parm11: lodsb
	cmp	al,' '                  ; strip leading blanks
	loope	parm11
	cmp	al,cr			; ending c/r?
	je	parm_done		;  just trailing blanks, then
	jcxz	parm20
parm12: stosb				; blindly copy the rest
	lodsb
	cmp	al,cr
	loopne	parm12
parm20: mov	ax,0ff00h		; append stoppers
	stosw

parm_done:				; hope we've got everything
	call	openarc 		; access the archive file
	jnc	xonenext
	ret

	page
;
;	process next archive header entry

xonenext:
	call	gethdr			; load next header
	jnc	xone2			; get CF at end of file, etc
	jmp	exit			; all done

xone2:	cmp	archdr.mbrcode,0	; archive eof?
	jne	xone2a			; nope, keep on truckin

	printl	' '                     ; blank line

	call	closarc 		; close file
	cmp	member,0		; selecting one file?
	je	xone_ok 		; no, skip next
	cmp	found,0 		; and did we get it?
	jne	xone_ok
	print	notfnd
	printl	' '
xone_ok:
	jmp	exit			; depart

xone2a:
	cmp	member,0		; selecting one file?
	je	xonego			; no, skip next
	mov	si,offset member	; yes, compare names
	mov	di,offset archdr.mbrname
	mov	cx,13
xonesel:
	lodsb
	cmp	al,0			; end of name
	je	xonego			; yes, select the file
	cmp	al,byte ptr [di]	; match so far?
	jne	xone_agn		; no, skip this file
	inc	di
	loop	xonesel
	jmp	short xonego		; it matches

;	the following is used to skip to the next ARC entry

xone_agn:
	mov	cx,word ptr archdr.mbrsize+2
	mov	dx,word ptr archdr.mbrsize
	add	dx,incurl		; add current hdr offset
	adc	cx,0
	add	cx,incurh
	mov	ax,4200h		; skip over file data
	mov	bx,archdl
	int	21h
	mov	incurh,dx		; new position
	mov	incurl,ax
	mov	inlen,0 		; reset read buffer
	jmp	xonenext

xonego:
	mov	di,offset vname 	; copy file name
	mov	si,offset archdr.mbrname
	mov	cx,13
xone3:
	lodsb
	cmp	al,0			; end of name?
	je	xone4
	stosb
	loop	xone3
	jmp	short xone5
xone4:
	mov	al,0			; pad with asciiz
	rep	stosb

xone5:
	sub	bx,bx			; determine style
	mov	bl,archdr.mbrcode
	shl	bx,1
	mov	wtg,bx			; save where-to-go offset
	shl	bx,1
	shl	bx,1			; times 8 for style table
	lea	si,styles-8[bx] 	; get ptr to style name
	mov	di,offset vstyle
	mov	cx,8
	rep	movsb

	print	vline			; display this file info
	cmp	outname,0		; specified different output?
	je	xone6
	print	outmsg

xone6:
	call	create			; allocate new file

	mov	bx,wtg			; where to go
	jmp	where-2[bx]		; let 'er rip

	subttl	- Extract current member file
	page
;
;	1 - straight copy of all formats

copy2:
unpack3:
unsqueez4:
uncrunch5:
uncrunch6:
uncrunch7:
uncrunch8:
unsquash9:

copy1:
	mov	si,offset newhdr	; copy arc header first
	mov	cx,hdrlen
copyhdr:
	lodsb
	call	putc
	loop	copyhdr

	mov	cx,word ptr archdr.mbrsize
	mov	dx,word ptr archdr.mbrsize+2
xone7:
	call	getc			; straight copy
	jc	xoner1
	call	putc
	sub	cx,1
	sbb	dx,0
	or	cx,cx			; any more bytes?
	jnz	xone7			; yup, keep on truckin'
	or	dx,dx
	jnz	xone7
	jmp	xonemore

xoner1: printl	'Premature EOF reading '
	print	vname
	jmp	error

xonemore:
	mov	al,arcmark		; append normal arc mark
	call	putc
	mov	al,0
	call	putc

	call	putblk			; flush buffer
	call	closout 		; close output
	jmp	xonenext

	subttl	' - miscellaneous subroutines'
	page

openarc proc	near			; open new archive
	push	bx
	mov	dx,offset arcname
	mov	ax,3d02h		; for input and output
	int	21h
	jc	openerr
	mov	archdl,ax		; save file handle
	clc
	printl	'  Using: '
	print	arcname
	printl	' '
	pop	bx
	ret
openerr:
	printl	'Unable to open archive: '
	print	arcname
	jmp	error
openarc endp


closarc proc	near
	push	bx
	mov	bx,archdl		; previous handle
	or	bx,bx			; already open?
	jz	closed
	mov	ah,3eh			; yes, so close it
	int	21h
closed: mov	archdl,0
	pop	bx
	ret
closarc endp

note	proc	near			; note location of header
	push	bx			; in ARC file
	sub	cx,cx
	sub	dx,dx
	mov	ax,4201h		; get file pointer to EOF
	mov	bx,archdl
	int	21h
	mov	incurh,dx		; save hdr position
	mov	incurl,ax
	pop	bx
	ret
note	endp

create	proc	near			; allocate new file
	push	bx
	mov	found,255		; indicate member extracted
	test	reuse,1 		; want to over-write?
	jnz	create1 		; yup, life in the danger zone
	mov	dx,offset outname	; output specified?
	cmp	byte ptr outname,0
	jne	open_it
	mov	dx,offset vname 	; no, use archive member file name

open_it:
	mov	ax,3d00h		; see if file already exists
	int	21h
	jc	create1 		; looks good so far

	mov	bx,ax			; close found file
	mov	ah,3eh
	int	21h

	print	prompt			; ask to re-use
	mov	ah,0			; get response
	int	16h
	mov	answer,al		; echo response
	mov	dx,offset answer
	call	prints

	cmp	answer,'Y'              ; get the okay?
	je	create1
	cmp	answer,'y'
	je	create1
	jmp	xone_agn

create1:
	mov	dx,offset outname	; output specified?
	cmp	byte ptr outname,0
	jne	create_it
	mov	dx,offset vname 	; actual file name
create_it:
	sub	cx,cx			; normal attribute
	mov	ah,3ch
	int	21h
	jc	creater 		; something failed
	mov	outhdl,ax
	pop	bx
	ret
creater:
	printl	'CREATE failed - '
	print	vname
	jmp	error
create	endp


closout proc	near			; close output file
	mov	bx,outhdl		; close output
	or	bx,bx			; was it open?
	jz	closedout		; no, that's funny
	mov	ah,3eh
	int	21h
closedout:
	ret
closout endp

;
;	print string like int 21h function 9

prints	proc	near			; dx has offset to string
	push	si			;  ending in char x'ff'
	push	bx
	push	cx
	mov	si,dx			; pointer to text
	sub	cx,cx			; length of text
ps1:	lodsb
	cmp	al,stopper		; ending stopper code?
	je	ps9
	inc	cx			; no, increment length
	jmp	short ps1

ps9:	mov	ah,40h			; write to stdout
	mov	bx,1
	int	21h

	pop	cx			; recover registers
	pop	bx
	pop	si
	ret
prints	endp

	subttl	' - i/o subroutines'
	page

getc	proc	near			; return next byte in al
	push	si			;  or cf=1 for eof
getc1:
	sub	inlen,1 		; any left in buffer
	jns	getc2			; yes, pick it up
	call	getblk
	jnc	getc1
	pop	si			; return cf=1 at eof
	ret
getc2:
	mov	si,inptr		; offset to next byte
	lodsb
	mov	inptr,si
	add	incurl,1		; bump file offset
	adc	incurh,0
	pop	si
	ret
getc	endp

getblk	proc	near			; read next block
	push	ax
	push	bx
	push	cx
	push	dx
	mov	ah,3fh			; read from handle
	mov	bx,archdl		; arc file handle
	mov	cx,inbufsz		; input buffer size
	mov	dx,offset inbuf 	; offset to input buffer
	mov	inptr,dx
	int	21h
	jc	getblkr 		; oops
	or	ax,ax			; anything read?
	jnz	getblka
	stc				; no, set cf=1 for eof
	jmp	short getblkx		; and exit
getblka:
	mov	inlen,ax		; return count of bytes read
	clc
getblkx:
	pop	dx
	pop	cx
	pop	bx
	pop	ax
	ret

getblkr:
	printl	"I/O error reading from "
	print	arcname
	jmp	error			; gotta quit
getblk	endp

	page

putc	proc	near
	cmp	outlen,0		; any room left?
	jg	putc1			; yes, stuff into buffer
	call	putblk			; no, write out buffer
	jnc	putc
	ret				; return cf=1 for error

putc1:	mov	di,outptr		; offset to next spot
	stosb
	mov	outptr,di		; update ptr for next time
	dec	outlen
	clc				; return cf=0 for okay
	ret

putblk: push	ax			; save regs
	push	bx
	push	cx
	push	dx
	mov	bx,outhdl		; output file handle
	mov	cx,outsize		; buffer size
	mov	ax,cx
	sub	cx,outlen		; less bytes unfilled
	mov	outlen,ax		; reset buffer size free
	mov	dx,offset outbuf	; offset to buffer
	mov	outptr,dx
	jcxz	putblk0 		; have nothing to write?
	mov	ah,40h			; write to a file
	int	21h
	jc	putcerr 		; write failed?
	cmp	ax,cx			; wrote it all?
	jne	putcerr
putblk0:
	clc				; clear CF error inidcator
	pop	dx			; recover regs
	pop	cx
	pop	bx
	pop	ax
	ret

putcerr:
	printl	'I/O error writing to '
	print	vname
	jmp	error
putc	endp

	subttl	'--- load next archive header'
	page

gethdr	proc	near
	mov	cx,128			; gotta look for the damn thing
gethdr2:
	call	getc			; get next file byte
	jc	gethdrr1		; premature eof
	cmp	al,arcmark		; start of header?
	je	gethdr3 		; yup, let's start cookin
	loop	gethdr2
gethdrr1:
	printl	"Invalid archive format!"
	jmp	error

gethdr3:
	call	getc			; get version code
	jc	gethdrr1
	mov	archdr.mbrcode,al
	cmp	al,xoneer		; reasonable code?
	ja	gethdrr1		; nope, funny stuff
	cmp	al,0			; archive eof?
	je	gethdr9 		; yup done

	mov	cx,13			; get member name
	mov	di,offset archdr.mbrname
gethdr4:
	call	getc
	jc	gethdrr1
	stosb
	loop	gethdr4
gethdr5:
	mov	cx,10			; length remaining
	cmp	archdr.mbrcode,1	; old format?
	je	gethdr6 		; yes, it's short
	mov	cl,14
gethdr6:
	mov	di,offset archdr.mbrsize
gethdr7:
	call	getc
	jc	gethdrr1
	stosb
	loop	gethdr7
gethdr8:
	cmp	archdr.mbrcode,1	; old format?
	jne	gethdr9 		; if so, it's short
	mov	si,offset mbrsize
	mov	di,offset mbrlen
	mov	cx,4
	rep	movsb
gethdr9:
	clc
	ret

gethdrr2:
	printl	'Invalid archive header'
	jmp	error
gethdr	endp

	subttl	'--- i/o data areas'
	page

xone	endp

newhdr	db	arcmark 		; starts an arc header
archdr	equ	$			; i/o area for a header
hdrlen	equ	size header + 1 	; length of normal ARC header

inbuf	equ	$ + 64			; input buffer

outbuf	equ	inbuf + inbufsz 	; output buffer

lastbyt equ	outbuf + outbufsz

pgmsize equ	(lastbyt - xone + 1024) /16	; paragraphs in program

cseg	ends
	end	xone
