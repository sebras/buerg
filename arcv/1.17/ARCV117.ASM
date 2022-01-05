	page	80,132
	title	ARCV - Verbose ARC directory listing

; history:
;	version 1.00 - 1/5/86
;	version 1.03 - 1/10/86
;		released for general use
;	version 1.04 - 1/19/86
;		make displays MS-DOS compatible
;	version 1.05 - 1/23/86
;		supports ARC 5.0 new formats
;	version 1.06 - 1/26/86
;		correct total SF
;	version 1.07 - 3/22/86
;		change open for input only
;	version 1.08 - 3/28/86
;		correct zero divide problem
;	version 1.09 - 4/08/86
;		check SF for funny archives
;	version 1.10 - 4/18/86
;		correct divide overflow problem
;	version 1.11 - 4/23/86
;		correct stowage factor
;	version 1.12 - 4/26/86
;		correct sending totals for no files
;	version 1.13 - 5/11/86
;		expand search for header arcmark
;	version 1.14 - 5/21/86
;		change for 'No files found' error on clones
;	version 1.15 - 6/14/86
;		use 'filename' if no files found to use DPATH
;	version 1.16 - 12/31/86
;		add entry for type 9 format, squashing
;	version 1.17 - 1/27/86
;		add DOS 3.x file sharing

	.xlist
print	macro	name			; display a field
	mov	dx,offset name
	call	prints
	endm

printl	macro	text			; display a literal
	local	txt,nxt
	mov	dx,offset txt
	call	prints
	jmp	nxt
txt	db	cr,lf,text
	db	stopper
nxt	equ	$
	endm

beep	macro				; sound the horn
	mov	dl,7
	mov	ah,2
	int	21h
	endm
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

arcv	proc	far
	mov	stkptr,sp		; save stack ptr
	mov	ah,30h			; get dos version
	int	21h
	mov	dosver,al		; save for open checks
	cmp	al,2			; version 2 or later?
	jb	badver			; no, gotta quit
	jmp	start			; do our thing

;	return with error

badver: print	vermsg			; version 2 red'q
error:	mov	ax,cs			; insure seg regs
	mov	ds,ax			;  for proper exit
	mov	sp,cs:stkptr
	mov	errlvl,1		; set bad return code
	beep
	jmp	arcv2a			; produce totals anyway

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

stopper equ	0		; end of display line indicator
arcmark equ	26		; special archive marker
arcver	equ	9		; highest compression code used

stkptr	dw	0		; stack pointer upon entry
errlvl	db	0		; dos error level returned
flags	db	0		; find-first return code
dosver	db	0		; major dos version
archdl	dw	0		; file handle

arctitl db	cr,lf,'Archive:  '
arcname db	76 dup (stopper)

fileptr dw	0		; ptr to filename part of arcname

	subttl	'--- i/o control variables'
	page

usage	db	cr,lf
	db	'ARCV 1.17 - Verbose ARC directory display - V.Buerg'
	db	cr,lf,lf,'  Usage:  arcv [d:][\path\]filespec[.ARC]'
	db	cr,lf,stopper

vermsg	db	cr,lf,'Wrong DOS version',cr,lf,stopper

inbufsz equ	30		; size of input buffer, seems best
inadr	dw	offset inbuf	; offset to input buffer
inptr	dw	offset inbuf	; offset to current byte
insize	dw	inbufsz 	; size of input buffer
inlen	dw	0		; bytes left in buffer

;	display lines for verbose

vhdr	db	cr,lf
	db	cr,lf,'Name          Length    Stowage    SF   Size now  Date       Time    CRC '
	db	cr,lf,'============  ========  ========  ====  ========  =========  ======  ===='
	db	stopper

vline	db	cr,lf
vname	db	14 dup (' ')
vlength db	'       0  '    ; length in archive
vstyle	db	'          '    ; compression method
vfactor db	' xx%  '        ; compression factor
vsize	db	10 dup (' ')    ; actual file bytes
vdate	db	'dd '           ; creation date
 vmonth db	'mmm '
 vyear	db	'yy  '
 vtime	db	'hh:mm   '      ; creation time
 vcrc	db	'xxxx'          ; crc in hex
	db	stopper

hundred dw	100		; for computing percentages
totsf	dw	0,0		; average stowage factor
totlen	dw	0,0		; total of file lengths
totsize dw	0,0		; total of file sizes
totmbrs dw	0		; total number of files

;	final totals line

vthdr	db	cr,lf,'*total    '
 vtmbrs db	'    '
 vtlen	db	8 dup (' '),'  '
	db	10 dup (' ')
 vtsf	db	'   %  '
 vtsize db	8 dup (' ')
	db	cr,lf		; for tom
	db	stopper
 sign	db	' '

styles	db	'  ----- '      ; 1 = old, no compression
	db	'  ----- '      ; 2 = new, no compression
	db	' Packed '      ; 3 = dle for repeat chars
	db	'Squeezed'      ; 4 = huffman encoding
	db	'crunched'      ; 5 = lz, no dle
	db	'crunched'      ; 6 = lz with dle
	db	'Crunched'      ; 7 = lz with readjust
	db	'Crunched'      ; 8 = lz with readjust and dle
	db	'Squashed'      ; 9 = modified lzw, no dle

months	db	'Jan Feb Mar Apr May Jun Jul Aug Sep Oct Nov Dec '

	subttl	'--- mainline processing'
	page
;
;	determine if command line or menu driven mode

start:
	mov	si,80h			; offset to command line
	sub	cx,cx
	or	cl,byte ptr [si]	; any operand?
	jnz	parm1
	print	usage
	jmp	exit

;	copy firt command line operand

parm1:	inc	si			; point to operand
parm2:	lodsb				; strip leading blanks
	cmp	al,' '
	loope	parm2
	mov	di,offset arcname
	stosb
parm3:	lodsb				; copy filename
	cmp	al,cr			; end of name?
	je	parm4
	cmp	al,' '                  ; don't know why this is here
	je	parm4
	stosb
	loop	parm3
parm4:
	mov	si,offset arcname+75	; end of filename stuff
	std
	mov	cl,76			; search for last path
parm5:
	lodsb
	cmp	al,'/'                  ; funny path delimiter?
	je	parm6
	cmp	al,'\'                  ; normal path delimiter?
	je	parm6
	cmp	al,':'                  ; bumped into drive?
	je	parm6
	loop	parm5
	dec	si
parm6:
	cld
	add	si,2			; point to where filename goes
	mov	fileptr,si		; and save for later

;	add default ARC extension if necessary

	mov	si,fileptr		; start of filespec
	mov	cx,13
parm10:
	lodsb
	cmp	al,0			; end of name?
	je	parm11
	cmp	al,'.'                  ; got extension?
	je	parm12
	loop	parm10
parm11:
	mov	di,si			; ptr to end of name
	dec	di
	mov	ax,'A.'                 ; default extension
	stosw
	mov	ax,'CR'
	stosw
	mov	ax,0FF00h		; append stoppers
	stosw
parm12:

;	find first matching file

getfirst:
	mov	dx,offset dta		; set local dta for murkers
	mov	ah,1ah
	int	21h

	mov	dx,offset arcname	; find first matching file
	sub	cx,cx			; normal attribute
	mov	ah,4eh
	int	21h
	mov	flags,al		; indicate find-first status
	or	ax,ax			; any return code?
	jz	parm7
	jmp	not_found		; in case of DPATH utility
nofiles:
	printl	'No file(s) found'
	jmp	error

getnext:
	mov	ah,4fh			; get next file name
	int	21h
	jc	alldone
	or	ax,ax
	jz	parm7
alldone:
	jmp	exit

;	set up next matching file name

parm7:
	mov	si,offset dta+30	; point to filename found
	mov	di,fileptr		; and overlay old name
	mov	cx,13
	rep	movsb

;	re-initialize

not_found:
	sub	ax,ax			; reset totals counters
	mov	totmbrs,ax
	mov	totsize,ax
	mov	totsize+2,ax
	mov	totlen,ax
	mov	totlen+2,ax
	mov	totsf,ax
	mov	inlen,ax
	mov	dx,offset inbuf
	mov	inptr,dx

	call	openarc 		; see if archive exists
	jnc	arcv1
	ret

	page
;
;	process next archive header entry

arcv1:	print	arctitl
	print	vhdr

arcvnext:
	call	gethdr			; load next header
	jnc	arcv2
	jmp	exit			; all done

arcv2:	cmp	archdr.mbrcode,0	; archive eof?
	je	arcv2a
	jmp	arcvgo

arcv2a:
	mov	ax,totmbrs		; total files
	or	ax,ax			; are there any?
	jnz	format_totals
	jmp	skip_totals

format_totals:
	sub	dx,dx
	mov	si,offset vtmbrs-4
	call	format

	mov	dx,totlen+2		; total actual file size
	mov	ax,totlen
	mov	si,offset vtlen
	call	format

	mov	dx,totsize+2		; total achive file size
	mov	ax,totsize
	mov	si,offset vtsize
	call	format

; reduce the total size/length to word values

	mov	bx,totlen		; get actual file size
	mov	ax,totlen+2
	mov	cx,totsize		; length of file in archive
	mov	dx,totsize+2
arcv2b: or	ax,ax			; big number?
	jz	arcv2c			; nope, can use it
	shr	ax,1			; yup, divide by two
	rcr	bx,1
	shr	dx,1
	rcr	cx,1
	jmp	short arcv2b

arcv2c: mov	si,offset vtsf-5	; format stowage factor
	mov	ax,bx
	mov	sign,' '                ; whata kludge
	cmp	ax,cx			; arc is bigger than orig?
	jb	arcv2c1
	sub	ax,cx			; amount saved
	jmp	short arcv2f
arcv2c1:
	sub	ax,cx
	neg	ax
	mov	sign,'-'
arcv2f:
	mul	hundred 		; to percentage
	add	ax,50
	adc	dx,0			; round up percent
	or	bx,bx			; empty file?
	jnz	arcv2d
	mov	ax,100
	jmp	short arcv2e

arcv2d: div	bx
arcv2e: sub	dx,dx
	call	format

	mov	al,sign
	mov	vtsf,al
	print	vthdr			; display totals

skip_totals:
	call	closarc
	jmp	getnext

	page
;
;	format single line for each member

arcvgo:
	mov	di,offset vname 	; copy file name
	mov	si,offset archdr.mbrname
	mov	cx,13
arcv3:
	lodsb
	cmp	al,0			; end of name?
	je	arcv4
	stosb
	loop	arcv3
	jmp	short arcv5
arcv4:
	mov	al,' '                  ; pad with blanks
	rep	stosb
arcv5:
	inc	totmbrs

; reduce the size/length to word values

	mov	bx,archdr.mbrlen	; get actual file size
	mov	ax,archdr.mbrlen+2

	mov	cx,archdr.mbrsize	; length of file in archive
	mov	dx,archdr.mbrsize+2

arcv51: or	ax,ax			; big number?
	jz	arcv52			; nope, can use it
	shr	ax,1			; yup, divide by two
	rcr	bx,1
	shr	dx,1
	rcr	cx,1
	jmp	short arcv51

arcv52: mov	si,offset vfactor-5	; format stowage factor
	mov	ax,bx			; low word of actual size
	mov	sign,' '
	cmp	ax,cx			; arc member is larger?
	jb	arcv520
	sub	ax,cx			; amount saved
	jmp	arcv56
arcv520:
	sub	ax,cx
	neg	ax
	mov	sign,'-'
arcv56:
	mul	hundred 		; to percentage
	add	ax,50
	adc	dx,0			; round up percent
	or	bx,bx			; empty file?
	jnz	arcv53
	mov	ax,100
	jmp	short arcv54

arcv53: div	bx
arcv54: sub	dx,dx
	cmp	ax,100			; archive fouled?
	jbe	arcv55
	sub	ax,ax
arcv55:
	call	format
	mov	al,sign
	mov	vfactor,al

	sub	bx,bx			; determine style
	mov	bl,archdr.mbrcode
	mov	cl,3			; eight bytes each entry
	shl	bx,cl
	lea	si,styles-8[bx] 	; get ptr to style name
	mov	di,offset vstyle
	mov	cx,8
	rep	movsb

	mov	si,offset vsize 	; format file size
	mov	dx,archdr.mbrsize+2
	mov	ax,archdr.mbrsize
	add	totsize,ax
	adc	totsize+2,dx
	call	format

	mov	si,offset vlength	; format file length
	mov	dx,archdr.mbrlen+2
	mov	ax,archdr.mbrlen
	add	totlen,ax
	adc	totlen+2,dx
	call	format

	mov	ax,archdr.mbrdate	; format file date
	call	getdate

	mov	ax,archdr.mbrtime	; format file time
	call	gettime

	mov	ax,archdr.mbrcrc	; format crc in hex
	mov	di,offset vcrc
	call	cvh

	print	vline			; display this file info

	mov	cx,word ptr archdr.mbrsize+2
	mov	dx,word ptr archdr.mbrsize
	sub	dx,inlen		; less bytes read/unprocessed
	sbb	cx,0
	mov	ax,4201h		; skip over file data
	mov	bx,archdl
	int	21h
	mov	inlen,0 		; reset read buffer
	jmp	arcvnext

	subttl	' - miscellaneous subroutines'
	page

openarc proc	near			; open new archive
	push	bx
	mov	dx,offset arcname
	mov	ax,3d00h		; for input
	cmp	dosver,3		; can we share?
	jb	noshare
	or	al,40h			; yes, deny none
noshare:
	int	21h			; issue open
	jc	openerr
	mov	archdl,ax		; save file handle
	clc
	pop	bx
	ret
openerr:
	cmp	flags,0 		; find-first or open?
	je	open_err
	jmp	nofiles
open_err:
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

;
;	print string like int 21h function 9

prints	proc	near			; dx has offset to string
	push	si			;  ending in char x'ff'
	push	bx
	push	cx
	mov	si,dx
	sub	cx,cx
ps1:	lodsb
	cmp	al,stopper		; ending hex ff?
	je	ps9
	inc	cx			; incr text length
	jmp	ps1

ps9:	mov	ah,40h			; write to file
	mov	bx,1			; using std out
	int	21h

	pop	cx			; recover registers
	pop	bx
	pop	si
	ret
prints	endp

	page
;
;	format the time

time	record	hour:5,min:6,sec:5	;packed time

gettime proc	near			;format the date
	mov	di,offset vtime
	or	ax,ax			;it is zero?
	jz	gottime
	push	ax			;save date
	and	ax,mask hour		;get hour part
	mov	cl,hour 		;bits to shift
	shr	ax,cl
	call	cnvrt1
	stosw
	mov	al,':'
	stosb

gt3:	pop	ax			;get the time back
	and	ax,mask min		;get min part
	mov	cl,min			;bits to shift
	call	cnvrt
	stosw
gottime:ret
gettime endp

cnvrt2	proc	near			;convert to ascii
	call	cnvrt
	cmp	al,'0'                  ;suppress leading zero
	jne	cnvrtd
	mov	al,' '
	ret

cnvrt:	shr	ax,cl
cnvrt1: aam				;make al into bcd
	or	ax,'00'                 ; and to ascii
	xchg	al,ah
cnvrtd: ret
cnvrt2	endp

	page
;
;	format the date

date	record	yr:7,mo:4,dy:5		;packed date

getdate proc	near			;format the date
	or	ax,ax			;is it zero?
	jz	gotdate
	push	ax			;save date
	and	ax,mask yr		;get year part
	mov	cl,yr			;bits to shift
	call	cnvrt
	mov	di,offset vyear
	or	al,'8'                  ;adjust for base year
	stosw

	pop	bx			;get the date back
	push	bx			;save it
	and	bx,mask mo		;get month part
	mov	cl,mo			;bits to shift
	shr	bx,cl
	add	bx,bx			; form month table index
	add	bx,bx
	lea	si,word ptr months-4[bx]
	mov	cx,3
	mov	di,offset vmonth
	rep	movsb

	pop	ax			;get the date back
	and	ax,mask dy		;get day part
	mov	cl,dy			;bits to shift
	call	cnvrt
	mov	di,offset vdate
	stosw
gotdate:ret
getdate endp

	page
;
; ripped from sdir.asm. how does this work?

ddptr	dw	0

format	proc	near	;formats a 32 bit integer in dx:ax
	push	bp	; to ds:si
	push	bx
	push	di
	push	si
	mov	ddptr,si	;addr of target field
	mov	di,dx		;routine uses di:si
	mov	si,ax
	call	printdd
	pop	si
	pop	di
	pop	bx
	pop	bp
	ret

printdd:
	xor	ax,ax		;zero out the
	mov	bx,ax		; working
	mov	bp,ax		; registers.
	mov	cx,32		;# bits of precision
j1:	shl	si,1
	rcl	di,1
	xchg	bp,ax
	call	j6
	xchg	bp,ax
	xchg	bx,ax
	call	j6
	xchg	bx,ax
	adc	al,0
	loop	j1
	mov	cx,1710h
	mov	ax,bx
	call	j2
	mov	ax,bp
j2:	push	ax
	mov	dl,ah
	call	j3
	pop	dx
j3:	mov	dh,dl
	shr	dl,1		;move high
	shr	dl,1		; nibble to
	shr	dl,1		; the low
	shr	dl,1		; position.
	call	j4
	mov	dl,dh
j4:	and	dl,0fh		;mask low nibble
	jz	j5		;if not zero
	mov	cl,0
j5:	dec	ch
	and	cl,ch
	or	dl,'0'          ;fold in ascii zero
	sub	dl,cl
	mov	bx,ddptr
	mov	[bx],dl 	;ptr to next target field
	inc	ddptr
	ret

j6:	adc	al,al
	daa
	xchg	al,ah
	adc	al,al
	daa
	xchg	al,ah
	ret
format	endp

	page
cvh	proc	near		; convert 16-bit binary word in ax
	push	di		; to hex ASCII string at ds:di
	push	bx		; save registers
	push	cx
	push	dx

	mov	dx,ax		; save 16-bits

	mov	bl,dh		; third nibble
	mov	cl,4
	shr	bl,cl
	mov	al,hexchar[bx]
	stosb

	mov	bl,dh		; last nibble
	and	bl,0fh
	mov	al,hexchar[bx]
	stosb

	mov	bl,dl		; first nibble
	mov	cl,4
	sub	bh,bh
	shr	bl,cl		; isolate
	mov	al,hexchar[bx]
	stosb

	mov	bl,dl		; second nibble
	and	bl,0fh		; isolate
	mov	al,hexchar[bx]
	stosb
	pop	dx		; restore registers
	pop	cx
	pop	bx
	pop	di
	ret			; return

hexchar db	'0123456789ABCDEF'
cvh	endp

	subttl	' - i/o subroutines'
	page

getc	proc	near			; return next byte in al
	push	si			;  or cf=1 for eof
getc1:
	dec	inlen			; any left in buffer
	jl	getc2			; yes, pick it up
	mov	si,inptr		; offset to next byte
	lodsb
	mov	inptr,si
	pop	si
	ret
getc2:
	call	getblk			; read next block
	jnc	getc1
	pop	si			; return cf=1 at eof
	ret
getc	endp


getblk	proc	near			; read next block
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
getblkx:
	pop	dx
	pop	cx
	pop	bx
	ret

getblkr:
	printl	'I/O error reading '
	print	arcname
	jmp	error			; gotta quit
getblk	endp

	subttl	'--- load next archive header'
	page

gethdr	proc	near
	mov	cx,512			; gotta look for the damn thing
gethdr2:
	call	getc			; get next file byte
	jc	gethdrr1		; premature eof
	cmp	al,arcmark		; start of header?
	je	gethdr3 		; yup, let's start cookin
	loop	gethdr2
gethdrr1:
	printl	'Invalid archive format!'
	jmp	error

gethdr3:
	call	getc			; get version code
	jc	gethdrr1
	mov	archdr.mbrcode,al
	cmp	al,arcver		; reasonable code?
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

arcv	endp

dta	equ	$		; data transfer area

archdr	equ	dta + 48	; i/o area for a header

inbuf	equ	archdr + 64	; read i/o buffer
cseg	ends
	end	arcv
