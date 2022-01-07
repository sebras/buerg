	page	74,132
	title	ZIPV - Display directory of ZIP files

; name: 	ZIPV, version 1, 7 March 1989
; copyright:	1989, for personal use only; may not be sold.
; author:	Vernon D. Buerg
;
; syntax:
;		ZIPV [filespec[.ZIP] [/p] [/b] [/c]
; where:
;    /p  pauses the display after a screen full
;    /b  suppresses display of d:\path information for bbs use
;    /c  displays ZIPfile and file comments and extra fields
;
; output:
;    - errorlevel returned:
;	0 - normal completion
;	1 - wrong DOS version
;	2 - no files found
;	3 - some invalid ZIP file(s) encountered
;
; notes:
;    - supports DOS 3 file sharing
;    - requires about 56k of memory, figure 64k for a .COM program
;    - assembled using SLR Systems OPTASM; you figure the JMPs for MASM
;    - handles self-extracting ZIP files (.EXE type)

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

save	macro	reglist 		; save registers
	irp	reg, <reglist>
	push	reg
	endm
	endm

restore macro	reglist 		; restore registers
	irp	reg, <reglist>
	pop	reg
	endm
	endm
	.list

central_dir	struc			; from APPNOTES.TXT
cd_sig		db	02h,01h,4bh,50h ; signature
cdver_made	db	0,0		; version made by
cdver_ext	db	0,0		; version to extract
cd_flag 	db	0,0		; general purpose bit flag
cd_method	dw	0		; compression method
cd_mod_time	dw	0		; last mod time
cd_mod_date	dw	0		; last mod date
cd_crc		dw	0,0		; crc-32
cd_comp_size	dw	0,0		; compressed size
cd_true_size	dw	0,0		; uncompressed size
cd_flnm_len	dw	0		; filename length
cd_extra_len	dw	0		; extra field length
cd_comment_len	dw	0		; file comment length
cd_disk_start	dw	0		; disk number start
cd_intfile_attr dw	0		; internal file attributes
cd_extfile_attr dw	0,0		; external file attributes
cd_local_offset dw	0,0		; file offset of local header
					; variable length fields follow (boo-hiss)
central_dir	ends

cd_filename	equ	size central_dir; filename (variable size)
cd_extra	equ	size central_dir; extra field (variable size)
cd_comment	equ	size central_dir; file comment (variable size)

central_end	struc			; length 22+n
ce_sig		db	06h,05h,4bh,50h ; signature
ce_disk_number	dw	0		; number of this disk
ce_disk_start	dw	0		; disk number with central dir start
ce_disk_entries dw	0		; entries in central dir on this disk
ce_entries	dw	0		; total entries in central dir
ce_size 	dw	0,0		; size of central dir
ce_offset	dw	0,0		; offset to central dir on this disk
ce_comment_len	dw	0		; length of zipfile comment
					; variable length fields follow (nerts)
central_end	ends

ce_comment	equ	size central_end; zipfile comment (variable size)

dtantry struc				; DOS Data Transfer Area
dtarsvd db	21 dup (0)		;  reserved
dtaattr db	0			;  attribute
dtatime dw	0			;  update time
dtadate dw	0			;  update date
dtasize dw	0,0			;  size bytes (lo,hi)
dtaname db	12 dup (' ')            ;  name and ext
	db	0,13,10,255		;  stopper and print
dtantry ends

	subttl	ZIPV - Mainline routines
	page

cseg	segment public para 'CODE'
	assume	cs:cseg, ds:cseg, ss:cseg, es:cseg
	org	100h

zipv	proc	far
	jmp	start			; skip around data

	subttl	--- constants, equates and data areas
	page

bel	equ	7			; honker
bs	equ	8			; backspace
tab	equ	9			; tabski
lf	equ	10			; Line Feed
cr	equ	13			; la Carriage Return
eof	equ	26			; end of file character
stopper equ	255			; ends print strings

	db	bs,bs,bs,'   '          ; overlay entry jmp for type

usage	db	cr,lf,	 'ZIPV Version 1.07 Copyright (c) 1989 Vernon D. Buerg'
	db	cr,lf,	 'For personal use only. May not be sold.'
	db	cr,lf,lf,'  Usage:  zipv [d:][\path\]filespec[.ZIP]  [/p] [/b] [/c]'
	db	cr,lf
	db	cr,lf,	 '  Where:  /P pauses after each screenful'
	db	cr,lf,	 '          /B suppresses display of d:\path'
	db	cr,lf,	 '          /C displays comments'
	db	cr,lf,stopper,eof

errlvl	db	0			; dos error level returned
opencod db	0			; open code for share
flags	db	255			; find-first return code

options db	0			; command options
b_parm	 equ	1			; /b -bbs display option
p_parm	 equ	2			; /p -pause at screen full
c_parm	 equ	4			; /c - display comments

stkptr	dw	0			; stack pointer upon entry
ce_ptr	dw	0			; offset to central_end dir record
ce_count dw	0			; count of entries in central dir

fileptr dw	filenm			; spot after d:\path
filehdl dw	0			; file handle

ziptitl db	cr,lf,'Archive:  ',stopper

zipname db	13 dup (0),0,stopper	; ZIP file name for heading

;	display lines for verbose

vhdr	db	cr,lf
	db	cr,lf,'Name          Length    Method     SF   Size now  Mod Date    Time    CRC-32 '
dashes	db	cr,lf,'============  ========  ========  ====  ========  =========  ======  ========'
	db	stopper

vline	db	cr,lf
vname	db	14 dup (' ')
vsize	db	'       0  '            ; acutal file size
vstyle	db	'          '            ; compression method
vfactor db	' xx%  '                ; compression factor
vlength db	10 dup (' ')            ; compressed length
vdate	db	'dd '                   ; creation date
 vmonth db	'mmm '
 vyear	db	'yy  '
 vtime	db	'hh:mm   '              ; creation time
 vcrc	db	'xxxxxxxx'              ; crc in hex
	db	stopper
len_vline equ	$-vline 		; length of print line

totsf	dw	0,0			; average stowage factor
totlen	dw	0,0			; total of file lengths
totsize dw	0,0			; total of file sizes
totmbrs dw	0			; total number of files

;	final totals line

vthdr	db	cr,lf,'*total'
 vtmbrs db	'        '
 vtsize db	8 dup (' '),'  '
	db	10 dup (' ')
 vtsf	db	'   %  '
 vtlen	db	8 dup (' ')
	db	cr,lf
	db	stopper
 sign	db	' '

vtotal	db	'*total'
ctitle	db	cr,lf,'Comment:  ',stopper
cextra	db	cr,lf,'Extra:    ',stopper

styles	db	'Stored  '              ; compression method names
	db	'Shrunk  '
	db	'Reduced1'
	db	'Reduced2'
	db	'Reduced3'
	db	'Reduced4'

hundred dw	100			; for computing percentages
months	db	'Jan Feb Mar Apr May Jun Jul Aug Sep Oct Nov Dec '
	subttl	--- Mainline
	page

start:
	mov	sp,offset cs:stk_end	; local stack
	mov	stkptr,sp		; save for dos return

	mov	ah,30h			; get dos version
	int	21h			;
	cmp	al,2			; version 2 or later?
	jb	badver			; no, gotta quit
	cmp	al,3			; enough for share?
	jb	dos_okay		; no, open as-is
	mov	opencod,40h		; yes, add read-only

dos_okay:
	mov	bx,paras		; size of program
	mov	ah,4ah			; shrink allocated memory
	int	21h			; setblock function

	mov	di,offset filenm	; clear operands
	mov	cx,offset stk-filenm	;  and work areas
	mov	al,0			;
	rep	stosb			;

	subttl	--- gather command line parameters
	page

getparm:
	mov	si,82h			; Command tail
	sub	cx,cx			;
	or	cl,byte ptr -2[si]	; test parm length
	jz	getparms		; none, return as-is

sw1:	lodsb				; scan for switch
	cmp	al,'/'                  ;
	loopne	sw1			;
	or	cx,cx			; found one?
	jz	getparms		; no, done
	mov	byte ptr -1[si],cr	; yes, stop command line there
	jmp	sw2a			; and check next character

sw2:	lodsb				; Next character
	cmp	al,'/'                  ; Another switch?
	loopne	sw2			;
	jcxz	getparms		;

sw2a:	lodsb				; yes, get letter following
	and	al,0dfh 		; make upper case
	dec	cx			;
	jle	sw3			; missing switch

sw3:	cmp	al,'P'                  ; Pause?
	jne	sw4			;
	or	options,p_parm		;

sw4:	cmp	al,'B'                  ; BBS use
	jne	sw5			;
	or	options,b_parm		;

sw5:	cmp	al,'C'                  ; display Comments?
	jne	sw2			;
	or	options,c_parm		;
	jmp	sw2			; Try for another option

	subttl	--- Gather command operands
	page

;	copy first command line operand as ZIP selection filespec

getparms:
	mov	si,80h			; offset to command line
	sub	cx,cx			; its length
	or	cl,byte ptr [si]	; any operand?
	jnz	parm0			; no,
	print	usage			;  display usage
	jmp	zipv_exit		;   and quit

parm0:	inc	si			; point to operands
parm2:	lodsb				; strip leading blanks
	cmp	al,' '                  ;
	loope	parm2			;

	mov	di,offset filenm	; first operand target
	stosb				;
parm3:	lodsb				; copy filename
	cmp	al,cr			; end of name?
	je	parm4			;
	cmp	al,' '                  ; don't know why this is here
	je	parm4			;
	stosb				;
	loop	parm3			;
parm4:
	mov	si,offset filenm +75	; end of filename stuff
	mov	cx,76			;
	std				;
parm5:
	lodsb				;
	cmp	al,'/'                  ; funny path delimiter?
	je	parm6			;
	cmp	al,'\'                  ; normal path delimiter?
	je	parm6			;
	cmp	al,':'                  ; bumped into drive?
	je	parm6			;
	loop	parm5			;
	dec	si			;
parm6:
	cld				;
	add	si,2			; point to where filename goes
	mov	fileptr,si		; and save for later

;	add default ZIP extension if necessary

	mov	si,fileptr		; start of filespec
	mov	cx,13			;
parm10:
	lodsb				;
	cmp	al,0			; end of name?
	je	parm11			;
	cmp	al,'.'                  ; got extension?
	je	parm12			;
	loop	parm10			;
parm11:
	mov	di,si			; ptr to end of name
	dec	di			;
	mov	ax,'Z.'                 ; default extension
	stosw				;
	mov	ax,'PI'                 ;
	stosw				;
parm12:

	subttl	--- Find matching files
	page
;
;	set up next matching file name

process:
	mov	dx,offset dta		; set local dta for murkers
	mov	ah,1ah			;
	int	21h			;

	mov	dx,offset filenm	; find first matching file
	sub	cx,cx			; normal attribute
	mov	ah,4eh			;
	int	21h			;
	mov	flags,al		; indicate find-first status
	or	ax,ax			; any return code?
	jz	gotfirst		; nope, continue
	jmp	nofiles 		; yup, abort

;	set up next matching file name

gotfirst:
	mov	si,offset dta+30	; point to filename found
	mov	di,fileptr		; and overlay old name
	mov	cx,13			;
gotfirst1:
	lodsb				; next char
	stosb				;
	cmp	al,0			; end of name?
	loopne	gotfirst1		;
	mov	al,0FFh 		; append stoppers
	stosb				;

	mov	si,offset dta+30	; copy filename for heading
	mov	di,offset zipname	;
	mov	cx,13			; asciiz filename
gotfirst2:
	lodsb				; next char
	stosb				;
	cmp	al,0			; end of name?
	loopne	gotfirst2		;
	mov	al,0FFh 		; append stoppers
	stosb				;

process_loop:				; open the file
	mov	dx,offset filenm	; point to d:\path\filename
	mov	ah,3dh			; open function
	mov	al,opencod		; share parameters
	int	21h			; issue open
	jc	open_err1		; oops
	mov	filehdl,ax		; save file handle

	call	posfile 		; position and read central directory

	call	close			; release the ZIP file

	call	dispdir 		; display directory contents

getnext:
	mov	ah,4fh			; get next file name
	int	21h			;
	jc	alldone 		;
	or	ax,ax			;
	jz	gotfirst		;
alldone:
	jmp	zipv_exit		; all done

	subttl	--- Display directory entries
	page

ecount	dw	0			; entries on current disk

dispdir proc	near
	sub	ax,ax			; reset totals counters
	mov	totmbrs,ax		;
	mov	totsize,ax		;
	mov	totsize+2,ax		;
	mov	totlen,ax		;
	mov	totlen+2,ax		;
	mov	totsf,ax		;

;  display titles

	mov	ax,ce_count		; number of entries
	mov	ecount,ax		; save as line counter
	print	ziptitl 		;
	test	options,b_parm		; want short filename?
	jz	dispdir1		; no
	print	zipname 		; show short name
	jmp	dispdir2		;
dispdir1:
	print	filenm			; show full name

;  display comments

dispdir2:
	test	options,c_parm		; want them?
	jz	disp3			; no
	mov	si,ce_ptr		; offset to ce dir
	mov	cx,ce_comment_len[si]	;
	jcxz	disp3			; if none
	print	ctitle			; yes, add heading item
	lea	dx,ce_comment[si]	; point to comment
	mov	ah,40h			; write to file
	mov	bx,1			; using std out
	int	21h			;

disp3:
	print	vhdr			; show headings
	mov	bx,offset cdir		; first header in central directory
dispdir_loop:
	mov	di,offset vname 	; clear print line
	mov	cx,14			;
	mov	al, ' '                 ;
	rep	stosb			;

	call	stowage 		; compute stowage factor

disp_style:
	mov	si,cd_method[bx]	; compression method code
	mov	cl,3			;
	shl	si,cl			; time style length
	add	si,offset styles	; list of method names
	mov	di,offset vstyle	;
	mov	cx,8			;
	rep	movsb			;

disp_crc:
	mov	di,offset vcrc		; format crc-32 value
	mov	ax,cd_crc+2[bx] 	; first word
	call	cvh			;
	mov	ax,cd_crc[bx]		; second word
	call	cvh			;

	mov	ax,cd_mod_time[bx]	; last modified time
	call	gettime 		; format it

	mov	ax,cd_mod_date[bx]	; last modified date
	call	getdate 		; format it

	mov	ax,word ptr cd_true_size[bx]   ; actual file size
	mov	dx,word ptr cd_true_size+2[bx] ; high word
	add	totsize,ax		; accumulate total size
	adc	totsize[2],dx		;
	mov	si,offset vsize 	;
	call	format			;

	mov	ax,word ptr cd_comp_size[bx]   ; compressed file size
	mov	dx,word ptr cd_comp_size+2[bx] ; high word
	add	totlen,ax		; accumulate total length
	adc	totlen[2],dx		;
	mov	si,offset vlength	;
	call	format			;

	mov	cx,cd_flnm_len[bx]	; file name length
	lea	si,cd_filename[bx]	;  and offset
	mov	di,offset vname 	;   to print line
	rep	movsb			;

	inc	totmbrs 		; total files count
	print	vline			; display an entry

;  process extra field

dispdir_extra:
	test	options,c_parm		; want comments?
	jz	dispdir_next		;  no
	mov	cx,cd_extra_len[bx]	; extra field
	jcxz	dispdir_comment 	; if none
	mov	si,cx			; compute offset
	add	si,bx			;  to extra field
	add	si,cd_flnm_len[bx]	;
	print	cextra			;
	lea	dx,cd_comment[si]	; point to comment
	mov	ah,40h			; write to file
	mov	bx,1			; using std out
	int	21h			;

;  display copmment field

dispdir_comment:
	mov	cx,cd_comment_len[bx]	; comment field
	jcxz	dispdir_next		; if none
	mov	si,cx			; compute offset
	add	si,bx			;  to comments
	add	si,cd_flnm_len[bx]	;
	add	si,cd_extra_len[bx]	;
	print	ctitle			;
	lea	dx,cd_comment[si]	; point to comment
	mov	ah,40h			; write to file
	mov	bx,1			; using std out
	int	21h			;

; set-up for next entry

dispdir_next:
	mov	cx,size central_dir	; minimum cd entry size
	add	cx,cd_flnm_len[bx]	;  plus file name length
	add	cx,cd_extra_len[bx]	;   plus extra field length
	add	cx,cd_comment_len[bx]	;    plus comment field length
	add	bx,cx			;     to point to next entry
	dec	ecount			;
	jnz	dispdir_loop		; continue

	page
;
;	display totals for current file

dir_totals:
	print	dashes			; separate totals line

	mov	ax,totsize		; total file sizes
	mov	dx,totsize[2]		; high word
	mov	si,offset vtsize	;
	call	format			;

	mov	ax,totlen		; compressed file size
	mov	dx,totlen[2]		; high word
	mov	si,offset vtlen 	;
	call	format			;

	mov	ax,totmbrs		; count of members
	sub	dx,dx			;
	mov	si,offset vtmbrs-2	;
	call	format			;

	mov	cx,totlen		; compressed file size
	mov	dx,totlen[2]		; high word
	mov	bx,totsize		; actual file size
	mov	ax,totsize[2]		; high word
	call	stow_total		;

	mov	si,offset vtotal	; say *total
	mov	di,offset vthdr+2	;
	mov	cx,6			;
	rep	movsb			;

	print	vthdr			; display totals
	ret				;
dispdir endp

	subttl	--- Position file
	page
;
;	Position to end of ZIP file less central directory size

margin	dw	size central_end	; how far before ce to read

posfile proc	near			;
	mov	margin,size central_end ; how far before ce dir to point

posfile_point:
	mov	bx,filehdl		; get file handle
	mov	cx,dta.dtasize[2]	; high word of size
	mov	dx,dta.dtasize		; low word of size
	sub	dx,margin		; less size of central
	sbb	cx,0			;   directory end record
	jl	posfile_start		; if small file
	mov	ax,4200h		; move to central end directory
	int	21h			; lseek function
	jmp	read_ce 		;

posfile_start:
	mov	ax,dta.dtasize		; use file size
	mov	margin,ax		;  as amount to position
	jmp	posfile_point		;

;  read central-directory-end record

read_ce:
	mov	cx,margin		; how much to read (pos before eof)
	mov	dx,offset cde		; central end dir area
	mov	ah,3fh			;
	int	21h			;
	jc	open_err2		; failed
	cmp	ax,cx			; read it all?
	jne	open_err3		; nope

;  search end of file for cde signature

	mov	bx,offset cde+1 	; point to centerl end dir record
	mov	cx,margin		; look back this far
	sub	cx,size central_end-1	;
	add	bx,cx			;
search_loop:
	mov	si,bx			; next cde byte
	dec	bx			;
	cmp	word ptr [si],4b50h	; check signature
	jne	search_loop1		;
	cmp	word ptr 2[si],0605h	;
	je	read_cd 		; found it
search_loop1:
	loop	search_loop		; continue search
	add	margin,256		; not yet,
	jmp	posfile_point		;  back up some more

; re-position to central-directory

read_cd:
	mov	ce_ptr,si		; save pointer to c_e dir start
	mov	ax,ce_disk_entries[si]	; number of entries
	mov	ce_count,ax		;  and save for later
	mov	dx,ce_offset[si]	; offset to central directory
	mov	cx,ce_offset+2[si]	;
	mov	bx,filehdl		; get file handle
	mov	ax,4200h		; move file pointer
	int	21h			; returns dx:ax position

; read the central directory until end-of-file

	mov	bx,dta.dtasize[2]	; get file size in bx:cx
	mov	cx,dta.dtasize		;  to compute
	sub	cx,ax			;   size of
	sbb	bx,dx			;    central dir to eof
	mov	bx,filehdl		; get file handle
	mov	ah,3fh			; for reading
	mov	dx,offset cdir		; central dir end area
	int	21h			;
	jc	open_err4		; failed
	cmp	ax,cx			; read it all?
	jne	open_err5		; nope

	ret				;
posfile endp

	page
;
;	compute stowage; reduce the size/length to word values

stowage proc	near			; compute stowage factor
	push	bx			; save dir pointer

	mov	cx,word ptr cd_comp_size[bx]	 ; compressed file size
	mov	dx,word ptr cd_comp_size+2[bx]	 ; high word

	mov	ax,word ptr cd_true_size+2[bx]	 ; high word
	mov	bx,word ptr cd_true_size[bx]	 ; actual file size
	mov	si,offset vfactor-5	; target area
	jmp	stow51			;

stow_total:
	push	bx			; entry for totals calculation
	mov	si,offset vtsf-5	; target area

stow51: or	ax,ax			; big number?
	jz	stow52			; nope, can use it
	shr	ax,1			; yup, divide by two
	rcr	bx,1			;
	shr	dx,1			;
	rcr	cx,1			;
	jmp	stow51			;

stow52:
	mov	ax,bx			; low word of actual size
	mov	sign,' '                ;
	cmp	ax,cx			; zip member is larger?
	jb	stow520 		;
	sub	ax,cx			; amount saved
	jmp	stow56			;
stow520:
	sub	ax,cx			;
	neg	ax			;
	mov	sign,'-'                ;
stow56:
	mul	hundred 		; to percentage
	add	ax,50			;
	adc	dx,0			; round up percent
	or	bx,bx			; empty file?
	jnz	stow53			;
	mov	ax,100			;
	jmp	stow54			;

stow53: div	bx			;
stow54: sub	dx,dx			;
	cmp	ax,100			; archive fouled?
	jbe	stow55			;
	sub	ax,ax			;
stow55:
	call	format			;
	mov	al,sign 		; get + or -
	mov	byte ptr [si],al	;
	pop	bx			; restore dir pointer
	ret				; return to caller
stowage endp				;

	subttl	--- subroutines
	page
;
;	close the file

close	proc	near			;
	mov	bx,filehdl		; file handle
	or	bx,bx			; is it open
	jz	close_done		;
	mov	ah,3eh			; close function
	int	21h			;
	sub	bx,bx			;
close_done:
	mov	filehdl,bx		; indicate closed
	ret				;
close	endp				;

	page
;
;	print string like int 21h function 9

pause	db	cr,lf,'... more?$'
backup	db	cr,9 dup (8),'$'
linecnt db	0		; line counter for pause
pagecnt db	23		; lines per screen

prints	proc	near			; dx has offset to string

	test	options,p_parm		; want pausing?
	jz	ps1			; no, skip next

	save	<bx,cx,dx,si>		; save work regs
	mov	al,linecnt		;
	cmp	al,pagecnt		; end of screen?
	jbe	ps0			; not yet
	mov	dx,offset pause 	; yup, say so
	mov	ah,9			;
	int	21h			;
	mov	ah,0			; get a key
	int	16h			;
	mov	dx,offset backup	; over write pause prompt
	mov	ah,9			;
	int	21h			;
	mov	linecnt,0		; reset line counter
ps0:	restore <si,dx,cx,bx>		; restore work regs

ps1:	save	<si,bx,cx>		; save work regs
	mov	si,dx			;
	sub	cx,cx			;
ps2:	lodsb				;
	cmp	al,stopper		; ending hex ff?
	je	ps8			;
	inc	cx			; incr text length
	cmp	al,lf			; another line?
	jne	ps2			;
	inc	linecnt 		;
	jmp	ps2			;

ps8:	mov	ah,40h			; write to file
	mov	bx,1			; using std out
	int	21h			;

ps9:	restore <cx,bx,si>		; recover registers
	ret				;
prints	endp

	page
;
;	format the time

time	record	hour:5,min:6,sec:5	; packed time

gettime proc	near			; format the date
	mov	di,offset vtime 	;
	push	ax			; save date
	and	ax,mask hour		; get hour part
	mov	cl,hour 		; bits to shift
	shr	ax,cl			;
	call	cnvrt1			;
	stosw				;
	mov	al,':'                  ;
	stosb				;

gt3:	pop	ax			; get the time back
	and	ax,mask min		; get min part
	mov	cl,min			; bits to shift
	call	cnvrt			;
	stosw				;
gottime:ret				;
gettime endp

cnvrt	proc	near			; convert to ascii
	shr	ax,cl			;
cnvrt1: aam				; make al into bcd
	or	ax,'00'                 ; and to ascii
	xchg	al,ah			;
cnvrtd: ret				;
cnvrt	endp

	page
;
;	format the date

date	record	yr:7,mo:4,dy:5		; packed date

getdate proc	near			; format the date
	push	bx			; save cd pointer
	or	ax,ax			; is it zero?
	jz	gotdate 		;
	push	ax			; save date
	and	ax,mask yr		; get year part
	mov	cl,yr			; bits to shift
	call	cnvrt			;
	mov	di,offset vyear 	;
	or	al,'8'                  ; adjust for base year
	stosw				;

	pop	bx			; get the date back
	push	bx			; save it
	and	bx,mask mo		; get month part
	mov	cl,mo			; bits to shift
	shr	bx,cl			;
	add	bx,bx			; form month table index
	add	bx,bx			;
	lea	si,word ptr months-4[bx];
	mov	cx,3			;
	mov	di,offset vmonth	;
	rep	movsb			;

	pop	ax			; get the date back
	and	ax,mask dy		; get day part
	mov	cl,dy			; bits to shift
	call	cnvrt			;
	mov	di,offset vdate 	;
	stosw				;
gotdate:				;
	pop	bx			; restore cd pointer
	ret				; back to caller
getdate endp

	page
;
;	 format 4-byte binary into ASCII for display

ddptr	dw	0			;

format	proc	near			; formats a 32 bit integer in dx:ax
	save	<bp,bx,di,si>		;  to ds:si
	mov	ddptr,si		; addr of target field
	mov	di,dx			; routine uses di:si
	mov	si,ax			;
	call	printdd 		;
	restore <si,di,bx,bp>		;
	ret				;

printdd:
	xor	ax,ax			; zero out the
	mov	bx,ax			; working
	mov	bp,ax			; registers.
	mov	cx,32			; # bits of precision
j1:	shl	si,1			;
	rcl	di,1			;
	xchg	bp,ax			;
	call	j6			;
	xchg	bp,ax			;
	xchg	bx,ax			;
	call	j6			;
	xchg	bx,ax			;
	adc	al,0			;
	loop	j1			;
	mov	cx,1710h		;
	mov	ax,bx			;
	call	j2			;
	mov	ax,bp			;
j2:	push	ax			;
	mov	dl,ah			;
	call	j3			;
	pop	dx			;
j3:	mov	dh,dl			;
	shr	dl,1			; move high
	shr	dl,1			;  nibble to
	shr	dl,1			;   the low
	shr	dl,1			;    position
	call	j4			;
	mov	dl,dh			;
j4:	and	dl,0fh			; mask low nibble
	jz	j5			; if not zero
	mov	cl,0			;
j5:	dec	ch			;
	and	cl,ch			;
	or	dl,'0'                  ; fold in ascii zero
	sub	dl,cl			;
	mov	bx,ddptr		;
	mov	[bx],dl 		; ptr to next target field
	inc	ddptr			;
	ret				;

j6:	adc	al,al			;
	daa				;
	xchg	al,ah			;
	adc	al,al			;
	daa				;
	xchg	al,ah			;
	ret				;
format	endp

	page
;
;	convert binary word to two hex characters

hexchar db	'0123456789ABCDEF'      ; for conversion

cvh	proc	near			; convert 16-bit binary word in ax
	save	<bx,cx,dx>		; to hex ASCII string at ds:di
	sub	bx,bx			;
	mov	dx,ax			; save 16-bits

	mov	bl,dh			; third nibble
	mov	cl,4			;
	shr	bl,cl			;
	mov	al,hexchar[bx]		;
	stosb				;

	mov	bl,dh			; last nibble
	and	bl,0fh			;
	mov	al,hexchar[bx]		;
	stosb				;

	mov	bl,dl			; first nibble
	mov	cl,4			;
	sub	bh,bh			;
	shr	bl,cl			; isolate
	mov	al,hexchar[bx]		;
	stosb				;

	mov	bl,dl			; second nibble
	and	bl,0fh			; isolate
	mov	al,hexchar[bx]		;
	stosb				;
	restore <dx,cx,bx>		; restore registers
	ret				; return

cvh	endp

	subttl	--- Errors and exits
	page
;
;	error messages and exits

errmsg	db	cr,lf,"ERROR! ",bel,stopper
errmsg1 db	"Unable to open ",stopper
errmsg2 db	"Reading central end directory: ",stopper
errmsg3 db	"Central end directory incomplete: ",stopper
errmsg4 db	"Reading central directory: ",stopper
errmsg5 db	"Central directory incomplete: ",stopper

open_err1:
	mov	dx,offset errmsg1	; display message
	jmp	zipv_error		;   and quit

open_err2:
	mov	dx,offset errmsg2	; display message
	jmp	zipv_error		;   and quit

open_err3:
	mov	dx,offset errmsg3	; display message
	jmp	zipv_error		;   and quit

open_err4:
	mov	dx,offset errmsg4	; display message
	jmp	zipv_error		;   and quit

open_err5:
	mov	dx,offset errmsg5	; display message
	jmp	zipv_error		;   and quit

nofiles:
	printl	'No file(s) found '     ; display message
	mov	errlvl,2		; set return code
	jmp	zipv_exit		;   and quit

badver:
	printl	"DOS 2.0 or later is required."
	mov	errlvl,1		; set return code
	jmp	zipv_exit		;   and quit

zipv_error:
	mov	sp,cs:stkptr		; insure stack pointer
	mov	errlvl,3		; return error code
	push	dx			;
	print	errmsg			; make some noise
	pop	dx			;
	call	prints			; display error message
	print	filenm			;  with file name
	cmp	flags,255		; processed any files?
	jne	getnext 		; yes, try some more

zipv_exit:
	mov	sp,cs:stkptr		; insure stack pointer
	mov	al,errlvl		; get error level
	mov	ah,4ch			; exit
	int	21h			;

	subttl	--- data areas
	page

filenm	equ	$			; command line filespec supplied

dta	equ	filenm+80		; dos data transfer area

cde	equ	dta+48			; central directory end record
					; with room for 8k of comments
cdir	equ	cde+(size central_end)+(8*1024) ; central directory

stk	equ	cdir+ (52*1024) 	; and what's left as room for comments

stk_end equ	stk+256 		; local stack

paras	equ	(stk_end+256-cseg)/16	; paragraphs in module

zipv	endp
	end	zipv
