	page	74,132
	title	ljbook - print files 2-up 2-sided on hp ljp

; syntax:	ljbook	filename  [outfile]  [/f] [/p] [/d]

; v0.90 7/02/87 - first flyer
; v0.97 7/05/87 - add option switches
; v0.98 7/19/87 - correction for multiples of 4 pages
; v0.99 8/10/87 - correction for files over 256 pages
; v1.0 10/05/87 - first public release

;	data area structures

psp		struc			; program segment prefix
psp_int_20	db	0cdh,020h	; int 20 instruction
psp_top 	dw	?		; top of memory in paragraph form
psp_resvl	dw	?		; reserved
psp_bytes	dw	?,?		; bytes available in segment
		db	118 dup (?)	; unused
psp_parm_len	db	?		; characters in parameter list
psp_parms	db	127 dup (?)	; command parameters
psp		ends


cseg	segment public para 'code'
	assume cs:cseg, ds:cseg, es:cseg
	org	100h

ljbook	proc	far
	lea	sp,word ptr lstack	; set local stack
	call	chkver			; check dos version
	call	parms			; process command line
	call	alloc			; allocate buffers
	call	open			; access input file
	call	scan			; build page table
	call	headers 		; set up (optional) headings
	call	copy			; print file
	call	close			; release input file
	mov	byte ptr errlvl,0	; set good return code
	jmp	short exit		; and return to system

error1:
	mov	dx,offset usage 	; show syntax
error:
	mov	ax,cs			; insure local regs
	mov	ds,ax			;
	mov	es,ax			;
	lea	sp,word ptr lstack	; insure stck pt
	mov	byte ptr errlvl,1	; set bad return
	call	prints			; print error message
exit:
	mov	dx,offset null		; space last line
	call	prints
	mov	al,byte ptr errlvl	; get error level
	mov	ah,4ch			; set exit function
	int	21h			; return to dos

	page
;
;	equates, constants, and data areas

tab	equ	09h			; tabby
lf	equ	0ah			; line-feed
ff	equ	0ch			; form-feed
cr	equ	0dh			; carriage return
eof	equ	1ah			; end-of-file
esc	equ	1bh			; escape
blank	equ	20h			; space

prn		equ	4		; handle for standard printer
switch_char	equ	'/'             ; delimiter for command line switches
stopper 	equ	255		; ends text strings

version db	cr,lf,'LJBOOK (c) Copyright 1987 by Vernon D. Buerg'
	db	cr,lf,'For personal use only. May not be sold.',stopper
usage	db	cr,lf
	db	cr,lf,'Usage:'
	db	cr,lf,'       ljbook  filename  [outfile] [/f][/p][/d]'
	db	cr,lf
	db	cr,lf,'       /f  put filename in heading of each page'
	db	cr,lf,'       /p  put page number in heading'
	db	cr,lf,"       /d  put today's date/time in heading"
null	db	cr,lf,stopper,26

flags	db	0			; procesing options
 swf	equ	1			; /f = filename in heading
 swd	equ	2			; /d = put today's date/time in heading
 swp	equ	4			; /p = put page numbers in heading
 swm	equ	8			; /m = left margin (not implemented)
 swt	equ	16			; /t = title supplied (not implemented)

errlvl	db	0			; dos error level returned
lastchr db	0			; previously read char

max	dw	0			; maximum pages/table entries
min	dw	128			; minimum

atable	dw	offset table		; offset to next table entry
btable	dw	offset table		; offset for right side

pages	dw	1			; number of pages
sides	dw	0			; number of two-up pages
sheets	dw	0			; number of sheets

lpp	equ	66			; lines per page
lcnt	dw	0			; current lines on page
cpl	equ	80			; characters per line
linelen dw	0			; length of current line

filepos dw	0,0			; current file offset

ibuf	dw	offset table		; next input character
ilen	dw	0			; bytes in buffer
ihandle dw	0			; input handle
msgopni db	cr,lf,"Can't open input file - "
ifile	db	76 dup (0),255		; input file name

ohandle dw	prn			; output handle
msgopno db	cr,lf,"Can't open output file - "
ofile	db	76 dup (0),255		; output file name

	page
;
;	print command codes

init	equ	$			; initilization strings
	db	27,'&l1O'               ; landscape
	db	27,'(s0p'               ; fixed spacing                 ;099
	db	     '16.66h'           ; font pitch                    ;099
	db	     '8.5v'             ; point size                    ;099
	db	     '0d'               ; style                         ;099
	db	     '0b'               ; weight                        ;099
	db	     '0T'               ; typeface                      ;099
	db	27,'&l8d'               ; 8 lpi                         ;099
	db	     '1e'               ; top margin                    ;099
	db	     '67f'              ; text length, 8x8.5=68 lines   ;099
	db	     '5.5C'             ; vertical motion index = n/48  ;099
	db	esc,'&s0C'              ; enable line wrap
initlen equ	$-init

					; printer codes for left side
left_side	db	27,'9',cr       ;  clear margins
		db	27,'&a1r'       ;  line 1                       ;099
		db	    'a0l'       ;  left margin                  ;099
		db	    'a79M'      ;  right margin                 ;099
		db	cr		;  column 0
left_side_len	equ	$-left_side

					; printer codes for right side
right_side	db	27,'9',cr       ;  clear margins
		db	27,'&a1r'       ;  line 1                       ;099
		db	     '96l'      ;  left margin                  ;099
		db	     '175M'     ;  right margin                 ;099
		db	cr		;  column 94 (col 1)
right_side_len	equ	$-right_side

endpage db	ff			; printer codes to write at end of page
endlen	equ	$-endpage

	page
;
;	messages

info	db	cr,lf,lf
infonr	db	'       sheets to print.',stopper

side1	db	cr,lf,cr,lf,'Printing side 1 ...',stopper
side2	db	cr,lf,cr,lf,'Printing side 2 ...',stopper

prompt	db	cr,   'Side 1 printed.    ',cr,lf
	db	cr,lf,'Place printed paper back in paper tray, '
	db	cr,lf,'and press ENTER when ready ...',stopper

ended	db	cr,   'Side 2 printed.    ',cr,lf,stopper

msgmem	db	cr,lf,'Insufficient memory',255
msgver	db	cr,lf,'Incorrect DOS version',255
msgread db	cr,lf,'Error reading file',255

	page
;
;	page headings and titles

page_const	db	'Page '

lheader 	db	cr		; line 1 of left page
left_page	equ	$		; spot for 'Page'
left_pagenr	equ	$+4		; spot for page number
left_date	equ	lheader+18	; spot for date
left_time	equ	lheader+35	; spot for time
		db	80 dup (' ')    ; supplied title
left_fname	equ	$-1		; last char of leftmost filename
		db	cr,lf,lf	; blank line 2
lheader_len	equ	$-lheader	; length of titles

rheader 	db	cr		; line 1 of right page
right_fname	equ	$		; first char of rightmost filename
		db	80 dup (' ')    ; supplied title
right_page	equ	$-4-6		; spot for 'Page'
right_pagenr	equ	$-6		; spot for page number
right_time	equ	right_page-12	; spot for time
right_date	equ	right_time-17
		db	cr,lf,lf	; blank line 2
rheader_len	equ	$-rheader

months	db	' Jan'
	db	' Feb'
	db	' Mar'
	db	' Apr'
	db	' May'
	db	'June'
	db	'July'
	db	' Aug'
	db	' Sep'
	db	' Oct'
	db	' Nov'
	db	' Dec'

	page
;
;	check dos version

chkver	proc	near			;
	mov	dx,offset version	; display verion number
	call	prints			;
	mov	ah,30h			; get dos version
	int	21h			;
	cmp	al,2			; at least 2.0?
	jae	chkdver 		; yes, good
	mov	dx,offset msgver	; no, complain
	jmp	error			; and exit
chkdver:				;
	ret				;
chkver	endp				;

	page
;
;	parse command line

parms	proc	near
	mov	si,offset psp_parm_len	; point to command line
	sub	cx,cx			; to receive command line length
	lodsb
	or	cl,al			; any command line?
	jnz	switches		; yes, continue
	jmp	error1			; no, show usage

switches:
	mov	di,offset psp_parms	; offset to command parameters
switches0:
	mov	al,switch_char		; see if ANY switches
	repne	scasb
	jne	switched		; none, skip next
	jcxz	switched		; no more data
	mov	byte ptr -1[di],cr	; terminate command line at first /
	cmp	byte ptr -2[di],blank	;
	jne	switchesa		;
	mov	byte ptr -2[di],cr	;
switchesa:
	mov	si,di			; point to next char
	lodsb				; get char following switch char
	cmp	al,'a'                  ;  and make it upper case
	jb	switches1		;
	sub	al,blank		;
switches1:
	cmp	al,'F'                  ; show file name?
	jne	switches2		;
	or	flags, swf		;
switches2:
	cmp	al,'D'                  ; show date/time?
	jne	switches3		;
	or	flags, swd		;
switches3:
	cmp	al,'P'                  ; create page numbers?
	jne	switches4		;
	or	flags, swp		;
switches4:
	cmp	al,'M'                  ; add left margin?
	jne	switches5		;
	or	flags, swm		;
switches5:
	cmp	al,'T'                  ; add user title?
	jne	switches6		;
	or	flags, swt		;
switches6:
	jcxz	switched		; any more operands?
	jmp	switches0		; yup

	page
;
;	get file names for input and output (printer) files

switched:
	mov	si,offset psp_parms	; point to command line again
	sub	ch,ch			;
	mov	cl,byte ptr ds:[psp_parm_len] ; get length back
parm1:
	lodsb				; next char
	cmp	al,blank		; skip leading blanks
	je	parm1a			;
	cmp	al,tab			; skip tabs, too
	jne	parm2			;
parm1a: loop	parm1			;
	jmp	error1			; operand(s) missing

parm2:
	mov	di,offset ifile 	; target for input file name
	sub	cx,1			; account for last lodsb
	jge	parm3			; if more to process
	jmp	error1			; operand(s) missing
parm3:
	stosb				; previous char
	lodsb				; next char
	cmp	al,blank		; have operand separator?
	jbe	parm4			; yes, have first op
	loop	parm3			;
	stosb				;
	jmp	short parm8		; no second operand, use printer

parm4:
	mov	di,offset ofile 	; target for output file name
	jcxz	parm8			; if no second operand
parm5:
	lodsb				; skip intervening delimiters
	cmp	al,blank		;
	je	parm6			;
	cmp	al,cr			; end of parameters?
	je	parm8			; yes, just one operand
	cmp	al,tab			; skip tabs
	jne	parm7			;
parm6:	loop	parm5			; until no more command parameters
	jmp	short parm8		; none left

parm7:					; copy 2nd parm to output file name
	stosb				; its first/next char
	lodsb				; get next command line char
	cmp	al,cr			; end of it?
	jbe	parm8			; yes, have both operands now
	loop	parm7			;
parm8:	ret				;
parms	endp

	page
;
;	allocate memory and buffer(s)

alloc	proc   near
	mov	ax,word ptr ds:psp_bytes ;size of segment
	sub	ax,pgmsize		; less program size
	sub	dx,dx			;
	mov	cx,ltable		; size of each table entry
	div	cx			;  to get maximum entries
	mov	max,ax			;
	cmp	ax,min			; have enough?
	jb	alloc_err		; no,
	mov	cx,ax			; clear table
	mov	di,offset table 	;
	sub	ax,ax			; to zeros
alloc1:
	stosw
	stosw
	stosw
	loop	alloc1
	ret

alloc_err:
	mov	dx,offset msgmem	; insufficient memory
	jmp	error			; return and exit
alloc	endp

open	proc	near
	mov	dx,offset ifile 	; input file name
	mov	ax,3d00h		; for input
	int	21h			;
	jc	open_err1		;
	mov	word ptr ihandle,ax	; save input file handle

	cmp	byte ptr ofile,0	; was output file specified?
	je	open_exit		; no, use default printer
	mov	dx,offset ofile 	; output file name
	mov	ah,3ch			;  for create
	sub	cx,cx			; normal attribute
	int	21h			;
	jc	open_err2		; failed
	mov	ohandle,ax		; save new output handle
open_exit:
	ret				;

open_err1:
	mov	dx,offset msgopni	; input failed to open
	jmp	error			; return and exit

open_err2:
	mov	dx,offset msgopno	; output failed to open
	jmp	error			; return and exit
open	endp
	page
;
;	close all files

close	proc	near			; close input and output files
	mov	bx,word ptr ihandle	; get input handle
	or	bx,bx			; was it opened?
	jz	close2			; no, skip it
	mov	ah,3eh			; yes, close it
	int	21h			;
	mov	word ptr ihandle,0	; mark it closed
close2:
	mov	bx,word ptr ohandle	; get output handle
	cmp	bx,prn			; is it standard printer?
	jbe	closed			; yes, skip it
	mov	ah,3eh			; yes, close it
	int	21h			;
	mov	word ptr ohandle,0	; mark it closed
closed:
	ret
close	endp

	page
;
;	Print string like int 21h function 9

prints	proc	near			; dx has offset to string
	push	di			;  ending in char x'ff'
	push	bx			;
	push	cx			;
	mov	di,dx			; ptr to string text
	mov	cx,-1			; overall text length
	mov	al,255			; find ending hex ff
	repne	scasb			;
	not	cx			; length is bytes scanned
	mov	bx,1			; standard output device
	mov	ah,40h			; write to a file or handle
	int	21h			;
	pop	cx			; recover registers
	pop	bx			;
	pop	di			;
	ret				;
prints	endp

	page
;
;	scan input file for page markers

scan	proc	near
	mov	bx,atable		; pointer to table entry
	mov	al,0			; no history
scanread:
	mov	byte ptr lastchr,al	; save previous character
	call	getc			; get next char
	jc	scanned 		; all done
	inc	word ptr [bx]		; bump page size
	cmp	al,esc			; is it control char?
	jbe	scan0			; yes, don't bump line length
	inc	word ptr linelen	; bump line length
scan0:
	cmp	word ptr linelen,cpl	; reached line limit?
	ja	scan1			; yes, force new line
	cmp	al,lf			; new line?
	jne	scan2			; no,
scan1:
	inc	lcnt			; yes, bump line count
	mov	word ptr linelen,0	; reset line length
	cmp	lcnt,lpp		; reached end of page?
	jb	scanread		; no, continue
	jmp	short scan3		; yes, simulate end of page
scan2:
	cmp	al,ff			; found start of next page?
	jne	scanread		; no, keep reading
scan3:
	cmp	lcnt,0			; any lines yet?
	jne	scan4			; yes, have lines to print
	cmp	lastchr,lf		; no, but was previous an lf?
	je	scanread		; yes, already have page boundary
scan4:
	inc	pages			; bump page count
	mov	lcnt,0			; reset line counter
	add	bx,ltable		; point to next table entry
	mov	atable,bx		;
	mov	di,filepos		; get
	mov	dx,filepos+2		;  file
	mov	word ptr 2[bx],di	;   position
	mov	word ptr 4[bx],dx	;    for next page
	jmp	short scanread		; look for next page

scanned:
	ret				; done, return
scan	endp

	page
;
;	get next byte from read buffer


getc	proc	near
	sub	ilen,1			; decr byte count
	jl	getb			; no more, get next block
	mov	si,word ptr ibuf	; next input char
	lodsb				; get next char
	mov	word ptr ibuf,si	;
	mov	byte ptr lastchr,al	; save previous character
	cmp	al,eof			; logical end of file?
	je	getcx			; yes, set return
	add	filepos,1		; bump file position
	adc	filepos+2,0		;
	clc				; set good return
	ret				;

getb:					; read next block
	push	bx			; save index reg
	mov	bx,word ptr ihandle	; input handle
	mov	cx,bufsize		; size to read
	mov	dx,offset buffer	; data area
	mov	word ptr ibuf,dx	; reset next char ptr
	mov	ah,3fh			; read from file
	int	21h			;
	pop	bx			; recover index reg
	jc	getcx			; none, exit
	or	ax,ax			; end of file?
	jz	getcx			; yes, return cf
	mov	word ptr ilen,ax	; save count read
	jmp	short getc		; and get next char

getcx:					; return with eof indication
	stc				;  of cf=1
	ret
getc	endp

	page
;
;	copy file to printer (or output file)

copy	proc	near
	add	pages,3 		; round up pages		;099
	and	pages,0fffch		;  to multiple of four		;098
	mov	ax,pages		;
	shr	ax,1			; number of two-up pages
	mov	sides,ax		;
	shr	ax,1			; number of pages, two sides each
	mov	sheets,ax		;
	mov	si,offset infonr	; tell how many sheets
	call	format			;
	mov	dx,offset info		;
	call	prints			;

	push	sheets			; save for second pass

	mov	ax,pages		; number of pages
	dec	ax			; adjust for zero indexing
	mov	cx,ltable		; get table
	mul	cx			;   pointer
	add	ax,offset table 	;    for last entry
	mov	btable,ax		; and save it

	mov	ax,offset table 	; ptr for first left side entry
	mov	atable,ax		;  and save it

	mov	dx,offset init		; initialization codes
	mov	cx,initlen		; length of start-of-page codes
	mov	bx,ohandle		; write to output file
	mov	ah,40h			; write to file
	int	21h			;

	mov	dx,offset side1 	;
	call	prints			;
	call	printer 		; print first side

	pop	sheets			; get page count back
	mov	dx,offset prompt	; ask to turn paper over
	call	prints			;
	mov	ax,0c08h		; clear console
	mov	dl,0ffh 		; direct console i/o
	int	21h			;

	mov	dx,offset side2 	;
	call	prints			;
	call	printer 		; print second side
	mov	dx,offset ended 	; tell them we're done
	call	prints			;
	ret

printer proc	near			; print one side of page
doleft:
	mov	dx,offset left_side	; codes at begin of page
	mov	cx,left_side_len	; length of start-of-page codes
	mov	bx,ohandle		; write to output file
	mov	ah,40h			; write to file
	int	21h			; via dos

	test	flags,swp		; want page number?
	jz	doleft1 		; no
	mov	si,offset left_pagenr	; yes, format it
	mov	ax,btable		; offset to page table entry
	sub	ax,offset table 	; offset into table
	sub	dx,dx			; clear for divide
	add	ax,ltable		; start with page 1
	mov	cx,ltable		; get page number
	div	cx			;
	call	format			;
doleft1:
	mov	dx,offset lheader	; supplied titles
	mov	cx,lheader_len		; their length
	mov	ah,40h			; write to file
	int	21h			; via dos

	mov	si,btable		; left side table entry
	mov	cx,word ptr 4[si]	; get file offset
	mov	dx,word ptr 2[si]	;
	mov	ax,4200h		; position from front
	mov	bx,ihandle		;  of input file
	int	21h			;

	mov	si,btable		; table entry
	mov	cx,word ptr 0[si]	; length of page
	sub	cx,1			; omit ending formfeed
	jle	doright 		; empty
	mov	dx,offset buffer	; read data area
	mov	ah,3fh			; read from file
	int	21h			;

	mov	bx,ohandle		; write to output file
	mov	ah,40h			; write to file
	int	21h			;

doright:
	sub	btable,ltable+ltable	; next table entry

	mov	dx,offset right_side	; codes at begin of right side
	mov	cx,right_side_len	; length of start-of-page codes
	mov	bx,ohandle		; write to output file
	mov	ah,40h			; write to file
	int	21h			; via dos

	test	flags,swp		; want page number?
	jz	doright1		; no
	mov	si,offset right_pagenr	; yes, format it
	mov	ax,atable		; offset to page table entry
	sub	ax,offset table 	; offset into table
	sub	dx,dx			; clear for divide
	add	ax,ltable		; start with page 1
	mov	cx,ltable		; get page number
	div	cx			;
	call	format			;
doright1:
	mov	dx,offset rheader	; supplied titles
	mov	cx,rheader_len		; their length
	mov	ah,40h			; write to file
	int	21h			; via dos

	mov	si,atable		; right side table entry
	mov	cx,word ptr 4[si]	; get file offset
	mov	dx,word ptr 2[si]	;
	mov	ax,4200h		; position from front
	mov	bx,ihandle		;  of input file
	int	21h			;

	mov	si,atable		; table entry
	mov	cx,word ptr 0[si]	; length of page
	sub	cx,1			; omit formfeed
	jle	doright2		; empty
	mov	dx,offset buffer	; read data area
	mov	ah,3fh			; read from file
	int	21h			;

	mov	bx,ohandle		; write to output file
	mov	ah,40h			; write to file
	int	21h			;

doright2:
	mov	dx,offset endpage	; eject at end of page
	mov	cx,endlen		; length of end-of-page codes
	mov	bx,ohandle		; write to output file
	mov	ah,40h			; write to file
	int	21h			;

	add	atable,ltable+ltable	; next table entry

	sub	sheets,1		; decr page count
	jz	printer_exit		; no more pages
	jmp	doleft			; do next page

printer_exit:				;
	ret				; done, exit
printer endp
copy	endp


ljbook	endp

	page
;
;	convert a binary number to ascii

	public	format
format	proc	near			;format a block number
	sub	dx,dx
formatd:push	ax
	push	bx			;value in dx:ax
	push	cx			;offset to target
	push	dx
	push	di

	mov	bx,si			;save target offset
	mov	cx,6			;clear target
form0:	mov	byte ptr [si],' '
	inc	si
	loop	form0

	mov	cx,4			;four times
	sub	di,di			;divisor offset
	mov	si,bx			;restore target ptr
form1:	or	ax,ax			;it is zero?
	jnz	form10
	or	dx,dx
	jz	form2
form10: div	tenk[di]
	aam				;make al into bcd
form2:	or	ax,'00'                 ; and to ascii
	xchg	al,ah
	or	byte ptr [si],al
	mov	byte ptr [si]+1,ah
	inc	si			;next digit
	add	di,2			;next divisor
	mov	ax,dx			;copy remainder
	sub	dx,dx			; and clear hi-word
	loop	form1

	aam				;make al into bcd
	or	ax,'00'                 ; and to ascii
	xchg	al,ah
	mov	byte ptr [si]+1,ah
	mov	cx,5			;suppress leading zeros
	mov	si,bx			;get target offset back
form3:	cmp	byte ptr [si],'0'
	jne	form4
	mov	byte ptr [si],' '
	inc	si
	loop	form3

form4:	pop	di
	pop	dx
	pop	cx
	pop	bx
	pop	ax
	ret

tenk	dw	10000,1000,100,10	;for converting numbers
format	endp

	page
;
;	set up optional page headings

headers proc	near
	test	flags,swf+swd+swp+swt	; any header options?
	jz	header_exit		; no, that was easy
	test	flags,swf		; want file name?
	jz	header2 		; no
	mov	cx,40			;
	mov	si,offset ifile 	; yes, copy filename
	mov	di,offset right_fname	;
headera:
	lodsb				; copy up to end of name
	cmp	al,0			;
	je	headerb 		;
	stosb				;
	loop	headera 		;
headerb:
	mov	cx,40			;
	std				; backwards
	mov	si,offset ifile+39	;  from end of filename
	mov	di,offset left_fname	;   to end of left filename area
header1:
	lodsb				;
	cmp	al,0			; found end of name?
	loope	header1 		; not yet
	inc	cx			;
	inc	si			;
	rep	movsb			; yes, copy it
header2:
	cld				; restore direction
	test	flags,swp		; want page numbering?
	jz	header4 		; no,
	mov	si,offset page_const	; yes, copy constant
	mov	di,offset left_page	;  'page' to left side
	mov	cx,5			;
	rep	movsb			;
	mov	si,offset page_const	;
	mov	di,offset right_page	;
	mov	cx,5			;
	rep	movsb			;
header4:
	test	flags,swd		; want date in title?
	jz	header5 		; no, skip next
	mov	di,offset left_date	; format today's date
	call	getdate 		;  in left side titles
	mov	di,offset left_time	; format today's time
	call	gettime 		;  in left side titles
	mov	di,offset right_date	; format today's date
	call	getdate 		;  in right side titles
	mov	di,offset right_time	; format today's time
	call	gettime 		;  in right side titles
header5:
header_exit:
	ret
headers endp

	page
;
;	get and format current date
;
;	input: DI points to target area

getdate proc	near
	mov	ah,2ah			; get date
	int	21h			;
	push	cx			; save year
	push	dx			; save day

	mov	bl,dh			; get month
	sub	bh,bh			; form index
	shl	bx,1			;  into month
	shl	bx,1			;   name list
	lea	si,offset months-4[bx]	; copy month name
	mov	cx,4			;
	rep	movsb			;
	mov	al,' '                  ; add space
	stosb				;

	pop	dx			; recover day
	mov	al,dl			; get day
	aam				;
	xchg	al,ah			;
	or	ax,'00'                 ;
	stosw				;
	mov	ax,' ,'                 ; add delimiter
	stosw				;
	mov	ax,'91'                 ; add century
	stosw

	pop	ax			; get year(19xx)
	sub	ax,1900 		;
	aam				;
	xchg	al,ah			;
	or	ax,'00'                 ;
	stosw				;
	ret				; return
getdate endp

	page
;
;	get current time
;
;	input: DI points to target area

gettime proc	near
	mov	ah,2ch			; dos time function
	int	21h			;
	mov	al,ch			; get hours
	aam				;
	xchg	al,ah			;
	or	ax,'00'                 ;
	stosw				;
	mov	al,':'                  ; add delimiter
	stosb				;
	mov	al,cl			; get minutes
	aam				;
	xchg	al,ah			;
	or	ax,'00'                 ;
	stosw				;
	ret				; return
gettime endp

	page
;
;	tables and dynamic data areas

	even
bufsize equ	18*1024 		; input file buffer size
buffer	db	0

lstack	equ	buffer + bufsize + 512	; local stack

ltable	equ	6			; size of each entry
table	equ	lstack+2		; page/offset table
					;  0,2	 page size in bytes
					;  2,4	 file offset to top of page

pgmsize equ	lstack-cseg+512 	; paragraphs in module

cseg	ends
	end	ljbook
