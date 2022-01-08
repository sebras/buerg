	page	74,132
	title	ljbook - print files 2-up 2-sided on hp ljp

; syntax:	ljbook	filename  [outfile]  [/f] [/p] [/d] [/2] [/t...]

; v0.90 7/02/87 - first flyer
; v0.97 7/05/87 - add option switches
; v0.98 7/19/87 - correction for multiples of 4 pages
; v0.99 8/10/87 - correction for files over 256 pages
; v1.0 10/05/87 - first public release
; v1.01 11/22/87 - play with line length and margins
; v1.02 1/14/88 - some suggestions from Guy Gallo
;		- print only one sheet if 1 or 2 pages
;		- leave empty pages blank
; v1.03 1/15/88 - process tabs
; v1.04, 1/26/88 - add /T title option
; v1.05, 1/26/88 - add /2 option
; v1.06, 2/05/88 - correct tab spacing

cpl	equ	83			; characters per line		;101

display macro	txt
	mov	dx,offset txt		; offset to message
	call	prints			; display it
	endm


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
	display null			; space last line
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

version db	cr,lf,'LJBOOK  (c) Copyright 1987,1988 by Vernon D. Buerg'
	db	cr,lf,'Version 1.06. For personal use only. May not be sold.',stopper
usage	db	cr,lf
	db	cr,lf,'Usage:'
	db	cr,lf,'       ljbook  filename  [outfile] [/f][/p][/d][/2][/t...]'
	db	cr,lf
	db	cr,lf,'       /f       put filename in heading of each page'
	db	cr,lf,'       /p       put page number in heading'
	db	cr,lf,"       /d       put today's date/time in heading"
	db	cr,lf,'       /2       one sided, two up printing'
	db	cr,lf,"       /ttext   put 'text' in heading"
null	db	cr,lf,stopper,26

flags	db	0			; procesing options
 swf	equ	1			; /f = filename in heading
 swd	equ	2			; /d = put today's date/time in heading
 swp	equ	4			; /p = put page numbers in heading
 swm	equ	8			; /m = left margin (not implemented)
 swt	equ	16			; /t = title supplied
 sw2	equ	32			; /2 = one sided, two up

errlvl	db	0			; dos error level returned
lastchr db	0			; previously read char

max	dw	0			; maximum pages/table entries
min	dw	128			; minimum

right_table	dw	offset table	; offset to next right side entry
left_table	dw	offset table	; offset for left side

pages	dw	1			; number of pages
sides	dw	0			; number of two-up pages
sheets	dw	0			; number of sheets

round_up	dw	3		; to make
round_mask	dw	0FFFCh		;   multiple of 4 or 2

lpp	equ	66			; lines per page
lcnt	dw	0			; current lines on page
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

init	label	byte			; initialization strings	;102
	db	esc,'&l1o'              ; landscape
	db	     'l8d'              ; 8 lpi                         ;099
	db	     '1e'               ; top margin                    ;099
	db	     '67f'              ; text length, 8x8.5=68 lines   ;099
;;	db	     'k2s'              ; compressed print              ;105
	db	     '5.5C'             ; vertical motion index = n/48  ;099
	db	esc,'(s0p'              ; fixed spacing                 ;099
	db	     '16.66h'           ; font pitch \ see k2s          ;099
	db	     '8.5v'             ; point size /                  ;099
	db	     '0d'               ; style                         ;099
	db	     '0b'               ; weight                        ;099
	db	     '0t'               ; typeface                      ;099
	db	     '1C'               ; disable line wrap             ;101
;;	db	esc,'(8U'               ; use USASCII symbol set        ;102
initlen equ	$-init

					; printer codes for left side
left_side	db	27,'9';cr       ;  clear margins
		db	27,'&a1r'       ;  line 1                       ;099
		db	    'a0l'       ;  left margin                  ;099
		db	    'a89M'      ;  right margin                 ;101
		db	cr		;  column 0
left_side_len	equ	$-left_side

					; printer codes for right side
right_side	db	27,'9';cr       ;  clear margins
		db	27,'&a1r'       ;  line 1                       ;099
		db	     '96l'      ;  left margin                  ;102
		db	     '178M'     ;  right margin                 ;101
		db	cr		;  column 96 (col 1)
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

ended	db	cr,   'Finished printing. ',cr,lf,stopper

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

months	db	' Jan Feb Mar Apr MayJuneJuly Aug Sep Oct Nov Dec'

	page
;
;	check dos version

chkver	proc	near
	display version 		; display verion number
	mov	ah,30h			; get dos version
	int	21h			;
	cmp	al,2			; at least 2.0?
	jae	chkdver 		;  yes, good
	mov	dx,offset msgver	;  no, complain
	jmp	error			;   and exit
chkdver:				;
	ret				; resume
chkver	endp				;

	page
;
;	parse command line

parms	proc	near
	mov	si,offset psp_parm_len	; point to command line
	sub	cx,cx			; to receive command line length
	lodsb				;
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
	jne	switches6		; nope, all done here
	sub	cx,1			; less the switch and ending cr
	jle	switches6		; oops, t'aint none
	cmp	cx,40			; too long?
	jbe	switches5a		; no, it will fit
	mov	cx,40			;
switches5a:
	push	cx			; save remaining length
	mov	di,offset right_fname	;
	rep	movsb			; overlay filename with title
	pop	cx			; get length back
	dec	si			; point to last char
	mov	di,offset left_fname	; left side is backwards
	std				;
	rep	movsb			;
	cld				; back to normal direction
	or	flags, swt		; we have titles
	and	flags, 255-swf		; can't have both

switches6:
	cmp	al,'2'                  ; one sided, two up?
	jne	switches7		;
	or	flags, sw2		;
	mov	round_up,1		; reset round up factors
	mov	round_mask,0FFFEh	;

switches7:
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
	stosw				;
	stosw				;
	stosw				;
	loop	alloc1			;
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
	ret				; resume
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
	mov	bx,right_table		; pointer to table entry
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
;102	jne	scanread		; no, keep reading
	je	scan3			; yes, check for full page
	cmp	al,tab			; is it a tabby?
	jne	scanread		; no, read some more
	add	linelen,7		; yes, bump to
	and	linelen,0fff8h		;  next tab column
	jmp	scanread		;   and continue reading
scan3:
	cmp	lcnt,0			; any lines yet?
	jne	scan4			; yes, have lines to print
	cmp	lastchr,lf		; no, but was previous an lf?
	je	scanread		; yes, already have page boundary
scan4:
	inc	pages			; bump page count
	mov	lcnt,0			; reset line counter
	add	bx,ltable		; point to next table entry
	mov	right_table,bx		;
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
	mov	ax,pages		;				;102
	cmp	ax,2			; 2 or less pages?		;104
	ja	copy1			; no, need form feeds		;104
	mov	endpage,' '             ; yes, use one side only        ;104
copy1:
	add	ax,round_up		; round up pages		;104
	and	ax,round_mask		;  to multiple of four or two	;104
	shr	ax,1			; number of two-up pages
	mov	sides,ax		;
	test	flags, sw2		; just one side?		;105
	jz	copy5			; yes, sheets=sides		;105
	mov	right_table,offset table+ltable ; first right page	;105
	mov	left_table,offset table ; and first left page		;105
	mov	sheets,ax		; save count			;105
	jmp	short	copy6		;				;105

copy5:
	shr	ax,1			; number of pages, two sides each
	mov	sheets,ax		;

	mov	ax,sides		; get ptr for left side entries
	shl	ax,1			; number of sheets  to pages
	dec	ax			; adjust for zero indexing
	mov	cx,ltable		; get table
	mul	cx			;   pointer
	add	ax,offset table 	;    for last entry
	mov	left_table,ax		; and save it

	mov	ax,offset table 	; ptr for first left side entry
	mov	right_table,ax		;  and save it

copy6:
	push	sheets			; save for second pass

	mov	dx,offset init		; initialization codes
	mov	cx,initlen		; length of start-of-page codes
	mov	bx,ohandle		; write to output file
	mov	ah,40h			; write to file
	int	21h			;

	mov	ax,sheets		;
	mov	si,offset infonr	; tell how many sheets
	call	format			;
	display info			;

	display side1			; say printing side 1

	call	printer 		; print first side

	pop	sheets			; get page count back

	test	flags, sw2		; one sided?			;105
	jnz	copy4			; yes, all done 		;105

	cmp	pages,2 		; just one sheet needed?	;103
	jbe	copy3			; yes, skip prompt		;103

copy2:
	display prompt			; ask to turn paper over

	mov	ax,0c08h		; clear console
	mov	dl,0ffh 		; direct console i/o
	int	21h			;

	display side2			; say printing side 1

copy3:
	call	printer 		; print second side
copy4:
	cmp	endpage,ff		; need final eject?
	je	copy_ended		; no
	mov	endpage,ff		; form feed
	mov	dx,offset endpage	; eject at end of page
	mov	cx,endlen		; length of end-of-page codes
	mov	bx,ohandle		; write to output file
	mov	ah,40h			; write to file
	int	21h			;

copy_ended:
	display ended			; tell them we're done
	ret

	page
;
;	copy left and right sides to printer one sheet at a time

printer proc	near			; print one side of page
doright:
	mov	dx,offset right_side	; codes at begin of right side
	mov	cx,right_side_len	; length of start-of-page codes
	mov	bx,ohandle		; write to output file
	mov	ah,40h			; write to file
	int	21h			; via dos

	mov	si,offset right_pagenr	; calculate page number
	mov	ax,right_table		; offset to page table entry
	sub	ax,offset table 	; offset into table
	sub	dx,dx			; clear for divide
	add	ax,ltable		; start with page 1
	mov	cx,ltable		; get page number
	div	cx			;
	or	ax,ax			; page 0?
	jz	doleft			; oops
	cmp	ax,pages		; empty page?
	ja	doleft			; yes, leave it blank
	test	flags,swp		; want page number?
	jz	doright1		; no
	call	format			;
doright1:
	mov	dx,offset rheader	; supplied titles
	mov	cx,rheader_len		; their length
	mov	ah,40h			; write to file
	int	21h			; via dos

	mov	si,right_table		; right side table entry
	mov	cx,word ptr 4[si]	; get file offset
	mov	dx,word ptr 2[si]	;
	mov	ax,4200h		; position from front
	mov	bx,ihandle		;  of input file
	int	21h			;

	mov	si,right_table		; table entry
	mov	cx,word ptr 0[si]	; length of page
	sub	cx,1			; omit formfeed
	jle	doleft			; empty
	mov	dx,offset buffer	; read data area
	mov	ah,3fh			; read from file
	int	21h			;

	call	printf			; print this block

doleft:
	mov	dx,offset left_side	; codes at begin of page
	mov	cx,left_side_len	; length of start-of-page codes
	mov	bx,ohandle		; write to output file
	mov	ah,40h			; write to file
	int	21h			; via dos

	mov	si,offset left_pagenr	; determine page number
	mov	ax,left_table		; offset to page table entry
	sub	ax,offset table 	; offset into table
	sub	dx,dx			; clear for divide
	add	ax,ltable		; start with page 1
	mov	cx,ltable		; get page number
	div	cx			;
	or	ax,ax			; page 0?
	jz	doleft2 		; oops
	cmp	ax,pages		; is this page empty?
	ja	doleft2 		; yes, don't over-write header

doleft0:
	test	flags,swp		; want page number?
	jz	doleft1 		; no, skip next
	call	format			; yes, make it readable

doleft1:
	mov	dx,offset lheader	; supplied titles
	mov	cx,lheader_len		; their length
	mov	ah,40h			; write to file
	int	21h			; via dos

	mov	si,left_table		; left side table entry
	mov	cx,word ptr 4[si]	; get file offset
	mov	dx,word ptr 2[si]	;
	mov	ax,4200h		; position from front
	mov	bx,ihandle		;  of input file
	int	21h			;

	mov	si,left_table		; table entry
	mov	cx,word ptr 0[si]	; length of page
	sub	cx,1			; omit ending formfeed
	jle	doleft2 		; empty
	mov	dx,offset buffer	; read data area
	mov	ah,3fh			; read from file
	int	21h			;

	call	printf			; copy file to printer

doleft2:
	mov	dx,offset endpage	; eject at end of left page
	mov	cx,endlen		; length of end-of-page codes
	mov	bx,ohandle		; write to output file
	mov	ah,40h			; write to file
	int	21h			;

	add	right_table,ltable+ltable ; next right table entry
	test	flags,sw2		; one sided?
	jnz	doleft3 		; yes,
	sub	left_table,ltable+ltable  ; next left side table entry
	jmp	short doleft4		;

doleft3:
	add	left_table,ltable+ltable ; next one-sided left side page
doleft4:
	sub	sheets,1		; decr sheet count
	jle	printer_exit		; no more sheets
	jmp	doright 		; do next page

printer_exit:				;
	ret				; done, exit

	page
;
;	copy file's page to printer with tabbing

flen	dw	0			; length of file's page

printf:
	mov	si,offset buffer	; page's file data
	mov	flen,ax 		; set length
printf2:
	mov	di,offset pline 	; to a single print line
	mov	bx,0			; relative column
printf3:
	lodsb				; get next char
	dec	flen			; decr length remaining
	cmp	al,tab			; is it a tab char?
	jne	printf4 		; no, check for new line
	mov	cx,bx			; current column
	add	cx,8			; round up
	and	cx,0fff8h		;  to tab column
	sub	cx,bx			; get number of
	add	bx,cx			;  blank chars
	jcxz	printf8 		;
	mov	al,' '                  ; move in
	rep	stosb			;  the blanks
printf8:
	jmp	printf6 		;

printf4:
	stosb				; copy next char
	inc	bx			; bump column
	cmp	al,lf			; new line?
	je	printf5 		; yes, print it now
	cmp	al,cr			; overlap line?
	jne	printf6 		; no, continue
	mov	bx,0			; yes, reset tab column

printf6:
	cmp	flen,0			; any length remaining?
	jne	printf3 		; yes, get next char
	mov	al,lf			; append final lf
	stosb				;

printf5:
	mov	dx,offset pline 	; start of line
	mov	cx,di			;  less end of line
	sub	cx,dx			;   as length of line
	jle	printf9 		; null line?
	mov	bx,ohandle		; output file
	mov	ah,40h			; write to file
	int	21h			;
printf9:
	cmp	flen,0			; all done?
	jg	printf2 		; no, do another line
	ret				; resume
printer endp

copy	endp

ljbook	endp

	page
;
;	convert a binary number to ascii

	public	format
format	proc	near			; format a block number
	sub	dx,dx			; entry for one word in ax only
formatd:push	ax
	push	bx			; value in dx:ax
	push	cx			; offset to target
	push	dx			;
	push	di			;

	mov	bx,si			; save target offset
	mov	cx,6			; clear target
form0:	mov	byte ptr [si],' '       ;
	inc	si			;
	loop	form0			;

	mov	cx,4			; four times
	sub	di,di			; divisor offset
	mov	si,bx			; restore target ptr
form1:	or	ax,ax			; it is zero?
	jnz	form10			;
	or	dx,dx			;
	jz	form2			;
form10: div	tenk[di]		;
	aam				; make al into bcd
form2:	or	ax,'00'                 ; and to ascii
	xchg	al,ah			;
	or	byte ptr [si],al	;
	mov	byte ptr [si]+1,ah	;
	inc	si			; next digit
	add	di,2			; next divisor
	mov	ax,dx			; copy remainder
	sub	dx,dx			; and clear hi-word
	loop	form1			;

	aam				; make al into bcd
	or	ax,'00'                 ; and to ascii
	xchg	al,ah			;
	mov	byte ptr [si]+1,ah	;
	mov	cx,5			; suppress leading zeros
	mov	si,bx			; get target offset back
form3:	cmp	byte ptr [si],'0'       ;
	jne	form4			;
	mov	byte ptr [si],' '       ;
	inc	si			;
	loop	form3			;

form4:	pop	di			; restore work regs
	pop	dx			;
	pop	cx			;
	pop	bx			;
	pop	ax			;
	ret				; resume

tenk	dw	10000,1000,100,10	; for converting numbers
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
	ret				; resume
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
pline	label	byte			; each print line

bufsize equ	18*1024 		; input file buffer size
buffer	equ	pline+256		;

lstack	equ	buffer + bufsize + 512	; local stack

ltable	equ	6			; size of each entry
table	equ	lstack+2		; page/offset table
					;  0,2	 page size in bytes
					;  2,4	 file offset to top of page

pgmsize equ	lstack-cseg+512 	; paragraphs in module

cseg	ends
	end	ljbook
