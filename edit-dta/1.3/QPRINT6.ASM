		page	80,132
		title	QPRINT5 - Place data directly into display buffer
		name	qprint

;   Segment, group definitions

qprint_code	segment para public 'CODESG'

dseg		segment word public 'DATASG'

dseg		ends

dgroup		group	dseg

		assume	cs:qprint_code,ds:dgroup

;   Other definitions

argz		equ	6[bp]			; Last arg
argy		equ	8[bp]			; Last arg but one
argx		equ	10[bp]			; Last arg but two
argw		equ	12[bp]			; Last arg but three


		subttl	QPRINT - Direct video I/O
		page	+

		comment &

------------------------------------------------------------------------------

Name:		QPRINT

Description:	Print a string direct to video

Usage:		CALL QPRINT(A$,ROW%,CLM%,ATTR%)

		where	ATTR% (attribute) examples:
		112	- reverse video
		113	- underlined
		135	- blinking
		15	- high intensity
		7	- normal

Authors:	Dan Rollins, Vern Buerg, Tom Neff

Revised:	Version 2q, Sept 2, 1984
		   Combined into ATORTS 21-Oct-85
		   Add /H conditional horizontal retrace delay 10-22-85
		Version 2v, Dec 15, 1985
		   Make DESQview/Topview compatible

------------------------------------------------------------------------------

		&

; Map the BIOS data area variables we'll use

bios_data	segment at 40H			; set up labels to determine

		org	10H			; color or monochrome card
equip_flag	label	word

		org	49H			; 40 or 80 column display
crt_mode	db	?			; CRT mode flag
crt_clms	label	word

		org	63H
addr_6845	label	word			; points to video card ports

bios_data	ends

; Here's the common flag for horizontal retrace delay --
; cleared by QPKHRD

do_wait 	equ	0FFH
dont_wait	equ	000H

hrd_flag	db	do_wait 		; Default setting
init_flag	db	0			; First time init switch
pad_seg 	dw	0			; Seg addr of video buffer/pad
pad_offset	dw	0			; -offset addr
card_addr	dw	0			; Addr of video card

		even

;		Rejoin CODE and start the public routine

		assume	es:bios_data

		public	qprint
qprint		proc	far

		push	bp
		mov	bp,sp			; point to arguments on stack

		mov	bx,argy 		; get addr of CLM% storage
		mov	di,[bx] 		; get the column value
		dec	di			; adjust for LOCATE format

		mov	bx,argx 		; get addr of ROW% storage
		mov	ax,[bx] 		; get the screen line value
		dec	ax			; adjust for LOCATE format

		mov	bx,argw 		; get ptr to string descriptor
		mov	ch,0			; clear hi-byte
		mov	cl,[bx] 		; get length of string
		cmp	cl,0			; null string?
		jne	get_display
		jmp	exit2			; if so,do nothing, Else,
get_display:
		mov	si,2[bx]		; SI => 1st character of VAR$

		mov	bx,bios_data		; get ready to determine card type
		mov	es,bx			; and number of columns
		mul	crt_clms		; AX = CLM% * words per line
		add	di,ax			; DI = words from start of screen
		shl	di,1			; adjust for attribute bytes

;   CX has the count of characters to write,
;   SI points to the string data,
;   DI points to a screen position

		cmp	init_flag,0		; already have video stuff?
		jne	skip_init		; yup, neato
		mov	init_flag,1
		mov	dx,addr_6845		; point to 6845 base port
		add	dx,6			; point to status port

		mov	ax,0B800H		; default to color card
;;		mov	bx,equip_flag
;;		and	bx,30H
		cmp	crt_mode,30H		; is it monochrome?
		jne	card_ok 		; no, go
		mov	ax,0B000H		; yes, set for monochrome
		mov	hrd_flag,dont_wait	;  and force /H
card_ok:
		push	cx
		mov	pad_seg,ax		; save display seg addr
		mov	card_addr,dx
		mov	cx,'DE'                 ; check for DV only
		mov	dx,'SQ'
		mov	ax,2b01h
		int	21h
		pop	cx
		cmp	al,0ffh
		je	skip_init

		push	di			; get display addr from
		sub	di,di			;  desqview
		mov	es,pad_seg		; buffer segment
		mov	ah,0feh
		int	10h
		mov	pad_seg,es		; actual pad addr
		mov	pad_offset,di
		pop	di
skip_init:
		mov	bx,argz 		; Addr of ATTR%
		mov	bh,0[bx]		; Get the color value
		mov	ax,pad_seg		; seg addr of video buffer/pad
		mov	es,ax			; points ES:DI to video area
		add	di,pad_offset
		mov	dx,card_addr		; addr of video port

; DS points to BASIC variables area
; ES points to video card memory
; Now display VAR$ on the screen.

		call	print_string

exit2:
		pop	bp
		ret	8			; intersegment return,
						; clearing stack of 4 args

qprint endp

;   This local routine displays a string of characters.

;   DS:SI => first character of string
;   ES:DI => screen memory to display it
;      CX =  number of characters to display
;      DX => status port of video card
;      BL =  attribute character

print_string	proc	near

		lodsb				; get next char
		mov	bl,al			; save char

		cmp	hrd_flag,dont_wait	; Horiz retrace delay needed?
		je	write_now		; No, skip it

; Wait for horizontal retrace


test_low:
		in	al,dx			; get status
		test	al,1			; is it low?
		jnz	test_low		; no, keep checking
		cli				; turn off interrupts

test_hi:
		in	al,dx			; get status
		test	al,1			; is it high?
		jz	test_hi 		; no, keep checking

; okay to write to screen now (no 'hash')


write_now:
		mov	ax,bx			; recover char and attr
		stosw				; char and attr to buffer
		sti				; turn interrupts back on
		loop	print_string		; do till end of string
		ret				; back to qprint proc

print_string	endp


qprint_code	ends

		end
