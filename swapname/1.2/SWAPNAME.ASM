	page	80,132
	title	SWAP - switch names of two files
	comment |


Name:	'swap' two file names.

Usage:
	swap  [d:][path]filename1  [d:][path]filename2

Remarks:
	The two files may be on different drives, and/or in
	different sub-directories.

	Both file names must be supplied. If drive and/or path
	names are omitted, the current drive/path is used.

	Written by V.Buerg for the IBM PC using DOS 2.0 or later.
	Public domain. Feb 20, 1986.				|


rename	macro	old,new
	mov	dx,offset old		; original file name
	mov	di,offset new		;  to new file name
	mov	ah,56h			; dos rename function
	int	21h
	endm


cseg	segment	public byte 'code'
	assume	cs:cseg, ds:cseg, es:nothing
	org	100h

swap	proc	far
	jmp	start			; skip around data for masm

cr	equ	31
lf	equ	10
stopper	equ	255

errlvl	db	0			; dos return code

usage	db	cr,lf
	db	'Usage:  swap  [d:][path]filename  [d:][path]filename'
	db	cr,lf,stopper

errors	db	cr,lf,'RENAME failed, return code = '
rc	dw	0
	db	cr,lf,stopper

ptr1	dw	0			; offset to filename part
ptr2	dw	0

tempnam	db	'@-@-@-@-.$$$',0		; temporary name

file1	db	76 dup (0)		; first file name
					; d1:path1\file1

file2	db	76 dup (0)		; second file name
					; d2:path2\file2

temp	db	76 dup (0)		; intermediate file 1 name
					; d1:path1\@-@-@-@-.$$$

new1	db	76 dup (0)		; new name for first file
					; d1:path1\file2

new2	db	76 dup (0)		; new name for second file
					; d2:path2\file1
	page

start:
	mov	ah,19h			; get current drive number
	int	21h
	add	al,'A'			; make into drive letter
	mov	ah,':'
	mov	word ptr new1,ax	;  and set into filenames
	mov	word ptr new2,ax
	mov	word ptr file1,ax
	mov	word ptr file2,ax

	mov	si,81h			; point to command line
	sub	cx,cx
	or	cl,byte ptr -1[si]	; get and test length
	jnz	parms
parm_error:
	mov	dx,offset usage		; display usage info
	call	prints			;  maybe they'll get it right
	jmp	exit			;  next time

;	get the command line file names

parms:
	mov	di,offset file1		; build first d:path\filename
	call	getparm

	mov	di,offset file2		; build second name
	call	getparm

	mov	si,offset file1		; set up temp file 1 name
	mov	di,offset temp
	mov	cx,76
	rep	movsb

;	set up temporary name with drive/path from original filename

	mov	si,offset file1		; first file name
	mov	di,offset new1		; change name to that of file 2
	call	getpath
	mov	ptr1,si			; save offset to file name

	mov	si,offset file2		; second file name
	mov	di,offset new2		; change name to that of file 1
	call	getpath
	mov	ptr2,si			; save offset to file name

;	swap the file name parts

	mov	bx,ptr1			; offset to file 1 name
	mov	bp,ptr2			; offset to file 2 name

	lea	di,word ptr temp[bx]	; set temp name from file 1
	mov	si,offset tempnam
	mov	cx,13			; just lazy
	rep	movsb

	lea	si,word ptr file1[bx] 	; set new file 2 name from file 1 name
	lea	di,word ptr cs:new2[bp]
	mov	cx,13
	rep	movsb

	lea	si,word ptr cs:file2[bp] ; set new file 1 name from file 1 name
	lea	di,word ptr new1[bx]
	mov	cx,13
	rep	movsb

;	finally, do the renaming

	rename	file1,temp
	jnc	do2			; check for error return
	mov	errlvl,al
	jmp	abort			; oops, return al as error level

do2:
	rename	file2,new2		; file2 becomes file1 name
	jnc	do3			; check for error return
	mov	errlvl,al
	rename	temp,file1		; undo first rename
	jmp	abort			; return al as error level

do3:
	rename	temp,new1		; file1 becomes file2 name
	jnc	done			; check for error return
	mov	errlvl,al		; save return code
	rename	new2,file2		; undo previous renames
	rename	temp,file1
	jmp	abort			; return al as error level

done:
	sub	al,al			; zero return code
	jmp	exit

;	normal and abnormal exits

abort:
	mov	al,errlvl		; get rename return code
	aam
	xchg	ah,al
	or	ax,'00'
	mov	rc,ax			; clean up the return code
	mov	dx,offset errors	; and display a nasty message
	call	prints
exit:
	mov	al,errlvl
	mov	ah,4ch			; exit to dos
	int	21h

	subttl	- subroutines
	page
;
;	get next command line operand
;
;	si points to current char in cmd line
;	di points to target filename field

getparm	proc	near			; get next filename operand

parm1:
	lodsb				; strip leading delimiters
	cmp	al,' '
	je	parm2     		; blanks
	cmp	al,9
	jne	parm3			; tabs
parm2:	loop	parm1
	jcxz	parm_bad		; nobody home

parm3:
	cmp	byte ptr [si],':'	; does it have a drive?
	je	parm4
	add	di,2
parm4:	stosb
	lodsb				; copy first file name
	cmp	al,' '			; check for delimiter
	jbe	parm6
	loop	parm4
parm_bad:
	jmp	parm_error		; oops, ran out of data
parm6:
	ret
getparm	endp

;	get drive and path from original file name
;	and use as prefix for file names used by rename

getpath	proc	near
	push	si
	mov	cx,76			; copy original to new name
	rep	movsb

	std
	mov	cx,76			; look for ending delimiter
get_file3:
	lodsb
	cmp	al,'\'			; bumped into path?
	je	got_file3
	cmp	al,':'			; or bumped into drive?
	je	got_file3
	loop	get_file3
got_file3:
	inc	si			; ptr to filename part
	inc	si
	pop	ax
	sub	si,ax			; return offset
	cld
	ret
getpath	endp

;
;	print string like int 21h/9

prints	proc	near
	sub	cx,cx			; length of text
	mov	si,dx			; pointer to text
prints1:
	lodsb
	cmp	al,stopper		; end of string?
	je	print9
	inc	cx
	jmp	prints1
print9:
	mov	bx,1			; use stdout handle
	mov	ah,40h			; write to file handle
	int	21h
	ret
prints	endp

swap	endp

cseg	ends
	end	swap
