	page	74,132
	title	DELDUPE - Delete duplicate and/or older files
	comment |

Syntax:
	DELDUPE  directory-to-delete  [master-directory]  [/O] [/T] [/S] [/V]

	Command line options:
	  /O	delete older files
	  /S	delete similiar files, same date/time but different sizes
	  /T	test mode, list duplicates but do not delete
	  /V	verify, ask for permission to delete each file
	  /P	pause when screen fills

License:
	DELDUPE 2.1, Copyright (c) Vernon D. Buerg 1987. ALL RIGHTS RESERVED.

	DELDUPE is free, but it is a copyrighted work and may be distributed
	only pursuant to this license.

	Permission is hereby granted to reproduce and disseminate DELDUPE so
	long as:

	   (1)	No remuneration of any kind is received in exchange; and

	   (2)	Distribution is without ANY modification to the contents
		of DELDUPE.COM, DELDUPE.ASM and all accompanying
		documentation and/or support files, including the
		copyright notice and this license.

	No copy of DELDUPE may be distributed without including a copy
	of this license.

	Any other use is prohibited without express, written permission in
	advance.

		Vernon D. Buerg
		456 Lakeshire Drive
		Daly City, CA  94015-4223

		CompuServe: 70007,1212
		Data/BBS:   415-994-2944
		Fidonet:    125/4					|

	page
;
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


dta		struc			; data transfer area
dtarsvd 	db	21 dup (?)	;  reserved for DOS
dtaattr 	db	?		;  attribute found
dtatime 	dw	?		;  file's time
dtadate 	dw	?		;  file's date
dtasize 	dd	?		;  file's size (lo,hi)
dtaname 	db	13 dup (?)	;  file name and ext, asciiz form
dta		ends


files		struc			; file entry in table
filetime	dw	?		;  file's time
filedate	dw	?		;  file's date
filesize	dd	?		;  file's size (lo,hi)
filename	db	13 dup (?)	;  file name and ext, asciiz form
files		ends

file_len	equ	size files	; size of each file entry

bios		segment at 40h		; dos data area
		org	84h		;
ega_rows	label	byte		; rows on screen
bios		ends

	page
;
;	main program - data areas, equates, and constants

cseg	segment public para 'code'
	assume	cs:cseg, ds:cseg, es:nothing
	org	100h

deldupe proc	far
	jmp	start			; skip around data areas


;	equates

zero	equ	0			; constant
one	equ	1			; constant

bs	equ	8			; backspace
tab	equ	9			; a tabby
cr	equ	13			; and a carriage return
lf	equ	10			; a line feed
eof	equ	26			; end of file marker
blank	equ	32			; a space

idos	equ	21h			; dos interrupt 21h functions
 dconio equ	08h			; direct console i/o
 pstrng equ	09h			; print string
 bufcon equ	0ah			; buffered keyboard input
 select equ	0eh			; select disk
 setdta equ	1ah			; set data transfer area
 curdsk equ	19h			; get current disk
 chdir	equ	3bh			; change current directory
 write	equ	40h			; write to a file or handle
 delete equ	41h			; delete a file
 getdir equ	47h			; get current directory
 ffirst equ	4eh			; find first matching file
 fnext	equ	4fh			; find next matching file

switch_char	equ	'/'             ; delimiter for command line switches
path_char	equ	'\'             ; delimiter for path names
drive_char	equ	':'             ; delimiter for drive letters
stopper 	equ	255		; ends print string text

date	record	year:7,month:4,day:5	; dos packed date mask
time	record	hour:5,minute:6,sec:5	; dos packed time mask

	page
;
;	messages

usage	db	cr,'   '                ; overwrite the jmp
	db	cr,lf,'DELDUPE 2.1, Copyright (c) 1987, Vernon D. Buerg. ALL RIGHTS RESERVED.'
	db	cr,lf
	db	cr,lf,'Usage:'
	db	cr,lf,tab,    'deldupe directory-to-delete [master-directory]'
	db	      ' [/O] [/T] [/S] [/V] [/P]'
	db	cr,lf
	db	cr,lf,tab,    '/O  delete older files of same name'
	db	cr,lf,tab,    '/S  delete similar files (diff size only)'
	db	cr,lf,tab,    '/T  display filenames but do not delete'
	db	cr,lf,tab,    '/V  confirm the deletion of each file'
	db	cr,lf,tab,    '/P  pause when screen fills'
null	db	cr,lf,'$'
	db	bs,blank,eof		; end of usage display for TYPE

cooking db	cr,lf,'Analyzing master directory ... $'

errmsg1 db	cr,lf,'No matching files found!',cr,lf,'$'
errmsg2 db	cr,   'No duplicate or older files to delete.',cr,lf,'$'

inform1 db	'Same   '               ; identical date/time/size
inform2 db	'Older  '               ; earlier date/time
inform3 db	'Similar'               ; same date, diff size

more	db	cr,lf,'More>','$'       ; full screen prompt
prompt	db	'- delete? $'           ; verification prompt
reply	db	2,0			; buffered console read buffer
answer	db	0,0			; their answer
titles	db	cr,tab,tab,tab, 	      '- Master directory -   -- Old directory ---'
	db	cr,lf,'Reason   Filename       Bytes    Last change   Bytes    Last change'
	db	stopper

prtline db	cr,lf			; detail print line
prtwhy	db	'Similar  '             ; reason for deleting
prtname db	12 dup (' ')            ; file name and ext
oldsize db	'         '             ; file's size
olddate db	'         '             ; file's date
oldtime db	'     '                 ; file's time
prtstop label	byte			; stop line here if same
newsize db	'         '             ; file's size
newdate db	'         '             ; file's date
newtime db	'     '                 ; file's time
	db	stopper
prt_len equ	$-prtline		; length of print line

	page
;
;	constants and work areas

flags	db	0			; processing options
 older	 equ	 1			; O = delete older version of files
 test	 equ	 2			; T = display but don't really delete
 similar equ	 4			; S = delete if same date/time but diff size
 verify  equ	 8			; V = ask to confirm each delete
 pause	 equ	 10h			; P = pause when screen fills
 first	 equ	 20h			; set when headings printed 1st time

max	dw	3000			; maximum table entries (dynamic)
count	dw	0			; total number of table entries used
mcount	dw	0			; number of entries for master dir
ocount	dw	0			; number of entries for old dir
deleted dw	0			; number of files deleted
old_table dw	0			; ptr to first table entry for old dir

msg1	db	cr,lf,'Old path not found -- '
oldpath db	76 dup (0),'$'          ; directory to delete from

msg2	db	cr,lf,'New path not found -- '
newpath db	76 dup (0),'$'          ; master directory

global	db	'*.*',0                 ; for find first/next
curdrv	db	0			; current drive number
crtrows db	0			; rows on screen

dtawork db	48 dup (0)		; data transfer area

olddrv	db	' :\'                   ; original path for oldpath drive
olddir	db	64 dup (0)		; its current directory

newdrv	db	' :\'                   ; original path for newpath drive
newdir	db	64 dup (0)		; its current directory

	page
;
;	set switches from command line

start:
	push	es			; set dos data area
	mov	ax,bios 		; segment address
	mov	es,ax			;
	mov	al,byte ptr es:ega_rows ; dos rows on screen
	mov	ah,24			; default max rows
	or	al,al			; is row value ok?
	jz	start1			; no, use default
	mov	ah,al			; yes,
start1: sub	ah,2			; compensate for heading
	mov	byte ptr crtrows,ah	; set max rows on screen
	pop	es			;

	mov	dx,offset dtawork	; use local dta
	mov	ah,setdta		; set disk transfer area
	int	idos			;

	mov	ah,curdsk		; get current disk
	int	idos			;
	mov	curdrv,al		; and save for exit

	lea	sp,table		; set local stack
	mov	ax,word ptr ds:psp_bytes ; size of segment
	sub	ax,pgmsize		;  less program size
	sub	dx,dx			;
	mov	cx,file_len		; size of each table entry
	div	cx			;  to get maximum entries
	mov	max,ax			;

	mov	si,offset psp_parm_len	; point to command line
	sub	cx,cx			; to receive command line length
	lodsb
	or	cl,al			; any command line?
	jnz	switches		; yes, continue

error1:
	mov	dx,offset usage 	; operands are missing
sendmsg:
	mov	ah,pstrng		; print final message
	int	idos			;
	mov	ah,chdir		; restore current directory
	mov	dx,offset olddrv	;  for oldpath drive
	int	idos			;
	mov	ah,chdir		; restore current directory
	mov	dx,offset newdrv	;  for newpath drive
	int	idos			;
	mov	dl,curdrv		; restore current drive
	mov	ah,select		; via select disk
	int	idos			;
	int	20h			; exit as is

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
	cmp	al,'O'                  ; delete older files?
	jne	switches2		;
	or	flags, older		;
switches2:
	cmp	al,'T'                  ; display but don't delete?
	jne	switches3		;
	or	flags, test		;
switches3:
	cmp	al,'S'                  ; delete similar files?
	jne	switches4		;
	or	flags,similar		;
switches4:
	cmp	al,'P'                  ; want to pause when screen fills?
	jne	switches5		;
	or	flags, pause		;
switches5:
	cmp	al,'V'                  ; want to verify each delete?
	jne	switches6		;
	or	flags, verify		;
switches6:
	jcxz	switched		; any more operands?
	jmp	switches0		; yup

	page
;
;	get path names for old and new directories

switched:
	mov	si,offset psp_parms	; point to command line again
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
	mov	di,offset oldpath	; target for old path name
	sub	cx,1			; account for last lodsb
	jg	parm3			; if more to process
	jmp	error1			; operand(s) missing
parm3:
	stosb				; previous char
	lodsb				; next char
	cmp	al,blank		; have operand separator?
	jbe	parm4			; yes, have first op
	loop	parm3			;
	stosb				;
	jmp	short parm2a		; no second operand, use curdir

parm4:
	mov	di,offset newpath	; target for master path name
	jcxz	parm2a			; if no second operand
parm5:
	lodsb				; skip intervening delimiters
	cmp	al,blank		;
	je	parm6			;
	cmp	al,cr			; end of parameters?
	je	parm2a			; yes, just one operand
	cmp	al,tab			; skip tabs
	jne	parm7			;
parm6:	loop	parm5			; until no more command parameters

parm2a:
	mov	di,offset newpath	; target for master path name
	mov	ah,curdsk		; get current drive
	int	idos			;
	mov	dl,al			; drive letter for oldpath
	add	al,'A'                  ; make into letter
	stosb				; set master path name
	mov	ax,'\:'                 ;  to current drive
	stosw				;
	inc	dl			; letter to drive number
	mov	ah,getdir		; get current directory
	mov	si,di			;
	int	idos			;
	mov	cx,64			; maximum length to find end of name
	lodsb				; first char of path name

parm7:					; copy 2nd path name to 'newpath'
	stosb				; its first/next char
	lodsb				; get next command line char
	cmp	al,cr			; end of it?
	jbe	check1			; yes, have both operands now
	loop	parm7

	page
;
;	get and save current directory name for drive
;	containing old and new (master) directories

check1: 				; check if path names are valid
	mov	ah,curdsk		; get current drive
	int	idos			;
	add	al,'A'                  ; convert to drive letter
	mov	byte ptr olddrv,al	;  and save it
	mov	word ptr olddrv+1,'\:'  ;   in original
	mov	byte ptr newdrv,al	;    directory names
	mov	word ptr newdrv+1,'\:'  ;     with delimiters

	mov	dl,0			; to use current drive
	cmp	byte ptr oldpath+1,drive_char	; was it supplied?
	jne	check1a 		; yes
	mov	dl,byte ptr oldpath	; drive supplied with oldpath
	and	dl,5fh			; insure upper case
	mov	byte ptr olddrv,dl	; and save
	sub	dl,'A'-1                ; make into drive number
check1a:
	mov	ah,getdir		; get current directory
	mov	si,offset olddir	;  for oldpath drive
	int	idos			;
	mov	ah,chdir		; change directory
	mov	dx,offset oldpath	;  to supplied oldpath name
	int	idos			;
	jnc	check2			; found it?
	mov	dx,offset msg1		; no, issue error message
	jmp	sendmsg 		;  and exit

check2:
	mov	ah,chdir		; restore oldpath current directory
	mov	dx,offset olddrv	;  to original directory
	int	idos			;

	mov	dl,0			; to use current drive
	cmp	byte ptr newpath+1,drive_char	; was it supplied?
	jne	check2a 		; yes
	mov	dl,byte ptr newpath	; drive supplied with oldpath
	and	dl,5fh			; insure upper case
	mov	byte ptr newdrv,dl	; and save
	sub	dl,'A'-1                ; make into drive number
check2a:
	mov	ah,getdir		; get current directory
	mov	si,offset newdir	;  for newpath drive
	int	idos			;
	mov	ah,chdir		; change directory
	mov	dx,offset newpath	;   to new path name
	int	idos			;
	jnc	checked 		; found it?
	mov	dx,offset msg2		; no, issue error message
	jmp	sendmsg 		;  and exit

checked:				; current directory is now newpath

	page
;
;	build list of files in master directory

build1:
	mov	dl,byte ptr newdrv	; reset current drive
	sub	dl,'A'                  ;  to newpath drive
	mov	ah,select		; select disk
	int	idos			;

	mov	dx,offset cooking	; show that we're working
	mov	ah,pstrng
	int	idos

	mov	di,offset table 	; first table spot
	mov	dx,offset global	; filespec for master directory
	mov	cx,07h			; file attributes: R+H+S
	mov	ah,ffirst		; find first matching file
	int	idos
	or	ax,ax
	jz	build12 		; have first file?
	mov	dx,offset errmsg1	; oops, now what
	jmp	sendmsg

build12:				; add master file to the table
	lea	si,dtawork.dtatime	; point to good stuff
	mov	cx,file_len		; just this much and some more
	rep	movsb
	inc	count			; and bump entry count
	mov	ax,max			; maximum table entries
	cmp	count,ax		;  exceeded?
	jae	build2			; yup, gotta go now
	inc	mcount			;
build13:
	mov	ah,fnext		; find next matching file
	int	idos
	or	ax,ax			; any more?
	jz	build12 		; yes, add it into table

	page
;
;	build list of files in old directory

build2:
	mov	old_table,di		; save ptr to first oldpath entry

	mov	dl,byte ptr olddrv	; get drive letter for oldpath
	sub	dl,'A'                  ;  and convert to drive number
	mov	ah,select		; change current drive
	int	idos			;  to oldpath

	mov	dx,offset oldpath	; change current directory
	mov	ah,chdir		;  to oldpath
	int	idos			;

	mov	dx,offset global	; filespec for old directory search
	mov	cx,07h			; file attributes: R+H+S
	mov	ah,ffirst		; find first matching file
	int	idos			;
	or	ax,ax			; have first file?
	jz	build22 		; yes, add to table
	mov	dx,offset errmsg1	; no, empty directory
	jmp	sendmsg

build22:				; add master file to the table
	lea	si,dtawork.dtatime	; point to good stuff
	mov	cx,file_len		; just this much and some more
	rep	movsb			;
	inc	count			; and bump entry count
	mov	ax,max			; maximum table entries
	cmp	count,ax		;  exceeded?
	jae	find1			; yup, gotta go now
	inc	ocount			;
build23:
	mov	ah,fnext		; find next matching file
	int	idos
	or	ax,ax			; any more?
	jz	build22 		; yes, add it into table

	page
;
;	look for old/duplicate files now

find1:
	mov	bx,offset table 	; first master entry
find2:
	mov	bp,old_table		; first entry in old dir
	mov	dx,ocount		; these many in old dir

find2a: 				; compare new/old asciiz file names
	lea	di,filename[bp] 	; its filename part
	lea	si,filename[bx] 	; point to a master dir entry
	mov	cx,size filename	; filename length
find2b:
	lodsb				; file names match?
	cmp	al,byte ptr [di]	; match so far?
	jne	find2d			; no, try next oldpath entry
	inc	di			; yes, point to next char
	cmp	al,0			; end of asciiz name?
	je	compare 		; yes, have match
	loop	find2b			;
	jmp	compare 		; all matched
find2d:
	add	bp,file_len		; point to next entry
	sub	dx,1			; no,
	jnz	find2a			;  any more to check?
	jmp	skipit			; not found

	page
;
;	compare old/new file dates, times and sizes

compare:
	mov	si,bp			; copy oldpath dta data
	lea	di,dtawork.dtatime	;  to work area
	mov	cx,file_len		;   for comparing
	rep	movsb			;    dta fields

	lea	si,dtawork.dtatime	; compare file data
	lea	di,word ptr filetime[bx] ; except for attribute byte
	mov	cx,filename - filetime
	repe	cmpsb
	je	purge1			; different, older or what?

	test	flags,older		; allowed to delete older files?
	jnz	compare1		; yes, check further
	jmp	skipit			; no, skip further checks

compare1:
	mov	si,offset inform2	; compare dates
	mov	ax,word ptr dtawork.dtadate
	cmp	ax,word ptr filedate.[bx]
	jb	purge2			; it's older file
	je	compare2		; it's the same
	jmp	skipit			; or newer

compare2:
	mov	ax,word ptr dtawork.dtatime  ; compare times
	cmp	ax,word ptr filetime.[bx]
	jb	purge2			; it's earlier
	je	compare3		; or the same
	jmp	skipit			; or later flavor

compare3:
	mov	si,offset inform3	; it same datestamp,
	test	flags,similar		;  but different size
	jnz	purge2			;   allowed to delete?
	jmp	skipit			; if /S not supplied

	page
;
;	print file information

purge1: mov	si,offset inform1	; exact duplicate file
purge2: mov	cx,7			; copy reason to print line
	mov	di,offset prtwhy	;
	rep	movsb			;

	mov	cx,size filename	; copy file name to print line
	lea	si,dtawork.dtaname	; point to file name
	mov	di,offset prtname	;  to copy here
print1: lodsb				; next filename char
	cmp	al,zero 		; end of name?
	je	print2			; yes, ready
	stosb				; no, copy next char
	loop	print1			; continue
	jcxz	print3			; used entire name
print2:
	mov	al,blank		; pad with spaces
	rep	stosb

print3: inc	deleted 		; increment count of files processed

	mov	di,offset oldsize	; format master file size
	mov	dx,word ptr filesize+2[bx]
	mov	ax,word ptr filesize[bx]
	call	getsize

	mov	di,offset olddate	; format date of master file
	mov	ax,word ptr filedate[bx]
	call	getdate

	mov	di,offset oldtime	; format time of master file
	mov	ax,word ptr filetime.[bx]
	call	gettime 		;

	mov	prtstop,stopper 	; short print line if same
	cmp	word ptr prtwhy,'aS'    ; duplicate files?
	je	print4			; yes, skip redundant info
	mov	prtstop,blank		; clear print line

	mov	di,offset newsize	; format new file size
	mov	dx,word ptr dtawork.dtasize+2
	mov	ax,word ptr dtawork.dtasize
	call	getsize

	mov	di,offset newdate	; format date of new file
	mov	ax,word ptr dtawork.dtadate
	call	getdate

	mov	di,offset newtime	; format time of new file
	mov	ax,word ptr dtawork.dtatime
	call	gettime

print4:
	test	flags, pause		; pause when screen fills?
	jz	print5			; no, just print
	mov	ax,deleted		; number of lines so far
	mov	cl,byte ptr crtrows	; max lines on screen
	div	cl			; get page number
	or	ah,ah			; at end of screen?
	jnz	print5			; no,
	mov	dx,offset more		; yes, prompt
	mov	ah,pstrng		; for operator action
	int	idos			;
	mov	ah,dconio		; wait for a key
	int	idos			;
	and	flags,255-first 	; insure new headings

print5:
	test	flags,first		; first time to print?
	jnz	print6			; no, already have titles
	mov	dx,offset titles	; yes, show headings
	call	prints			;
	or	flags,first		; and indicate have titles
print6:
	mov	dx,offset prtline	; print detail line
	call	prints			;

	test	flags, test		; just display possible actions?
	jnz	skipit			; yes, don't really delete
	page
;
;	delete the duplicate file

	test	flags, verify		; want to confirm each delete?
	jz	purge_now		; no, just do it
	and	flags,255-pause 	; /P is superfluous

askem:
	mov	dx,offset prompt	; display prompt message
	mov	ah,pstrng		; use print string function
	int	idos			;
	mov	dx,offset reply 	; point to reply buffer
	mov	ah,bufcon		;  for buffered console i/o
	int	idos			;
	mov	al,byte ptr answer	; get their one char answer
	and	al,5fh			; make it upper case
	cmp	al, 'Y'                 ; want to proceed?
	je	purge_now		;  yes
	jmp	skipit			;  no, let null enter skip it

purge_now:
	lea	dx,dtawork.dtaname	; point to file name
	mov	ah,delete		; delete a file
	int	idos			;
	jc	skipit			; oops, doesn't count

;	bump to next table entry

skipit:
	add	bx,file_len		; point to next file entry
	sub	mcount,one		; any more?
	jle	finished		;
	jmp	find2			; yup, work work work

;	finished processing all table entries

finished:
	mov	dx,offset null		; all done
	cmp	deleted,zero		; deleted any files?
	ja	done			; yes, looks good
	mov	dx,offset errmsg2	; no, say so
done:
	jmp	sendmsg 		; emit final blank line

	page
;
;	Format the date
;
; Input:	AX contains file date
;		DI points to area to fill in with formatted date

getdate proc	near			; format the date
	or	ax,ax			; is it valid?
	jz	gotdate 		; no, quit

	push	ax			;Save it
	and	ax,mask month		;Get month part
	mov	cl,month		;Bits to shift
	call	cnvrt
	cmp	al,'0'                  ; Suppress leading zero
	jne	getdat1
	mov	al,' '
getdat1:stosw
	mov	al,'/'
	stosb
	pop	ax			;Get the date back

	push	ax
	and	ax,mask day		;Get day part
	mov	cl,day			;Bits to shift
	call	cnvrt
	stosw
	mov	al,'/'
	stosb
	pop	ax

	and	ax,mask year		;Get year part
	mov	cl,year 		;Bits to shift
	call	cnvrt
	or	al,'8'                  ;Adjust for base year
	stosw

gotdate:
	ret
getdate endp

;	Format the time
;
; Input:	AX contains file time
;		DI points to area to fill in with formatted time

gettime proc	near			; format the date
	or	ax,ax			; is it valid?
	jz	gottime
	push	ax			; save date
	and	ax,mask hour		; get hour part
	mov	cl,hour 		; mask bits to shift
	shr	ax,cl
	call	cnvrt1
	stosw
	mov	al,':'
	stosb
	pop	ax			; get the time back
	and	ax,mask minute		; get min part
	mov	cl,minute		; bits to shift
	call	cnvrt
	stosw
gottime:
	ret
gettime endp

cnvrt	proc	near
	shr	ax,cl
cnvrt1: aam				; make al into bcd
	or	ax,'00'                 ;  and to ascii
	xchg	al,ah
cnvrtd: ret
cnvrt	endp

	Page
;
;	Format double word
;
; Input:	DX:AX has binary value to format
;		DI points to area to fill with formatted ascii number

ddptr	Dw	0

getsize proc	near			; formats a 32 bit integer
	push	bp			;  in dx:ax
	push	bx			;  to ds:si
	push	di
	push	si
	mov	ddptr,di		; addr of target field
	mov	di,dx			; routine uses di:si
	mov	si,ax
	call	printdw
	pop	si
	pop	di
	pop	bx
	pop	bp
	ret

printdw:
	xor	ax,ax			; clear work regs
	mov	bx,ax			;
	mov	bp,ax			;
	mov	cx,32			; bits of precision
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
	shr	dl,1			; move high
	shr	dl,1			;  nibble to
	shr	dl,1			;   the low
	shr	dl,1			;    position
	call	j4
	mov	dl,dh
j4:	and	dl,0fh			; mask low nibble
	jz	j5			; if not zero
	sub	cl,cl
j5:	dec	ch
	and	cl,ch
	or	dl,'0'                  ; fold in ascii zero
	sub	dl,cl
	mov	bx,ddptr
	mov	[bx],dl 		; ptr to next target field
	inc	ddptr
	ret

j6:	adc	al,al
	daa
	xchg	al,ah
	adc	al,al
	daa
	xchg	al,ah
	ret
getsize endp

	page
;
;	Print string like int 21h function 9

prints	proc	near			; dx has offset to string
	push	di			;  ending in char x'ff'
	push	bx			;
	push	cx			;
	mov	di,dx			; ptr to string text
	mov	cx,-1			; overall text length
	mov	al,stopper		; find ending hex ff
	repne	scasb			;
	not	cx			; length is bytes scanned
	mov	bx,1			; standard output device
	mov	ah,write		; write to a file or handle
	int	idos			;
	pop	cx			; recover registers
	pop	bx			;
	pop	di			;
	ret				;
prints	endp

	page
;
;	dynamic work areas

	even

lstack	label	byte			; local stack

table	equ	byte ptr lstack+256	; contains master file entries
					; as many as free memory will permit

pgmsize equ	table-cseg+256		; program, psp and stack size

deldupe endp

cseg	ends

	end	deldupe
