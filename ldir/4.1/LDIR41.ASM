	page	74,132
	title	--- ldir - list directory -

;    LDIR (c) Copyright Vernon D. Buerg 1985-1989
;    ALL RIGHTS RESERVED.

dtantry struc				; DTA entry returned by DOS
dtarsvd db	21 dup (0)		;  reserved
dtaattr db	0			;  attribute
dtatime dw	0			;  update time
dtadate dw	0			;  update date
dtasize dw	0,0			;  size bytes (lo,hi)
dtaname db	12 dup (' ')            ;  name and ext
	db	0,13,10,255		;  stopper and print
dtantry ends

argntry struc				; Search arguments
argdriv db	0,':'                   ;  drive
argpath db	'\'                     ;  path delimiter
argname db	64 dup (0),255		;  path,file,ext
argntry ends

tblntry struc				; Table Entries
tblattr db	0			;  attribute
tblpath db	21 dup (0)		;  path name(s)
tblname db	8 dup (' ')             ;  file name
tbldot	db	' '                     ;  delimiter
tblext	db	3 dup (' ')             ;  extension
tblsize db	' 0000000 '             ; File size
tbldate db	'80-01/01 '             ; Date
tbltime db	' 0:00 '                ; Time
tblfatr db	3 dup (' ')             ; File attributes
tblctl	db	13,10,255		; print control chars
tblntry ends

filntry struc				; List of files in table
filsub	db	0			; -index to subdirectory name
filattr db	0			; -file attributes
filtime dw	0			; -time stamp
fildate dw	0			; -date stamp
filsize dw	0,0			; -file size
filname db	12 dup ('?')            ; -asciiz file name
filstop db	?			; -asciiz stopper
filntry ends


bios	segment at 40h		; dos data area
	org	84h		;
ega_row label	byte		; rows on screen
bios	ends

save	macro	reglist
	irp	reg, <reglist>
	push	reg		; save register
	endm
	endm

return	macro	reglist
	irp	reg, <reglist>
	pop	reg		; restore register
	endm
	ret			; return to caller
	endm


cseg	segment public para 'CODE'
	assume	cs:cseg, ds:cseg, es:nothing
	org	100h

ldir	proc	far
	mov	sp,offset local_stack_end ; Use local stack
	mov	word ptr stackx,sp	  ; Save stack ptr for exiting
	jmp	start

	page
;
;	Data Areas, Constants, Etc.

dta_len equ	size dtantry		; DTA length
arg_len equ	size argntry		; Argument length
tbl_len equ	size tblntry		; Disk record entry
fil_len equ	size filntry		; File description entry

tblpara equ	tbl_len/16		; paragraphs in each table entry

depth	equ	3			; Maximum sub-DIR nest level
tab	equ	9			; A tabbie
lf	equ	10			; Line feed
cr	equ	13			; Carriage return
stopper equ	255			; Ends print strings

curdsk	equ	19h			;Get current disk
setdta	equ	1ah			;Set data transfer area
dskspc	equ	36h			;Get disk free space
chdir	equ	3bh			;Change directory
write	equ	40h			;Write to a file handle
getpath equ	47h			;Get current directory

stackx	dw	0			; Entry stack pointer
dirmask db	0			; Directory flags mask
errlvl	db	0			; DOS return code
_attr	db	7			; Clear attribute
_page	db	0			; Video page
_rows	db	0			; Rows on screen

flags	db	byname			; Command switches
 byattr  equ	1			; -attributes included
 byhide  equ	2			; -want hidden files
 byclear equ	4			; -clear screen
 bydate  equ	8			; -sort by date/time
 byext	 equ	10h			; -sort by extension
 byname  equ	40h			; -sort by name
 bysize  equ	80h			; -sort by size

flags2	db	0			; More switches
 bymod	 equ	01h			; -modified files only
 bywait  equ	02h			; -wait when screen full
 bybrief equ	4			; -four up
 bypath  equ	20h			; -all paths

date	record	yr:7,mo:4,dy:5		; Packed date
time	record	hour:5,min:6,sec:5	; Packed time

anyname db	'\????????.???',0,stopper ;Global filename.ext
subdir	db	'-Dir'

count	dw	0			; Number of files
numdir	dw	0			; Number of table entries
maxdir	dw	0			; Maximum table entries
nxtdir	dw	0			; Offset to next entry
segdir	dw	0			; Segment addr of of gotten table
numbyte dw	0,0			;Total bytes used
linecnt db	0			;Line counter for /W

ddptr	dw	0

	page
;
;	Headings and titles

titlea	db	'List DIRectory            Volume: '
volname db	11 dup (' '),11 dup (' ')
month	db	'mm/'
day	db	'dd/'
year	db	'yy '
hours	db	'hh:'
mins	db	'mm:'
secs	db	'ss',cr,lf,stopper

more	db	'... more',stopper
backsp	db	8 dup (8),stopper	; backspace over 'more'

titleb	db	tab,tab,tab,tab,'  '    ;Command parameters
titles	db	64 dup (0),stopper	;Current directory

titlec	db	cr,lf,'Filename Ext   Bytes  -Last Change-     '
titled	db	'Filename Ext   Bytes  -Last Change-'
newline db	lf,cr,stopper
nrmsg	db	cr,cr,2 dup (' ')       ;Ending message
nrbytes db	'       0 bytes in'
nrfiles db	'       0 File(s);  '
nrsize	db	'       0 bytes free.',stopper


extfcb	db	255,0,0,0,0,0		; Extended FCB to get label
	db	8			; Attribute
drivenr db	0,11 dup('?')           ; Drive number
	db	2 dup(0)		; Current block number
	db	3 dup(0)		; Logical record size
	db	20 dup(0)		; File size

temp	db	0			; Sort exchange area
origdr	db	'x:'                    ; Original drive
origdir db	'\',63 dup (0)          ; and path
origptr dw	origdir 		; End of orig path name

rootdir db	'x:\',0                 ; To get vol label
olddate db	8 dup (0)		;
drptr	dw	offset parmdr		;

model	tblntry <>			; Model print line
	page
;
;	Set default drive and path

start:
	mov	ah,8			; Get monitor stuff
	int	10h			;
	mov	_page,0 		; -video page
	mov	_attr,ah		; -current attribute

	push	es			; set dos data area
	mov	ax,bios 		; segment address
	mov	es,ax			;
	mov	al,byte ptr es:ega_row	; dos rows on screen
	mov	ah,24			; default max rows
	or	al,al			; is row value ok?
	jz	start1			; no, use default
	mov	ah,al			; yes,
start1: sub	ah,2			; compensate for heading
	mov	byte ptr _rows,ah	; set max rows on screen
	pop	es			;

	call	switchs 		; Get program options

	mov	ah,13			; Reset diskettes
	int	21h			;

	mov	ah,curdsk		; Get current disk
	int	21h			;
	add	al,'A'                  ;
	mov	origdr,al		; Save original drive letter
	mov	rootdir,al		;  for reading vol label
	mov	parmdr,al		;

	mov	dx,offset dta		; Set Data Transfer Area
	mov	ah,setdta		;
	int	21h			;

	call	getparm 		; Get desired dr:path in 'parmdir'

	call	getvol			; Get vol name, current dir in 'origdir'

	call	setarg			; Set search argument

	call	alloc			; Allocate table for directory

	call	clock			; Date/time to heading

	call	getdir			; Read the directory

	test	flags,255		; Any sort options?
	jz	nosort			; no, display fifo dir
	call	sort			; Sort directory table

nosort:
	call	print			; Display the entries

	mov	ax,count		; Number of files
	sub	dx,dx			;
	mov	si,offset nrfiles	;
	call	format			;

	mov	dx,numbyte		; Total bytes used
	mov	ax,numbyte+2		;
	mov	si,offset nrbytes	;
	call	format			;

	mov	dx,offset nrmsg 	; Display summary stats

exit:	mov	sp,cs:stackx		; Insure exiting stack
	call	prints			; Display final message

done:	mov	sp,cs:stackx		; Insure exiting stack
	mov	al,errlvl		; Return to system
	mov	ah,4ch			; via EXIT with error level
	int	21h			;

ldir	endp

	page
;
;	Set options from command line

switchs proc	near
	mov	si,82h			; Command tail
	mov	dh,flags		; Default switches
	mov	dl,flags2
	sub	cx,cx
	or	cl,byte ptr -2[si]	; test parm length
	jz	switch_exit		; none, return as-is

sw1:	lodsb				; Scan for switch
	cmp	al,'/'
	loopne	sw1
	or	cx,cx			; found one?
	jz	switch_exit
	mov	byte ptr -1[si],cr	; Stop string here
	jmp	short sw2a

switch_exit:
	mov	flags,dh		; Store new switches
	mov	flags2,dl

	mov	al,dirmask		; Current directory attribute mask
	test	flags,byhide		;  include hidden files
	jz	swx1
	or	al,2
swx1:	test	flags,byattr		;  include display of attributes?
	jz	swx2
	or	al,7
swx2:	test	flags2,bypath		;  include sub-directories?
	jz	swx3
	or	al,16
swx3:	mov	byte ptr dirmask,al	; Update dir search criteria
	ret

sw2:	lodsb
	cmp	al,'/'                  ; Another switch?
	loopne	sw2
	jcxz	switch_exit

sw2a:	lodsb				; yes, get letter following
	dec	cx
	jle	sw3			; missing switch

sw3:	cmp	al,'?'                  ; Help?
	jne	sw4
	mov	dx,offset help
	jmp	exit

sw4:	and	al,0dfh 		; Make option uppercase
	cmp	al,'A'                  ; Attributes?
	jne	sw5
	or	dh,byattr
sw5:	cmp	al,'B'                  ; Brief?
	jne	sw6
	or	dl,bybrief
sw6:	cmp	al,'C'                  ; Clear?
	jne	sw7
	or	dh,byclear
	call	cls
sw7:	cmp	al,'D'                  ; Date?
	jne	sw8
	or	dh,bydate
sw8:	cmp	al,'X'                  ; Ext?
	jne	sw9
	or	dh,byext
sw9:	cmp	al,'P'                  ; Paths?
	jne	sw10
	or	dl,bypath
sw10:	cmp	al,'S'                  ; Size?
	jne	sw11
	or	dh,bysize
sw11:	cmp	al,'H'                  ; Hidden?
	jne	sw12
	or	dh,byhide
sw12:	cmp	al,'M'                  ; Modified only
	jne	sw12b
	or	dl,bymod
sw12b:	cmp	al,'W'                  ; Wait when screen fills?
	jne	sw12c
	or	dl,bywait
sw12c:	cmp	al,'F'                  ; Sort by filename?
	jne	sw12d
	or	dh,byname
sw12d:	cmp	al,'N'                  ; No sorting?
	jne	sw13
	and	dh,0ffh-byname-byext-bysize-bydate

sw13:	jmp	sw2			; Try for another option

switchs endp
	page
;
;	Copy command parameters

getparm proc	near
	mov	si,82h			; Command tail
	mov	di,offset parmdir	; goes after d:\
	sub	cx,cx			;
	or	cl,byte ptr -2[si]	; any parmeters?
	jz	parm9			; no, use defaults

parm0:	cmp	byte ptr 1[si],':'      ; Drive specified?
	jne	parm1			;  no
	mov	di,offset parmdr	;  yes, replace drive letter

parm1:	lodsb				; Skip leading blanks
	cmp	al,' '                  ;
	jne	parm3			;
	loope	parm1			;
	jcxz	parm9			;

parm2:	lodsb				; Copy d:\path\fname.ext
parm3:	cmp	al,cr			; end of string?
	je	parm9			;
	cmp	al,' '                  ; end of operand?
	jbe	parm9			;
	cmp	al,','                  ;
	je	parm9			;
	stosb				;
	loop	parm2			;

parm9:	and	parmdr,0dfh		; Upper case drive parm
	mov	drptr,di		; Save ptr to parm end
	mov	al,0			; Insure asciiz
	stosb				;
	mov	al,parmdr		;
	mov	origdr,al		;
	mov	rootdir,al		;
	ret				;
getparm endp
	page
;
;	Get volume label and disk free space

getvol	proc	near
	mov	dl,parmdr		; Get drive letter
	sub	dl,64			; and make it a number
	mov	drivenr,dl		;
	mov	si,offset origdir+1	; Save current path name
	mov	ah,getpath		;
	int	21h			;

	mov	al,0			; Get end of path name
	mov	di,offset origdir	;
	mov	cx,67			;
	repne	scasb			;
	sub	di,2			;
	mov	origptr,di		;

	cmp	origdir+1,0		; Already in root?
	je	getvl3			; yes, no chdir needed
	inc	origptr 		;
	mov	dx,offset rootdir	; no, point to root directory
	mov	ah,chdir		;
	int	21h			;
	jc	getvl9			;

getvl3: mov	dx,offset extfcb	; Search for volume entry
	mov	ah,11h			;
	int	21h			;

	or	al,al			; Any found?
	jnz	getvl4			; no, tough
	mov	cx,11			; yes, copy it to heading
	mov	si,offset dta+8 	;
	mov	di,offset volname	;
	repz	movsb			;

getvl4: cmp	origdir+1,0		; Need to restore curdir?
	je	getvl9			;
	mov	dx,offset origdr	; Back to current dir
	mov	ah,chdir		;
	int	21h			;

getvl9: 				; Get disk free space
	mov	dl,parmdr		; Current drive letter
	sub	dl,64			;  as a number
	mov	ah,dskspc		; Get free space
	int	21h			;
	cmp	ax,0ffffh		; Valid?
	je	getvl10 		; no, skip it
	mul	cx			;  Bytes per cluster
	mul	bx			;  Total free
	mov	si,offset nrsize	; Point to msg
	call	format			;
getvl10:
	ret				;
getvol	endp				;
	page
;
;	Set search criteria

setarg	proc	near
set1:	mov	bp,offset dta		; First DTA
	mov	bx,offset search	; Search arument entries

	mov	ax,word ptr parmdr	; Set search drive
	lea	di,[bx].argdriv 	;
	stosw				;

;	parameter is possibly a filespec

set2:	cmp	byte ptr parmdir,'\'    ; path requested?
	je	set8			; yes, more than a filespec
	mov	cx,origptr		; no, set search path
	mov	si,offset origdr+2	;  from original path
	sub	cx,si			;
	jcxz	set2a			; In a subdir?
	rep	movsb			;
	mov	al,'\'                  ; Add filespec delimiter
	stosb				;

set2a:	mov	si,offset parmdir	; Copy filespec
	mov	cx,drptr		;  to search criteria
	sub	cx,si			;
	jcxz	set5			; None, append global filespec
	rep	movsb			;
	jmp	set7			; Done

;	parameter is possibly a path\filespec

set8:	mov	dx,offset parmdr	; Requested d:\path\filespec
	mov	ah,chdir		;
	int	21h			; Is parm a valid path name?
	jc	set4			;  no, have d:\path\filespec

set8a:	mov	dx,offset origdr	; Restore path
	mov	ah,chdir		;
	int	21h			;

	mov	si,offset parmdir	; Set search d:\path
	mov	cx,drptr		;  from command parameter
	sub	cx,si			;
	jcxz	set5			;
	rep	movsb			;
	jmp	set5			; Append global filespec

set4:	mov	si,offset parmdir	; Set search d:\path
	mov	cx,drptr		;  from command parameter
	sub	cx,si			;
set4a:	jcxz	set5			;
	rep	movsb			;
	jmp	set7			; Done

;	append global filespec to search criteria

set5:	mov	si,offset anyname	; Add global search arg
	cmp	byte ptr -1[di],'\'     ; Already have delimiter?
	jne	set6			;
	dec	di			; yes, overlay it

set6:	mov	cx,15			; Length of global filespec
	push	di			; Save current end pointer
	rep	movsb			;
	pop	di			; Restore work reg
	jmp	set9			;

set7:	mov	al,0			; Append ASCIIZ stopper
	stosb				;

set9:	lea	si,[bx].argdriv 	; Copy d:\path\filespec
	mov	cx,di			;
	sub	cx,si			;
	mov	di,offset titles	;  to titles
	rep	movsb			;
	mov	byte ptr [di],stopper	; Add print stopper

set10:	ret				; Back to caller

setarg	endp
	page
;
;	Obtain directory table

alloc	proc	near
	push	bx			; save registers
	mov	bx,pgmsize		; size of program module
	mov	ah,4ah			; modify memory
	int	21h			;
	mov	bx,-1			; ask for all remaining memory
alloc1:
	mov	ah,48h			; allocate memory
	int	21h			;
	jc	alloc1			; get what there is

	mov	segdir,ax		; segment addr of table
	mov	nxtdir,0		; offset to first entry

	shr	bx,1			; change number of paragraphs
	shr	bx,1			;  to 64-byte entries
	mov	maxdir,bx		; maximum table count
	pop	bx			; restore registers
	ret				;
alloc	endp

	page
;
;	Build table of directory entries

getdir	proc	near
	push	bp			; Ptr to DTA
	push	bx			; Ptr to search are

; Set DTA for current nesting level
	mov	dx,bp			; Data transfer area
	mov	ah,setdta		; Set local DTA
	int	21h

; Set search criteria for this level
	mov	dx,bx			; Search criteria
	sub	cx,cx			; Directory options
	mov	cl,dirmask
	mov	ah,4eh			; Find first matching entry
	int	21h

; Examine directory entry just returned
get1:	or	al,al
	jnz	gotdir			; Not found, quit looking.
	cmp	byte ptr [bp].dtaattr,10h
	jne	get3			; Is it a sub-dir?
	cmp	byte ptr [bp].dtaname,'.'
	je	get4			; May be <DIR> entry

	call	addfile 		; Add directory entry to table

; Build parms for sub-dir search
	lea	dx,[bp].dtaname 	; Save ptr to found name
	lea	si,[bx].argdriv 	; Point to current arg
	add	bp,dta_len		; Next DTA
	add	bx,arg_len		; Next search arg

; Copy previous arg as next search arg
	mov	cx,64			; Maximum length
	lea	di,[bx].argdriv 	; Point to new search arg
get6:	lodsb				;
	cmp	al,'?'                  ; Used global name?
	je	get9			;  yes, single nest
	cmp	al,0			; End of dir name?
	je	get5			;  yes, append wild cards
	stosb				;
	loop	get6			; Continue copying

; Add sub-dir name to search arg
get9:	mov	si,dx			; Saved ptr to found name
get8:	lodsb				;
	cmp	al,0			; End of DIR name?
	je	get5			;  yes, append wild cards
	stosb				;  no, add to arg
	loop	get8			; Continue copying fname

get5:	mov	si,offset anyname	; Append wild cards
	rep	movsb			;

	call	getdir			; Search the sub-dir
	sub	bx,arg_len		; restore arg
	sub	bp,dta_len		; and DTA

; Restore DTA to find next matching entry
	mov	dx,bp			; Data transfer area
	mov	ah,setdta		; Set DTA
	int	21h			;
	jmp	short get4		;

get3:	call	addfile 		; Add the entry

get4:	mov	cx,12			; Clear found name
	mov	al,' '                  ;
	lea	di,[bp].dtaname 	; Point to file name area
	rep	stosb			;

	mov	ah,4fh			; Search for next file
	mov	dx,bp			;
	int	21h			;
	jmp	get1			; Loop for next one

gotdir: pop	bx			; Restore arg
	pop	bp			;  and DTA
	ret				; Return to caller
getdir	endp				;
	page
;
;	Add a directory entry to table

addfile proc	near
	save	<cx,bp,di,si>		; Save registers

	mov	cx,tbl_len		; Initialize table entry
	mov	si,offset model 	;
	mov	di,offset pline 	;
	rep	movsb			;

	mov	al,[bp].dtaattr 	; Copy file attributes
	mov	pline.tblattr,al	;
	test	flags2,bymod		; Just modified files?
	jz	addfile1		;  no, add all
	test	al,10h			;  yes, pass subdirs
	jnz	addfile1		;
	test	al,20h			; is it modified tho?
	jnz	addfile1		; yes, add the entry
	jmp	addfile11		; no, exit

addfile1:
	call	getdate 		; Format date
	call	gettime 		;  time
	call	getsize 		;  bytes

	lea	si,[bp].dtaname 	; Copy file name
	lea	di,pline.tblname	;
	mov	cx,12			;
addfile2:
	lodsb				;
	cmp	al,0			;
	je	addfile5		;
	cmp	al,'.'                  ; separate extension
	je	addfile3		;
	stosb				;
	loop	addfile2		;
addfile3:
	jcxz	addfile5		;
	lea	di,pline.tblname+8	;
addfile4:
	stosb				;
	lodsb				;
	cmp	al,0			;
	je	addfile5		;
	loop	addfile4		;

addfile5:
	lea	di,pline.tblpath	; Copy path name
	lea	si,[bx].argname 	;
	mov	cx,size tblpath 	;
addfile6:
	cmp	byte ptr 1[si],'?'      ; Wildcard part?
	je	addfile7		; yes, have name
	lodsb				;
	stosb				;
	loop	addfile6		;

addfile7:
	lea	si,pline.tblname	;
	test	pline.tblattr,10h	; Subdirectory?
	jnz	addfile8		;  yes, copy path name
	jcxz	addfile10		;  no, pad with blanks
	mov	al,' '                  ;
	rep	stosb			;
	jmp	addfile10		;

addfile8:
	cmp	cl,12			; Max subdir name length
	jbe	addfile9		; to be copied
	mov	cl,12			;
addfile9:
	rep	movsb			;

addfile10:
	mov	cx,numdir		; Number of table entries
	cmp	cx,maxdir		; is table full?
	jae	addfile11		;  yes, skip it
	push	es			;  no, add to table
	mov	ax,word ptr segdir	; Segment addr of table
	add	ax,nxtdir		; plus next entry offset
	sub	di,di			;
	mov	si,offset pline 	; copy table stuff
	mov	cx,tbl_len		;
	mov	es,ax			; Set target segment
	rep	movsb			;
	pop	es			;

	inc	numdir			; Incr entry count
	add	nxtdir,tblpara		; Bump offset for next table entry

addfile11:
	return	<si,di,bp,cx>		; restore registers
addfile endp
	page
;
;	Print file information

print	proc	near
	cmp	numdir,1		; Just one file?
	ja	printt			;  no, two up heading
	mov	word ptr titled,0a0dh	;
	mov	titled+2,stopper	;

printt:
	mov	dx,offset titlea	; Top titles
	call	prints			;
	mov	dx,offset titleb	; Subdir name
	call	prints			;
	mov	dx,offset titlec	; Headings
	call	prints			;

	mov	ax,cs			; Set extra seg
	mov	es,ax			;  locally

	sub	ax,ax			; Offset to first table entry
	mov	nxtdir,ax		;  as current entry
	mov	ax,numdir		; Compute offset
	inc	ax			;  to second half
	shr	ax,1			;
	mov	cl,2			; Times 64 (4 paras each)
	shl	ax,cl			;
	mov	cx,numdir		; Number of entries
	or	cx,cx			; Even number of entries?
	jz	print7			; yes, all set
	inc	cx			; no, just one
	shr	cx,1			; Set half of count

print_next:
	call	print0			; Left side
	push	[nxtdir]		;
	add	nxtdir,ax		;
	call	print0			; Right side
	pop	[nxtdir]		;

	add	nxtdir,tblpara		; Point to next entry

	test	flags2,bywait		; Wait for screen full?
	jz	printw1 		;  no, continue
	inc	linecnt 		;  yes, bump line count
	mov	dl,_rows		; rows available on screen
	dec	dl			; leave room for headings
	cmp	linecnt,dl		; Full now?
	jb	printw1 		;  no, continue
	call	waitkey 		;  yes, get a key

printw1:
	loop	print_next		; continue for all entries
print7:
	ret				; done, return
print	endp				;


print0	proc	near
	save	<ax,cx,di>		; Save registers

	push	ds			; copy table entry to print line
	mov	cx,tbl_len		; length of table entry
	sub	si,si			; offset to next entry
	mov	di,offset pline 	; offset to print line
	mov	ax,word ptr segdir	; Segment addr for table
	add	ax,nxtdir		;  plus paras offset
	mov	ds,ax			;   as source segment
	rep	movsb			;    for copy
	pop	ds			;

	inc	count			; Number of files
	mov	ax,count		;
	cmp	ax,numdir		; Done em all?
	jbe	print1			; no, display this one
	dec	count			; yes,
	jmp	print9			;  done, return

print1:
	mov	cl,byte ptr pline.tblattr
	lea	di,byte ptr pline.tblfatr

	test	cl,32			; Archived?
	jnz	print2			;
	mov	al,'A'                  ;
	stosb				;

print2: test	cl,4			; System?
	jz	print3			;
	mov	al,'S'                  ;
	stosb				;

print3: test	cl,2			; Hidden?
	jz	print4			;
	mov	al,'H'                  ;
	stosb				;

print4: test	cl,1			; Read only?
	jz	print5			;
	mov	al,'R'                  ;
	stosb				;

print5: test	cl,10h			; Sub directory?
	jz	print5a 		; no
	lea	di,pline.tblfatr-1	; yes, special display
	mov	si,offset subdir	;
	mov	cx,4			;
	rep	movsb			;   for copying

print5a:
	test	flags2,bypath		; Doing all paths?
	jz	print6			;
	cmp	pline.tblpath+1,'?'     ; Nested entry?
	je	print6			;  no, as-is
	mov	pline.tblfatr-1,'-'     ;  yes, flag it in display

print6: lea	si,pline.tbldate	; Reformat date
	mov	di,offset olddate	;   for copying
	mov	cx,8			;
	rep	movsb			;

	lea	di,pline.tbldate	; Format date
	mov	ax,word ptr olddate+3	;
	stosw				;
	mov	al,"/"                  ;
	stosb				;
	mov	ax,word ptr olddate+6	;
	stosw				;
	mov	al,"/"                  ;
	stosb				;
	mov	ax,word ptr olddate	;
	stosw				;

	cmp	pline.tblext,' '        ; Any extension?
	jne	print8			;  yes, leave the dot
	mov	pline.tblext-1,' '      ;  no, rid it

print8: lea	dx,pline.tblname	;
	mov	byte ptr pline.tblctl,' '
	mov	byte ptr pline.tblctl+1,stopper
	mov	nrmsg+1,lf		;
	test	count,1 		; Right side?
	jnz	print8a 		;
	mov	nrmsg+1,cr		;
	mov	word ptr pline.tblctl,0a0dh
print8a:
	call	prints			; Display an entry

print9:
	return	<di,cx,ax>		; Restore registers
print0	endp

	page
;
;	Pause at end of screen for any key

waitkey proc	near
	save	<ax,bx,cx,dx>		; save work regs

	mov	linecnt,0		; reset counter
	mov	ah,2			; Set cursor position
	mov	dl,0			;  col 72
	mov	dh,_rows		;  last row
	add	dh,2			; adjust for heading
	sub	bx,bx
	int	10h

	mov	dx,offset more		; ask for more
	call	prints			;

	mov	ah,0			; wait for a key
	int	16h			;

	mov	dx,offset backsp	; backspace over 'more...'
	call	prints			;

	test	flags,byclear		; Clear screen each time?
	jz	waitkeyc		;  no
	call	cls			; Clear screen
waitkeyc:
	mov	dx,offset titlea	; Top titles
	call	prints			;
	mov	dx,offset titleb	; Subdir name
	call	prints			;
	mov	dx,offset titlec	; Headings
	call	prints			;

waitkeyx:
	return	<dx,cx,bx,ax>		; restore registers
waitkey endp
	page
;
;	Format the date

getdate proc	near			;Format the date
	mov	ax,word ptr [bp].dtadate
	mov	di,offset pline.tbldate
	or	ax,ax			;Is it zero?
	jz	gotdate
	push	ax			;Save date
	and	ax,mask yr		;Get year part
	mov	cl,yr			;Bits to shift
	call	cnvrt
	or	al,'8'                  ;Adjust for base year
	stosw
	mov	al,'-'
	stosb

	pop	ax			;Get the date back
	push	ax			;Save it
	and	ax,mask mo		;Get month part
	mov	cl,mo			;Bits to shift
	call	cnvrt2
	stosw
	mov	al,'/'
	stosb

	pop	ax			;Get the date back
	and	ax,mask dy		;Get day part
	mov	cl,dy			;Bits to shift
	call	cnvrt
	stosw
gotdate:ret
getdate endp

	page
;
;	Format the time

gettime proc	near			; Format the date
	mov	ax,word ptr [bp].dtatime;
	lea	di,pline.tbltime	;
	or	ax,ax			; It is zero?
	jz	gottime 		;
	push	ax			; Save date
	and	ax,mask hour		; Get hour part
	mov	cl,hour 		; Bits to shift
	shr	ax,cl			;
	call	cnvrt1			;
	stosw				;
	mov	al,':'                  ;
	stosb				;

gt3:	pop	ax			; Get the time back
	and	ax,mask min		; Get min part
	mov	cl,min			; Bits to shift
	call	cnvrt			;
	stosw				;
gottime:
	ret				;
gettime endp

cnvrt2	proc	near			; Convert to ASCII
	call	cnvrt			;
	cmp	al,'0'                  ; Suppress leading zero
	jne	cnvrtd			;
	mov	al,' '                  ;
	ret				;

cnvrt:	shr	ax,cl			;
cnvrt1: aam				; Make AL into BCD
	or	ax,'00'                 ; and to ASCII
	xchg	al,ah			;
cnvrtd: ret				;
cnvrt2	endp				;
	page
;
;	Format the size

getsize proc	near
	save	<bp,bx> 		; Ptr to Dta entry
	mov	ax,word ptr [bp].dtasize;
	add	numbyte+2,ax		;
	mov	dx,word ptr [bp].dtasize+2
	adc	numbyte,dx		;
	lea	si,pline.tblsize	; Target offset
	call	format			; Format double word
	return	<bx,bp> 		;
getsize endp

	page
;
;	Format ASCII numbers from binary

format	proc	near			; Formats a 32 bit integer in DX:AX
	save	<bp,bx,di,si>		; to DS:SI
	mov	ddptr,si		; addr of target field
	mov	di,dx			; subroutine uses di:si
	mov	si,ax
	call	printdd
	return	<si,di,bx,bp>

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
	sub	cl,cl
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
;
;	Print String like INT 21H function 9

prints	proc	near			; DX has offset to string
	save	<si,bx,cx>		;  ending in char x'FF'
	mov	si,dx			; Ptr to string text
	sub	cx,cx			; Overall text length
ps1:	lodsb
	cmp	al,stopper		; Ending hex FF?
	je	ps9
	inc	cx
	jmp	short ps1

ps9:
	mov	bx,1			; Standard output device
	mov	ah,40h			;  to write to
	int	21h

	return	<cx,bx,si>		; Recover registers
prints	endp


cls	proc	near			; Clear screen
	save	<ax,bx,cx,dx,si>

	mov	ax,600h 		; Scroll all lines
	sub	cx,cx			;  upper left
	mov	dx,184fh		;  lower right
	mov	bl,_page		;  video page
	mov	bh,_attr		;  attribute
	int	10h			; Video I/O

	mov	bl,_attr		; Set cursor position
	mov	bh,_page
	sub	dx,dx			;  to 1,1
	mov	ah,2
	int	10h

	return	<si,dx,cx,bx,ax>	; return to caller
cls	endp

	page
;
;	Format current date and time

clock	proc	near
	save	<ax,bx,cx,dx>		; save work regs

	mov	ah,2ah			;Get date
	int	21h
	sub	cx,1900 		; last two digits
	mov	ax,cx			;Make readable
	call	cnvrt1			;Convert to ASCII
	mov	word ptr year,ax
	xchg	al,dh			;Get month
	call	cnvrt1			;Convert to ASCII
	mov	word ptr month,ax
	xchg	al,dl			;Get day
	call	cnvrt1			;Convert to ASCII
	mov	word ptr day,ax

	mov	ah,2ch			;Get time
	int	21h
	xchg	al,ch			;Get hours
	call	cnvrt1			;Convert to ASCII
	mov	word ptr hours,ax
	xchg	al,cl			;Get minutes
	call	cnvrt1			;Convert to ASCII
	mov	word ptr mins,ax
	xchg	al,dh			;Get seconds
	call	cnvrt1			;Convert to ASCII
	mov	word ptr secs,ax

	return	<dx,cx,bx,ax>		; return to caller
clock	endp

	page
;
;	Shell-Metzger Sort of 64-byte table records

;	Variables used for sort subroutine

numrec	dw	0			; Number of entries
loc	dw	0
index1	dw	0
incr	dw	0
limit	dw	0
index2	dw	0
ptr1	dw	0			;Offset to record Index1
ptr2	dw	0			;Offset to record Index2

keyptr	dw	0			;Offset to key
keylen	dw	0			;Length of key
base	dw	0			;Seg addr of array

sort	proc	near
	push	ds			; Save seg regs
	push	es

;	Set sort options

	sub	bx,bx			; Offset to key
	mov	bl,offset tblpath
	test	flags,bysize
	jz	sort1
	mov	bl,offset tblsize	; Sort by size
sort1:	test	flags,bydate
	jz	sort2
	mov	bl,offset tbldate	; Sort by date/time
sort2:	test	flags,byext
	jz	sort3
	mov	bl,offset tblext

;	Initialize sort parameters

sort3:	mov	cx,numdir		; Number of entries
	mov	numrec,cx
	mov	keyptr,bx

	mov	dx,64			; Length of key
	sub	dx,bx
	mov	keylen,dx
	mov	es,segdir		; Seg addr of table
	mov	ax,es			; Save array addr
	sub	ax,4			;  adjust for indexing
	mov	base,ax

;	Sort 64-byte entries

	mov	loc,cx			; Loc=NumRecs

check:	cmp	loc,1			; IF Loc<=1 THEN
	jg	check1			; GOTO SORTED
	jmp	sorted

check1: mov	ax,loc
	sar	ax,1			; Loc=2*(Loc/4)+1
	or	ax,1
	mov	loc,ax

	mov	ax,numrec		; Limit=NumRec-Loc
	sub	ax,loc
	mov	limit,ax

	mov	incr,0			; Incr=0

again:	inc	incr			; Incr=Incr+1

	mov	ax,incr 		; IF Incr>Limit THEN GOTO CHECK
	cmp	ax,limit
	jg	check

	shl	ax,1
	shl	ax,1
	mov	index1,ax		; Index1=Incr

	mov	index2,ax		; Index2=Index1+Loc
	mov	ax,loc
	shl	ax,1			; times 2
	shl	ax,1			; times 4
	add	index2,ax

comp:	mov	ax,index1		; IF array(Index1)<=array(Index2)
	add	ax,base
	mov	es,ax
	mov	ptr1,ax
	mov	di,keyptr

	mov	ax,index2		; THEN GOTO AGAIN
	add	ax,base
	mov	ptr2,ax
	mov	si,keyptr
	mov	cx,cs:keylen

	push	ds
	mov	ds,ax
	repe	cmpsb
	pop	ds
	jae	again

swap:	mov	bx,ptr1 		; ELSE
	mov	dx,ptr2 		; TEMP=array(Index1)

	mov	ax,cs
	mov	es,ax
	mov	di,offset temp
	mov	cx,tbl_len

	mov	ds,bx
	sub	si,si
	rep	movsb

	mov	es,bx			; array(Index1)=array(Index2)
	mov	ds,dx
	sub	di,di
	sub	si,si
	mov	cx,tbl_len
	rep	movsb

	mov	ax,cs			; array(Index2)=TEMP
	mov	ds,ax
	mov	si,offset temp
	mov	es,dx
	sub	di,di
	mov	cx,tbl_len
	rep	movsb

	mov	ax,index1		; Index2=Index1
	mov	index2,ax

	mov	ax,loc			; Index1=Index1-Loc
	shl	ax,1
	shl	ax,1
	sub	index1,ax

	jg	comp			; IF Index1>0 then GOTO COMP
	jmp	again			; ELSE GOTO AGAIN

sorted: pop	es			;Recover register
	pop	ds
	ret
sort	endp

	page
;
;	Usage information, display panel

help	db	cr,lf,tab,tab,' -- LDIR Version 4.1 --- 25 Jan 89 --'
	db	cr,lf,tab,tab,'  (c) Copyright Vernon D. Buerg 1986-89'
	db	cr,lf
	db	cr,lf,tab,tab,tab,' Command syntax:'
	db	cr,lf
	db	cr,lf,tab,tab,'LDIR [d:][\path[fname[.ext]]] /?.../?'
	db	cr,lf,tab,tab
	db	cr,lf,tab,tab,'    /A   include Attributes'
	db	cr,lf,tab,tab,'    /C   Clear screen first'
	db	cr,lf,tab,tab,'    /D   sort by Date'
;	Db	CR,LF,TAB,TAB,'    /F   sort by Filename (default)'
	db	cr,lf,tab,tab,'    /H   include Hidden files'
	db	cr,lf,tab,tab,'    /M   only Modified files'
	db	cr,lf,tab,tab,'    /N   No sorting'
	db	cr,lf,tab,tab,'    /P   include all Paths'
	db	cr,lf,tab,tab,'    /S   sort by Size'
	db	cr,lf,tab,tab,'    /W   Wait after screen full'
	db	cr,lf,tab,tab,'    /X   sort by eXtension'
	db	stopper
;	Db	CR,LF,TAB,TAB,'    /?   display usage syntax',Stopper


;
;	Data structures and work areas


parmdr		db	' :'                            ; Drive letter
parmdir 	equ	$				; for specific path

pline		equ	parmdir+64			; Print line

dta		equ	pline+tbl_len			; Disk transfer areas

search		equ	dta + (depth+1)*dta_len 	; Search arguments

local_stack	equ	search + (depth+1)*arg_len	; Local stack
local_stack_end equ	local_stack+512

workend 	equ	local_stack_end + 2		; End of work areas

pgmsize 	equ	(workend - cseg + 512) /16	; Size of program

cseg		ends
		end	ldir
