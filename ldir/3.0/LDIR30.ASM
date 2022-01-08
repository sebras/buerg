	Page	80,132
	Title	--- LDIR - List	DIRectory - Version 3.0	---

	;    List Entire Directory

DtaNtry	Struc				;File entry
DtaRsvd	Db	21 Dup (0)		; reserved
DtaAttr	Db	0			; attribute
DtaTime	Dw	0			; update time
DtaDate	Dw	0			; update date
DtaSize	Dw	0,0			; size bytes (lo,hi)
DtaName	Db	12 Dup (' ')		; name and ext
	Db	0,13,10,255		; stopper and print
DtaNtry	Ends

ArgNtry	Struc				;Search	arguments
ArgDriv	Db	0,':'			; drive
ArgPath	Db	'\'			; path delimiter
ArgName	Db	64 Dup (0),255		; path,file,ext
ArgNtry	Ends

TblNtry	Struc				;Table Entries
TblAttr	Db	0			; attribute
TblPath	Db	21 Dup (0)		; path name(s)
TblName	Db	8 Dup (' ')		; file name
TblDot	Db	' '			; delimiter
TblExt	Db	3 Dup (' ')		; extension
TblSize	Db	' 0000000 '		;File size
TblDate	Db	'80-01/01 '		;Date
TblTime	Db	' 0:00 '		;Time
TblFatr	Db	3 Dup (' ')		;File attributes
TblCtl	Db	13,10,255
TblNtry	Ends


Cseg	Segment	Public Para 'CODE'
	Assume	CS:Cseg,DS:Cseg,ES:Cseg
	Org	100h
Ldir	Proc	Far
	Mov	Stackx,SP		;Save stack ptr	for exiting
	Jmp	Start
	Page
;
;	Data Areas, Constants, Etc.

Dta_Len	Equ	Size DtaNtry		;DTA length
Arg_Len	Equ	Size ArgNtry		;Argument length
Tbl_Len	Equ	Size TblNtry		;Disk record entry

Depth	Equ	3			;Maximum sub-DIR nest level
TAB	Equ	9
LF	Equ	10
CR	Equ	13
Stopper	Equ	255			;Ends print strings

CURDSK	Equ	19h			;Get current disk
SETDTA	Equ	1Ah			;Set data transfer area
DSKSPC	Equ	36h			;Get disk free space
CHDIR	Equ	3Bh			;Change	directory
WRITE	Equ	40h			;Write to a file handle
GETPATH	Equ	47h			;Get current directory

Stackx	Dw	0			;Entry stack pointer
DirMask	Db	0			;Directory flags mask
Errlvl	Db	0			;DOS return code
_Attr	Db	7			;Clear attribute
_Page	Db	0			;Video page

Flags	Db	ByName			;Command switches
 ByAttr	 Equ	1			;-attributes included
 ByHide	 Equ	2			;-want hidden files
 ByClear Equ	4			;-clear	screen
 ByDate	 Equ	8			;-sort by date/time
 ByExt	 Equ	10h			;-sort by extension
 ByName	 Equ	40h			;-sort by name
 BySize	 Equ	80h			;-sort by size

Flags2	Db	0			;More switches
 ByMod	 Equ	01h			;-modified files only
 ByWait	 Equ	02h			;-wait when screen full
 ByBrief Equ	4			;-four up
 ByPath	 Equ	20h			;-all paths

Date	Record	Yr:7,Mo:4,Dy:5		;Packed	date
Time	Record	Hour:5,Min:6,Sec:5	;Packed	time

AnyName	Db	'\????????.???',0,Stopper ;Global filename.ext
Blanks	Db	22 Dup (' ')
Subdir	Db	'-Dir'

Count	Dw	0			;Number	of files
NumDir	Dw	0			;Number	of table entries
MaxDir	Dw	0			;Maximum table entries
NxtDir	Dw	0			;Offset	to next	entry
PtrDir	Dw	0			;Offset	to first entry
SegDir	Dw	0			;Seg addr of table
NumByte	Dw	0,0			;Total bytes used
Linecnt	Db	0			;Line counter for /W

NumRec	Dw	0			;Number	of entries
Loc	Dw	0
Index1	Dw	0
Incr	Dw	0
Limit	Dw	0
Index2	Dw	0
Ptr1	Dw	0			;Offset	to record Index1
Ptr2	Dw	0			;Offset	to record Index2

KeyPtr	Dw	0			;Offset	to key
KeyLen	Dw	0			;Length	of key
Base	Dw	0			;Seg addr of array
	Page
;
;	Headings and titles

Titlea	Db	'List DIRectory            Volume: '
VolName	Db	11 Dup (' '),11	Dup (' ')
Month	Db	'mm/'
Day	Db	'dd/'
Year	Db	'yy '
Hours	Db	'hh:'
Mins	Db	'mm:'
Secs	Db	'ss',CR,LF,Stopper

More	Db	'... more',Stopper

Titleb	Db	TAB,TAB,TAB,TAB,'  '	;Command parameters
Titles	Db	64 Dup (0),Stopper	;Current directory

Titlec	Db	CR,LF,'Filename Ext   Bytes  -Last Change-     '
Titled	Db	'Filename Ext   Bytes  -Last Change-'
Newline	Db	Cr,Lf,Stopper
NrMsg	Db	Cr,Cr,2	Dup (' ')	;Ending	message
NrBytes	Db	'       0 bytes in'
NrFiles	Db	'       0 File(s);  '
NrSize	Db	'       0 bytes free.',Stopper
	Page

ExtFCB	Db	255,0,0,0,0,0		;Extended FCB to get label
	Db	8			;Attribute
DriveNr	Db	0,11 Dup('?')		;Drive number
	Db	2 Dup(0)		;Current block number
	Db	3 Dup(0)		;Logical record	size
	Db	20 Dup(0)		;File size

ParmDr	Db	' :'			;Drive letter
ParmDir	Db	64 Dup (0)		; for specific path

Temp	Db	0			;Sort exchange area
OrigDr	Db	'x:'			;Original drive
OrigDir	Db	'\',63 Dup (0)		; and path
OrigPtr	Dw	OrigDir			;End of	orig path name

RootDir	Db	'x:\',0			;To get	vol label
OldDate	Db	8 Dup (0)
DrPtr	Dw	Offset ParmDr
Model	TblNtry	<>			;Model print line
	Page
;
;	Set default drive and path

Start:
	Mov	AH,8			;Get monitor stuff
	Int	10h
	Mov	_Page,0
	Mov	_Attr,AH

	Call	Switchs			; Get program options

	Mov	AH,13			; Reset	diskettes
	Int	21h

	Mov	AH,CURDSK		; Get current disk
	Int	21h
	Add	AL,'A'
	Mov	OrigDr,AL		; Save original	drive letter
	Mov	RootDir,AL		;  for reading vol label
	Mov	ParmDr,AL

	Mov	DX,Offset DTA		; Set Data Transfer Area
	Mov	AH,SETDTA
	Int	21h

	Mov	CX,Offset Table		; Clear	work areas
	Mov	DI,Offset Entry
	Sub	CX,DI
	Mov	AL,0
	Rep	Stosb

	Call	GetParm			; Get desired dr:path

	Call	GetVol			; Get volume name

	Call	SetArg			; Set search argument

	Call	Alloc			; Allocate table for directory

	Call	Clock			; Date/time to heading

	Call	GetDir			; Read the directory

	Test	Flags,255		; Any sort options?
	Jz	NoSort			; no, display fifo dir
	Call	Sort			; Sort directory table

NoSort:
	Call	Print			; Display the entries

	Mov	AX,Count		; Number of files
	Sub	DX,DX
	Mov	SI,Offset NrFiles
	Call	Format

	Mov	DX,NumByte		; Total	bytes used
	Mov	AX,NumByte+2
	Mov	SI,Offset NrBytes
	Call	Format

	Mov	DX,Offset NrMsg

Exit:	Mov	SP,Stackx		;Insure	exiting	stack
	Call	PrintS			;Display final message

Done:	Mov	AL,Errlvl		;Return	to system
	Mov	AH,4Ch			; via EXIT
	Int	21h

Ldir	Endp

	Page
;
;	Set options from command line

Switchs	Proc	Near
	Mov	SI,82h			; Command tail
	Mov	DH,Flags		; Default switches
	Mov	DL,Flags2
	Sub	CX,CX
	Or	CL,Byte	Ptr -2[SI]	; test parm length
	Jz	Switch_Exit		; none,	return as-is

Sw1:	Lodsb				; Scan for switch
	Cmp	AL,'/'
	Loopne	Sw1
	Or	CX,CX			; found	one?
	Jz	Switch_Exit
	Mov	Byte Ptr -1[SI],CR	; Stop string here
	Jmp	Short Sw2a

Switch_Exit:
	Mov	Flags,DH		; Store	new switches
	Mov	Flags2,DL

	Mov	AL,DirMask		; Current directory attribute mask
	Test	Flags,ByHide		;  include hidden files
	Jz	Swx1
	Or	AL,2
Swx1:	Test	Flags,ByAttr		;  include display of attributes?
	Jz	Swx2
	Or	AL,7
Swx2:	Test	Flags2,ByPath		;  include sub-directories?
	Jz	Swx3
	Or	AL,16
Swx3:	Mov	Byte Ptr DirMask,AL	; Update dir search criteria
	Ret

Sw2:	Lodsb
	Cmp	AL,'/'			; Another switch?
	Loopne	Sw2
	Jcxz	Switch_Exit

Sw2a:	Lodsb				; yes, get letter following
	Dec	CX
	Jle	Sw3			; missing switch

Sw3:	Cmp	AL,'?'			; Help?
	Jne	Sw4
	Mov	DX,Offset Help
	Jmp	Exit

Sw4:	And	AL,0DFh			; Make option uppercase
	Cmp	AL,'A'			; Attributes?
	Jne	Sw5
	Or	DH,ByAttr
Sw5:	Cmp	AL,'B'			; Brief?
	Jne	Sw6
	Or	DL,ByBrief
Sw6:	Cmp	AL,'C'			; Clear?
	Jne	Sw7
	Or	DH,ByClear
	Call	Cls
Sw7:	Cmp	AL,'D'			; Date?
	Jne	Sw8
	Or	DH,ByDate
Sw8:	Cmp	AL,'X'			; Ext?
	Jne	Sw9
	Or	DH,ByExt
Sw9:	Cmp	AL,'P'			; Paths?
	Jne	Sw10
	Or	DL,ByPath
Sw10:	Cmp	AL,'S'			; Size?
	Jne	Sw11
	Or	DH,BySize
Sw11:	Cmp	AL,'H'			; Hidden?
	Jne	Sw12
	Or	DH,ByHide
Sw12:	Cmp	AL,'M'			; Modified only
	Jne	Sw12b
	Or	DL,ByMod
Sw12b:	Cmp	AL,'W'			; Wait when screen fills?
	Jne	Sw12c
	Or	DL,ByWait
Sw12c:	Cmp	AL,'F'			; Sort by filename?
	Jne	Sw12d
	Or	DH,ByName
Sw12d:	Cmp	AL,'N'			; No sorting?
	Jne	Sw13
	And	DH,0FFh-ByName-ByExt-BySize-ByDate

Sw13:	Jmp	Sw2			; Try for another option

Switchs	Endp
	Page
;
;	Copy command parameters

GetParm	Proc	Near
	Mov	SI,82h			;Command tail
	Mov	DI,Offset ParmDir	; goes after d:\
	Sub	CX,CX
	Or	CL,Byte	Ptr -2[SI]	; any parmeters?
	Jz	Parm9			; no, use defaults

Parm0:	Cmp	Byte Ptr 1[SI],':'	;Drive specified?
	Jne	Parm1
	Mov	DI,Offset ParmDr

Parm1:	Lodsb				;Skip leading blanks
	Cmp	AL,' '
	Jne	Parm3
	Loope	Parm1
	Jcxz	Parm9
Parm2:	Lodsb				;Copy d:\path\fname.ext
Parm3:	Cmp	AL,CR			; end of string?
	Je	Parm9
	Cmp	AL,' '			; end of operand?
	Jbe	Parm9
	Cmp	AL,','
	Je	Parm9
	Stosb
	Loop	Parm2

Parm9:	And	ParmDr,0DFh		;Upper case drive parm
	Mov	DrPtr,DI		;Save ptr to parm end
	Mov	AL,ParmDr
	Mov	OrigDr,AL
	Mov	RootDir,AL
	Ret
GetParm	Endp
	Page
;
;	Get volume label and disk free space

GetVol	Proc	Near
	Mov	DL,ParmDr		; Get drive letter
	Sub	DL,64			; and make it a	number
	Mov	DriveNr,DL
	Mov	SI,Offset OrigDir+1	; Save current path name
	Mov	AH,GETPATH
	Int	21h

	Mov	AL,0			; Get end of path name
	Mov	DI,Offset OrigDir
	Mov	CX,67
	Repne	Scasb
	Sub	DI,2
	Mov	OrigPtr,DI

	Cmp	OrigDir+1,0		; Already in root?
	Je	Getvl3			; yes, no chdir	needed
	Inc	OrigPtr
	Mov	DX,Offset RootDir	; no, point to root directory
	Mov	AH,CHDIR
	Int	21h
	Jc	Getvl9

Getvl3:	Mov	DX,Offset ExtFCB	;Search	for volume entry
	Mov	AH,11h
	Int	21h

	Or	AL,AL			;Any found?
	Jnz	Getvl4			; no, tough
	Mov	CX,11			; yes, copy it to heading
	Mov	SI,Offset DTA+8
	Mov	DI,Offset VolName
	Repz	Movsb

Getvl4:	Cmp	OrigDir+1,0		; Need to restore curdir?
	Je	Getvl9
	Mov	DX,Offset OrigDr	; Back to current dir
	Mov	AH,CHDIR
	Int	21h

Getvl9:				; Get disk free	space
	Mov	DL,ParmDr		; Current drive	letter
	Sub	DL,64			;  as a	number
	Mov	AH,DSKSPC		; Get free space
	Int	21h
	Cmp	AX,0FFFFh		; Valid?
	Je	Getvl10			; no, skip it
	Mul	CX			;  Bytes per cluster
	Mul	BX			;  Total free
	Mov	SI,Offset NrSize	; Point	to msg
	Call	Format
Getvl10:
	Ret
Getvol	Endp

	Page
;
;	Set search criteria

SetArg	Proc	Near
Set1:	Mov	BP,Offset DTA		;First DTA
	Mov	BX,Offset Search	;Search	arument	entries

	Mov	AX,Word	Ptr ParmDr	;Set search drive
	Lea	DI,[BX].ArgDriv
	Stosw
	Mov	CX,OrigPtr		;Set search path
	Mov	SI,Offset OrigDr+2	; from original	path
	Sub	CX,SI

Set2:	Cmp	ParmDir,0		;Is parm a path	or filespec
	Je	Set4a			; none,	append global to orig
	Mov	DX,Offset ParmDr
	Mov	AH,CHDIR
	Int	21h			;Is parm a valid path name?
	Jnc	Set3			; yes, leave criteria alone

	Jcxz	Set2a
	Rep	Movsb
Set2a:	Mov	SI,Offset ParmDir	; no, add filespec as criteria
	Mov	CX,DrPtr
	Sub	CX,SI
	Rep	Movsb
	Push	DI
	Jmp	Short Set7

Set3:	Mov	DX,Offset OrigDr	;Restore path
	Mov	AH,CHDIR
	Int	21h

Set4:	Mov	SI,Offset ParmDir	;Add parm path
	Mov	CX,DrPtr
	Sub	CX,SI
Set4a:	Jcxz	Set5
	Rep	Movsb

Set5:	Mov	SI,Offset AnyName	;Add global search arg
	Cmp	Byte Ptr -1[DI],'\'	;Already have delimiter?
	Jne	Set6
	Dec	DI			; yes, overlay it
Set6:	Mov	CX,15
	Push	DI
	Rep	Movsb
Set7:	Pop	CX
	Lea	SI,[BX].ArgDriv
	Sub	CX,SI
	Mov	DI,Offset Titles
	Rep	Movsb
	Mov	Byte Ptr [DI],Stopper

Set10:	Ret
SetArg	Endp
	Page
;
;	Obtain directory table

Alloc	Proc	Near
	Mov	DX,SP			; Upper	segment	limit
	Sub	DX,128			; less stack size
	And	DX,0FFF0h		; to paragraph boundary
	Mov	AX,Offset Table		; lower	memory limit
	And	AX,0FFF0h		; to paragraph boundary
	Add	AX,16
	Mov	NxtDir,AX		; as table address
	Mov	PtrDir,AX
	Sub	DX,AX			; to bytes available
	Mov	CL,6			; into 64-byte entries
	Shr	DX,CL			; to hold directory data
	Mov	MaxDir,DX
	Mov	CL,4			;Convert table offset
	Shr	AX,CL			; to a segment address
	Mov	CX,CS
	Add	CX,AX
	Mov	SegDir,CX
	Ret
Alloc	Endp
	Page
;
;	Build table of directory entries

GetDir	Proc	Near
	Push	BP			;Ptr to	DTA
	Push	BX			;Ptr to	search are

; Set DTA for current nesting level
	Mov	DX,BP			;Data transfer area
	Mov	AH,SETDTA		;Set DTA
	Int	21h

; Set search criteria for this level
	Mov	DX,BX			;Search	criteria
	Sub	CX,CX			;Directory options
	Mov	CL,DirMask
	Mov	AH,4Eh			;Find first matching entry
	Int	21h

; Examine directory entry just returned
Get1:	Or	AL,AL
	Jnz	GotDir			;Not found, quit looking.
	Cmp	Byte Ptr [BP].DtaAttr,10h
	Jne	Get3			;Is it a sub-dir?
	Cmp	Byte Ptr [BP].DtaName,'.'
	Je	Get4			;May be	<DIR> entry

	Call	Writer

; Build	parms for sub-dir search
	Lea	DX,[BP].DtaName		;Save ptr to found name
	Lea	SI,[BX].ArgDriv		;Point to current arg
	Add	BP,Dta_Len		;Next DTA
	Add	BX,Arg_Len		;Next search arg

; Copy previous	arg as next search arg
	Mov	CX,64			;Maximum length
	Lea	DI,[BX].ArgDriv		;Point to new search arg
Get6:	Lodsb
	Cmp	AL,'?'			;Used global name?
	Je	Get9			; yes, single nest
	Cmp	AL,0			;End of	dir name?
	Je	Get5			; yes, append wild cards
	Stosb
	Loop	Get6			;Continue copying

; Add sub-dir name to search arg
Get9:	Mov	SI,DX			;Saved ptr to found name
Get8:	Lodsb
	Cmp	AL,0			;End of	DIR name?
	Je	Get5			; yes, append wild cards
	Stosb				; no, add to arg
	Loop	Get8			;Continue copying fname

Get5:	Mov	SI,Offset AnyName	;Append	wild cards
	Rep	Movsb

	Call	GetDir			;Search	the sub-dir
	Sub	BX,Arg_Len		; restore arg
	Sub	BP,Dta_Len		; and DTA

; Restore DTA to find next matching entry
	Mov	DX,BP			;Data transfer area
	Mov	AH,SETDTA		;Set DTA
	Int	21h
	Jmp	Short Get4

Get3:	Call	Writer			;Add the entry

Get4:	Mov	CX,12			;Clear found name
	Mov	SI,Offset Blanks
	Lea	DI,[BP].DtaName		;Point to file name area
	Rep	Movsb

	Mov	AH,4Fh			;Search	for next file
	Mov	DX,BP
	Int	21h
	Jmp	Get1			;Loop for next one

GotDir:	Pop	BX			;Restore arg
	Pop	BP			; and DTA
	Ret
GetDir	Endp
	Page
;
;	Add directory entry to table

Writer	Proc	Near
	Push	CX
	Push	BP
	Push	DI
	Push	SI

	Mov	CX,Tbl_Len		;Initialize table entry
	Mov	SI,Offset Model
	Mov	DI,Offset Entry
	Rep	Movsb

	Mov	AL,[BP].DtaAttr		;Copy file attributes
	Mov	Entry.TblAttr,AL
	Test	Flags2,ByMod		;Just modified files?
	Jz	Writer0			; no, add all
	Test	AL,10h			; yes, pass subdirs
	Jnz	Writer0
	Test	AL,20h			; is it	modified tho?
	Jnz	Writer0			; yes, add the entry
	Jmp	Write1			; no, exit

Writer0:
	Call	GetDate			;Format	date
	Call	GetTime			; time
	Call	GetSize			; bytes

	Lea	SI,[BP].DtaName		;Copy file name
	Lea	DI,Entry.TblName
	Mov	CX,12
Writea:	Lodsb
	Cmp	AL,0
	Je	Writec
	Cmp	AL,'.'			; separate extension
	Je	Writeb
	Stosb
	Loop	Writea
Writeb:	Jcxz	Writec
	Lea	DI,Entry.TblName+8
Writed:	Stosb
	Lodsb
	Cmp	AL,0
	Je	Writec
	Loop	Writed

Writec:	Lea	DI,Entry.TblPath	;Copy path name
	Lea	SI,[BX].ArgName
	Mov	CX,Size	TblPath
Writc1:	Cmp	Byte Ptr 1[SI],'?'	; Wildcard part?
	Je	Writc2			; yes, have name
	Lodsb
	Stosb
	Loop	Writc1

Writc2:
	Lea	SI,Entry.TblName
	Test	Entry.TblAttr,10h	;Subdirectory?
	Jnz	Writc3			; yes, copy path name
	Jcxz	Writee			; no, pad with blanks
	Mov	SI,Offset Blanks
	Rep	Movsb
	Jmp	Writee

Writc3:	Cmp	CL,12			; Max subdir name length
	Jbe	Writc4			; to be	copied
	Mov	CL,12
Writc4:	Rep	Movsb

Writee:	Mov	CX,NumDir		;Number	of table entries
	Cmp	CX,MaxDir		; is table full?
	Jae	Write1			; yes, skip it
	Mov	DI,NxtDir		;Offset	to next	table entry
	Mov	SI,Offset Entry		; copy table stuff
	Mov	CX,Tbl_Len
	Rep	Movsb
	Inc	NumDir			;Incr entry count
	Add	NxtDir,Tbl_Len		; and next ptr

Write1:	Pop	SI
	Pop	DI
	Pop	BP
	Pop	CX
	Ret
Writer	Endp
	Page
;
;	Print file information

Print	Proc	Near
	Cmp	NumDir,1		;Just one file?
	Ja	PrintT			; no, two up heading
	Mov	Word Ptr Titled,0A0Dh
	Mov	Titled+2,Stopper
PrintT:	Mov	DX,Offset Titlea	;Top titles
	Call	PrintS
	Mov	DX,Offset Titleb	;Subdir	name
	Call	PrintS
	Mov	DX,Offset Titlec	;Headings
	Call	PrintS

	Mov	AX,CS			;Set extra seg
	Mov	ES,AX
	Mov	AX,PtrDir		;Offset	to table
	Mov	NxtDir,AX		; as current entry
	Mov	AX,NumDir		;Compute offset
	Inc	AX			; to second half
	Shr	AX,1
	Mov	CL,6
	Shl	AX,CL
	Mov	CX,NumDir		;Number	of entries
	Or	CX,CX
	Jz	Print7
	Inc	CX			; in each half
	Shr	CX,1

Print_Next:
	Call	Print0			;Left side
	Push	[NxtDir]
	Add	NxtDir,AX
	Call	Print0			;Right side
	Pop	[NxtDir]
	Add	NxtDir,Tbl_Len		; point	to next	entry

	Test	Flags2,ByWait		;Wait for screen full?
	Jz	PrintW1
	Inc	Linecnt			; yes, bump line count
	Cmp	Linecnt,20		;Full now?
	Jbe	PrintW1			; no, continue
	Call	Waitkey
PrintW1:
	Loop	Print_Next

Print7:	Ret
Print	Endp

Print0	Proc	Near
	Push	AX
	Push	CX
	Push	DI
	Inc	Count			;Number	of files
	Mov	AX,Count
	Cmp	AX,NumDir		;Done em all?
	Jbe	Print1
	Dec	Count
	Jmp	Print9

Print1:
	Mov	BP,NxtDir		;Offset	to table entry
	Mov	CL,Byte	Ptr [BP].TblAttr
	Lea	DI,Byte	Ptr [BP].TblFatr
	Test	CL,32			;Archived?
	Jnz	Print2
	Mov	AL,'A'
	Stosb

Print2:	Test	CL,4			;System?
	Jz	Print3
	Mov	AL,'S'
	Stosb

Print3:	Test	CL,2			;Hidden?
	Jz	Print4
	Mov	AL,'H'
	Stosb

Print4:	Test	CL,1			;Read only?
	Jz	Print5
	Mov	AL,'R'
	Stosb

Print5:	Test	CL,10h			;Sub directory?
	Jz	Print5a
	Lea	DI,[BP].TblFatr-1	; yes, special display
	Mov	SI,Offset Subdir
	Mov	CX,4
	Rep	Movsb

Print5a:
	Test	Flags2,ByPath		;Doing all paths?
	Jz	Print6
	Cmp	[BP].TblPath+1,'?'	;Nested	entry?
	Je	Print6			; no, as-is
	Mov	[BP].TblFatr-1,'-'	; yes, flag it in display

Print6:	Lea	SI,[BP].TblDate		;Reformat date
	Mov	DI,Offset OldDate
	Mov	CX,8
	Rep	Movsb

	Lea	DI,[BP].TblDate
	Mov	AX,Word	Ptr OldDate+3
	Stosw
	Mov	AL,"/"
	Stosb
	Mov	AX,Word	Ptr OldDate+6
	Stosw
	Mov	AL,"/"
	Stosb
	Mov	AX,Word	Ptr OldDate
	Stosw

	Cmp	[BP].TblExt,' '		;Any extension?
	Jne	Print8			; yes, leave the dot
	Mov	[BP].TblExt-1,' '	; no, rid it

Print8:	Lea	DX,[BP].TblName
	Mov	Byte Ptr [BP].TblCtl,' '
	Mov	Byte Ptr [BP+1].TblCtl,Stopper
	Mov	NrMsg+1,Lf
	Test	Count,1			;Right side?
	Jnz	Print8a
	Mov	NrMsg+1,Cr
	Mov	Word Ptr [BP].TblCtl,0a0dh
Print8a:
	Call	PrintS			;Display an entry

Print9:	Pop	DI
	Pop	CX
	Pop	AX
	Ret
Print0	Endp

	Page
;
;	Pause at end of	screen for any key

Waitkey	Proc	Near
	Push	AX
	Push	BX
	Push	CX
	Push	DX

	Mov	Linecnt,0		; reset	counter
	Mov	AH,2
	Mov	DX,1847h
	Sub	BX,BX
	Int	10h

	Mov	DX,Offset More		; ask for more
	Call	PrintS

	Mov	AH,0			; wait for a key
	Int	16h

	Test	Flags,ByClear		; Clear	screen each time?
	Jnz	Waitkeyc
	Mov	DX,Offset Newline
	Call	PrintS
	Jmp	Waitkeyx

Waitkeyc:
	Call	Cls

	Mov	DX,Offset Titlea	;Top titles
	Call	PrintS
	Mov	DX,Offset Titleb	;Subdir	name
	Call	PrintS
	Mov	DX,Offset Titlec	;Headings
	Call	PrintS

Waitkeyx:
	Pop	DX
	Pop	CX
	Pop	BX
	Pop	AX
	Ret
Waitkey	Endp
	Page
;
;	Format the date

GetDate	Proc	Near			;Format	the date
	Mov	AX,Word	Ptr [BP].DtaDate
	Mov	DI,Offset Entry.TblDate
	Or	AX,AX			;Is it zero?
	Jz	GotDate
	Push	AX			;Save date
	And	AX,Mask	Yr		;Get year part
	Mov	CL,Yr			;Bits to shift
	Call	Cnvrt
	Or	AL,'8'			;Adjust	for base year
	Stosw
	Mov	AL,'-'
	Stosb

	Pop	AX			;Get the date back
	Push	AX			;Save it
	And	AX,Mask	Mo		;Get month part
	Mov	CL,Mo			;Bits to shift
	Call	Cnvrt2
	Stosw
	Mov	AL,'/'
	Stosb

	Pop	AX			;Get the date back
	And	AX,Mask	Dy		;Get day part
	Mov	CL,Dy			;Bits to shift
	Call	Cnvrt
	Stosw
GotDate:Ret
GetDate	Endp

;	Format the time

GetTime	Proc	Near			;Format	the date
	Mov	AX,Word	Ptr [BP].DtaTime
	Lea	DI,Entry.TblTime
	Or	AX,AX			;It is zero?
	Jz	GotTime
	Push	AX			;Save date
	And	AX,Mask	Hour		;Get hour part
	Mov	CL,Hour			;Bits to shift
	Shr	AX,CL
	Call	Cnvrt1
	Stosw
	Mov	AL,':'
	Stosb

GT3:	Pop	AX			;Get the time back
	And	AX,Mask	Min		;Get min part
	Mov	CL,Min			;Bits to shift
	Call	Cnvrt
	Stosw
GotTime:Ret
GetTime	Endp

Cnvrt2	Proc	Near			;Convert to ASCII
	Call	Cnvrt
	Cmp	AL,'0'			;Suppress leading zero
	Jne	Cnvrtd
	Mov	AL,' '
	Ret

Cnvrt:	Shr	AX,CL
Cnvrt1:	Aam				;Make AL into BCD
	Or	AX,'00'			; and to ASCII
	Xchg	AL,AH
Cnvrtd:	Ret
Cnvrt2	Endp
	Page
;
;	Format the size

GetSize	Proc	Near
	Push	BP			; Ptr to Dta entry
	Push	BX
	Mov	AX,Word	Ptr [BP].DtaSize
	Add	NumByte+2,AX
	Mov	DX,Word	Ptr [BP].DtaSize+2
	Adc	NumByte,DX
	Lea	SI,Entry.TblSize	;Target	offset
	Call	Format			;Format	double word
	Pop	BX
	Pop	BP
	Ret
GetSize	Endp

	Page
;
; Ripped from sdir.asm.	How does this work?

Ddptr	Dw	0

Format	Proc	Near	;Formats a 32 bit integer in DX:AX
	Push	BP	; to DS:SI
	Push	BX
	Push	DI
	Push	SI
	Mov	Ddptr,SI	;addr of target	field
	Mov	DI,DX		;routine uses di:si
	Mov	SI,AX
	Call	Printdd
	Pop	SI
	Pop	DI
	Pop	BX
	Pop	BP
	Ret

Printdd:
	Xor	AX,AX		;zero out the
	Mov	BX,AX		; working
	Mov	BP,AX		; registers.
	Mov	CX,32		;# bits	of precision
J1:	Shl	SI,1
	Rcl	DI,1
	Xchg	BP,AX
	Call	J6
	Xchg	BP,AX
	Xchg	BX,AX
	Call	J6
	Xchg	BX,AX
	Adc	AL,0
	Loop	J1
	Mov	CX,1710h
	Mov	AX,BX
	Call	J2
	Mov	AX,BP
J2:	Push	AX
	Mov	DL,AH
	Call	J3
	Pop	DX
J3:	Mov	DH,DL
	Shr	DL,1		;move high
	Shr	DL,1		; nibble to
	Shr	DL,1		; the low
	Shr	DL,1		; position.
	Call	J4
	Mov	DL,DH
J4:	And	DL,0fh		;mask low nibble
	Jz	J5		;if not	zero
	Sub	CL,CL
J5:	Dec	CH
	And	CL,CH
	Or	DL,'0'		;fold in ascii zero
	Sub	DL,CL
	Mov	BX,Ddptr
	Mov	[BX],DL		;ptr to	next target field
	Inc	Ddptr
	Ret

J6:	Adc	AL,AL
	Daa
	Xchg	AL,AH
	Adc	AL,AL
	Daa
	Xchg	AL,AH
	Ret


Format	Endp
	Page
;
;	Print String like INT 21H function 9

PrintS	Proc	Near			; DX has offset	to string
	Push	SI			;  ending in char x'FF'
	Push	BX
	Push	CX
	Mov	SI,DX			; Ptr to string	text
	Sub	CX,CX			; Overall text length
PS1:	Lodsb
	Cmp	AL,Stopper		; Ending hex FF?
	Je	PS9
	Inc	CX
	Jmp	Short PS1

PS9:
	Mov	BX,1			; Standard output device
	Mov	AH,40h			;  to write to
	Int	21h

	Pop	CX			; Recover registers
	Pop	BX
	Pop	SI
	Ret
PrintS	Endp


Cls	Proc	Near			; Clear	screen
	Push	AX
	Push	BX
	Push	CX
	Push	DX
	Push	SI

	Mov	AX,600h			; Scroll all lines
	Sub	CX,CX			;  upper left
	Mov	DX,184Fh		;  lower right
	Mov	BL,_Page		;  video page
	Mov	BH,_Attr		;  attribute
	Int	10h			; Video	I/O

	Mov	BL,_Attr		; Set cursor position
	Mov	BH,_Page
	Sub	DX,DX			;  to 1,1
	Mov	AH,2
	Int	10h

	Pop	SI
	Pop	DX
	Pop	CX
	Pop	BX
	Pop	AX
	Ret
Cls	Endp

	Page
;
;	Format current date and	time

Clock	Proc	Near
	Push	AX
	Push	BX
	Push	CX
	Push	DX

	Mov	AH,2Ah			;Get date
	Int	21h
	Sub	CX,1900			; last two digits
	Mov	AX,CX			;Make readable
	Call	Cnvrt1			;Convert to ASCII
	Mov	Word Ptr Year,AX
	Xchg	AL,DH			;Get month
	Call	Cnvrt1			;Convert to ASCII
	Mov	Word Ptr Month,AX
	Xchg	AL,DL			;Get day
	Call	Cnvrt1			;Convert to ASCII
	Mov	Word Ptr Day,AX

	Mov	AH,2Ch			;Get time
	Int	21h
	Xchg	AL,CH			;Get hours
	Call	Cnvrt1			;Convert to ASCII
	Mov	Word Ptr Hours,AX
	Xchg	AL,CL			;Get minutes
	Call	Cnvrt1			;Convert to ASCII
	Mov	Word Ptr Mins,AX
	Xchg	AL,DH			;Get seconds
	Call	Cnvrt1			;Convert to ASCII
	Mov	Word Ptr Secs,AX

	Pop	DX
	Pop	CX
	Pop	BX
	Pop	AX
	Ret
Clock	Endp
	Page
;
;	Shell-Metzger Sort of 64-byte table records

Sort	Proc	Near
	Push	DS			;Save seg regs
	Push	ES

;	Set sort options

	Sub	BX,BX			;Offset	to key
	Mov	BL,Offset TblPath
	Test	Flags,BySize
	Jz	Sort1
	Mov	BL,Offset TblSize	;Sort by size
Sort1:	Test	Flags,ByDate
	Jz	Sort2
	Mov	BL,Offset TblDate	;Sort by date/time
Sort2:	Test	Flags,ByExt
	Jz	Sort3
	Mov	BL,Offset TblExt

;	Initialize sort	parameters

Sort3:	Mov	CX,NumDir		;Number	of entries
	Mov	NumRec,CX
	Mov	KeyPtr,BX

	Mov	DX,64			;Length	of key
	Sub	DX,BX
	Mov	KeyLen,DX
	Mov	ES,SegDir		;Seg addr of table
	Mov	AX,ES			;Save array addr
	Sub	AX,4			; adjust for indexing
	Mov	Base,AX

;	Sort 64-byte entries

	Mov	Loc,CX			; Loc=NumRecs

Check:	Cmp	Loc,1			; IF Loc<=1 THEN
	Jg	Check1			; GOTO SORTED
	Jmp	Sorted

Check1:	Mov	AX,Loc
	Sar	AX,1			; Loc=2*(Loc/4)+1
	Or	AX,1
	Mov	Loc,AX

	Mov	AX,NumRec		; Limit=NumRec-Loc
	Sub	AX,Loc
	Mov	Limit,AX

	Mov	Incr,0			; Incr=0

Again:	Inc	Incr			; Incr=Incr+1

	Mov	AX,Incr			; IF Incr>Limit	THEN GOTO CHECK
	Cmp	AX,Limit
	Jg	Check

	Shl	AX,1
	Shl	AX,1
	Mov	Index1,AX		; Index1=Incr

	Mov	Index2,AX		; Index2=Index1+Loc
	Mov	AX,Loc
	Shl	AX,1			; times	2
	Shl	AX,1			; times	4
	Add	Index2,AX

Comp:	Mov	AX,Index1		; IF array(Index1)<=array(Index2)
	Add	AX,Base
	Mov	ES,AX
	Mov	Ptr1,AX
	Mov	DI,KeyPtr

	Mov	AX,Index2		; THEN GOTO AGAIN
	Add	AX,Base
	Mov	Ptr2,AX
	Mov	SI,KeyPtr
	Mov	CX,CS:KeyLen

	Push	DS
	Mov	DS,AX
	Repe	Cmpsb
	Pop	DS
	Jae	Again

Swap:	Mov	BX,Ptr1			; ELSE
	Mov	DX,Ptr2			; TEMP=array(Index1)

	Mov	AX,CS
	Mov	ES,AX
	Mov	DI,Offset Temp
	Mov	CX,Tbl_Len

	Mov	DS,BX
	Sub	SI,SI
	Rep	Movsb

	Mov	ES,BX			; array(Index1)=array(Index2)
	Mov	DS,DX
	Sub	DI,DI
	Sub	SI,SI
	Mov	CX,Tbl_Len
	Rep	Movsb

	Mov	AX,CS			; array(Index2)=TEMP
	Mov	DS,AX
	Mov	SI,Offset Temp
	Mov	ES,DX
	Sub	DI,DI
	Mov	CX,Tbl_Len
	Rep	Movsb

	Mov	AX,Index1		; Index2=Index1
	Mov	Index2,AX

	Mov	AX,Loc			; Index1=Index1-Loc
	Shl	AX,1
	Shl	AX,1
	Sub	Index1,AX

	Jg	Comp			; IF Index1>0 then GOTO	COMP
	Jmp	Again			; ELSE GOTO AGAIN

Sorted:	Pop	ES			;Recover register
	Pop	DS
	Ret
Sort	Endp
	Page
Help	Db	CR,LF,TAB,TAB,' -- LDIR Version 3.0 --- 4 June 86 --'
	Db	CR,LF,TAB,TAB,'  (c) Copyright Vernon D. Buerg 1986'
	Db	CR,LF
	Db	CR,LF,TAB,TAB,TAB,' Command syntax:'
	Db	CR,LF
	Db	CR,LF,TAB,TAB,'LDIR [d:][\path[fname[.ext]]] /?.../?'
	Db	CR,LF,TAB,TAB
	Db	CR,LF,TAB,TAB,'    /A   include Attributes'
	Db	CR,LF,TAB,TAB,'    /C   Clear screen first'
	Db	CR,LF,TAB,TAB,'    /D   sort by Date'
;	Db	CR,LF,TAB,TAB,'    /F   sort by Filename (default)'
	Db	CR,LF,TAB,TAB,'    /H   include Hidden files'
	Db	CR,LF,TAB,TAB,'    /M   only Modified files'
	Db	CR,LF,TAB,TAB,'    /N   No sorting'
	Db	CR,LF,TAB,TAB,'    /P   include all Paths'
	Db	CR,LF,TAB,TAB,'    /S   sort by Size'
	Db	CR,LF,TAB,TAB,'    /W   Wait after screen full'
	Db	CR,LF,TAB,TAB,'    /X   sort by eXtension'
	Db	Stopper
;	Db	CR,LF,TAB,TAB,'    /?   display usage syntax',Stopper

	Page
;
;	Data structures	and work areas

Entry	Equ	$			;Print line

DTA	Equ	Entry+Tbl_Len		;Disk transfer areas

Search	Equ	DTA + (Depth+1)*Dta_Len	;Search	arguments

Table	Equ	Search + (Depth+1)*Arg_Len

Cseg	Ends
	End	Ldir
