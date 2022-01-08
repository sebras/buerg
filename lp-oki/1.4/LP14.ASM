	Title	LP - Print File With Pagination
	Page	80,132
	Comment	|

LP Command
________________

Purpose:  To print an ASCII file on the standard printer
	  device at either 66 or 88 lines per page. A title
	  is printed at the top of each page which contains
	  the file name, creation date, and page number.

Syntax:	  LP [d][path]filename[.ext]	[/6][/8]
					[/L1][/L2]
					[/10][/12][/17]

Remarks:
	  Written by Vernon Buerg for the IBM PC using
	  DOS 2.0 or later. For public domain use. Not
	  for sale or hire.

	  Version 1.1, April 27, 1984.
	  Version 1.2, Sept 12, 1984.
	  Version 1.4, Aug 8, 1985.
		- account for TABs and long lines
		- remove Int 17h due to bad spoolers
________________							|

Cseg	Segment	Public Para 'CODE'
	Assume	CS:Cseg,DS:Cseg
	Org	100h

LP	Proc	Far
	Mov	SP,Offset CS:Lstack	;Use local stack

	Push	DS			;For DOS return
	Sub	AX,AX
	Push	AX
	Mov	Stk_Top,SP

	Call	Ver			; Check DOS version

	Call	Alloc			; Allocate memory

	Call	GetFile			; Get file name

	Call	Opens			; Open input

	Call	InitLPT			; Initialize printer

	Call	GetName			; Format title line

	Call	Titles			; and print it

	Call	List			; Print the file

	Call	Flush			; Drain the output buffer

Eod:	Mov	DX,Offset EofMsg	;Say END-OF-FILE
	Jmp	Fini

Error:	Mov	CS:Errlvl,1
Fini:	Mov	AX,CS			;Insure seg regs
	Mov	DS,AX
	Mov	SP,Stk_Top		; and stackck

	Mov	AH,9			;Print error message
	Int	21h

	Mov	BX,IHandle		;Close input
	Mov	AH,3Eh
	Int	21h

	Mov	BX,OHandle		; Close output
	Cmp	BX,4			;  if not standard output
	Je	Exit
	Mov	AH,3Eh
	Int	21h
Exit:
	Mov	AL,Errlvl		; Set ERROR LEVEL
	Mov	AH,4Ch			; and Exit
	Int	21h
	Page
;
;	Constants and Data Areas

BEL	Equ	07
BS	Equ	08
TAB	Equ	09
LF	Equ	10
FF	Equ	12
CR	Equ	13
EOF	Equ	1Ah
ESC	Equ	1Bh

Buflen	Dw	0			;I/O buffer size (variable)
Stk_Top	Dw	0			;Stack ptr at entry

Lcnt	Db	0			;Line counter
Cpp	Db	96			;Chars per page
LPP	Db	82			;Lines per page
LPTn	Dw	0			;Printer port
Errlvl	Db	0			;Error level returned
Ccnt	Db	0			;Chars in current line

MsgIn	Db	CR,LF,'Enter INPUT filename  $'
Msg1	Db	CR,LF,'Unable to open input'
InKey	Db	32,32			;Keyboard buffer
Input	Db	76 Dup (0),'$'		;Drive:path\name.ext
IHandle	Dw	0			;Input file handle
Ilen	Dw	0			;Input block length
Iptr	Dw	0			;Offset	to next	char
InPtr	Dw	0			;Offset to input buffer


Msg2	Db	CR,LF,'Unable to open LPT'
Msg2a	Db	'1$'
Output	Db	'LPT1:',0,'$'		;Printer name
OHandle	Dw	0			;Output file handle
Olen	Dw	0			;Output block length
Optr	Dw	0			;Offset	to next	char
OutPtr	Dw	0			;Offset to output buffer

OutChar	Db	0

AlocMsg	Db	CR,LF,'Not enough memory',CR,LF,BEL,'$'
ErrMsg	Db	CR,LF,'Invalid command option(s)',CR,LF,BEL,'$'
Version	Db	'LP - Version 1.4 - V.Buerg',CR,LF,'$'
Sorry	Db	'Sorry, PC DOS 2.0 or later required',CR,LF,BEL,'$'

Heading	Db	CR			;Top line title
FileNm	Db	43 Dup (' ')
Date	Db	'mm-dd-yy',9,9
	Db	'Page  '
Pageno	Db	'1',LF

EofMsg	Db	CR,LF
Len_H	Equ	This Byte - Heading
	Db	'End of File',CR,LF,'$'

Dater	Record	Yr:7,Mo:4,Dy:5

Reset	Db	CR			;Printer initialization codes
	Db	FF,ESC			;Form feed (no CPI setting)
Lpi	Db	56			;Lines per inch
Cpi	Db	28			;Chars per inch

Tabs	Db	ESC,TAB
	Db	'009,017,025,033,041,049,057,065,073'
Reset10 Equ	$-Reset+1
Tabs12	Db	',081,089'		; When using 12-cpi
Reset12 Equ	$-Reset+1
Tabs17	Db	',097,105,113,121,129',CR
Reset17	Equ	$-Reset

Reset_L	Dw	Reset12			; Length of initial string
	Page
;
;	Copy file to printer

List	Proc	Near

List1:	Call	Read			;Get one character
	And	AL,7FH			;Strip hi-order	bit

	Cmp	AL,FF			;Is it form feed?
	Je	Eject

	Cmp	AL,LF			;Pass line feed
	Je	Passit

	Cmp	AL,CR			;Pass carriage return
	Je	Passit

	Cmp	AL,BS			;Pass back space
	Je	PassBS

	Cmp	AL,TAB			;Pass tab chars
	Je	PassTAB
	Inc	Ccnt			;Incr count of chars in line

	Cmp	AL,EOF			;End of	file?
	Je	Done

	Cmp	AL,32			;Other control char?
	Jns	Passit
	Jmp	CtlChr

PassTAB:Add	Ccnt,8			;Round up to TAB column
	And	Ccnt,0F8h
	Jmp	Passit

PassBS:	Dec	Ccnt			;Account for backspace
	Jns	Passit
	Mov	Ccnt,0

Passit:	Call	PutChar
	Mov	AH,Cpp			;Max chars per line
	Cmp	Ccnt,AH			; filled up a line?
	Ja	Passit2
Passit1:
	Cmp	AL,LF			;Is it line feed?
	Jne	List1			; no, get next char
Passit2:
	Inc	Lcnt			; yes, incr line count
	Mov	Ccnt,0
	Mov	AL,Lcnt
	Cmp	AL,LPP			;End of	page?
	Jb	List1			; no, get next char

Eject:	Mov	Ccnt,0			;Reset char count in line
	Cmp	Lcnt,2			;Printed any lines yet?
	Jbe	List1			; no, ignore form feed
	Call	NewPage
	Jmp	List1			;Get next record

CtlChr:	Cmp	AL,0			;Null char?
	Je	Blanks			; yes, make it a space
	Push	AX
	Mov	AL,'^'			;Indicate a control char
	Call	PutChar
	Inc	Ccnt
	Pop	AX     			;Get char again
Blanks:	Add	AL,20H			;Make it printable
	Jmp	Passit

Done:	Ret
List	Endp
	Page
;
;	Process end of page

NewPage	Proc	Near
	Cmp	Lcnt,2			;Is it title line?
	Je	Titles			; yes, skip rest
	Mov	AL,CR
	Call	PutChar			; no, send CR
	Mov	AL,FF
	Call	PutChar			; and form feed
	Mov	Lcnt,0			;Reset line count

	Push	DI
	Mov	DI,Offset Pageno
	Mov	AX,3A30h
Next:	Inc	Byte Ptr [DI]		;Incr page number
	Cmp	[DI],AL			;End in	zero?
	Js	Set1			; yes, make it a one
	Cmp	[DI],AH			;Over nine?
	Jne	PgSet			; no, have good number
	Mov	[DI],AL			; yes, make last digit zero
	Dec	DI			; and incr hi-order
	Jmp	Next

Set1:	Mov	Byte Ptr [DI],'1'
PgSet:	Pop	DI

;
;	Print top line titles

Titles:	Mov	SI,Offset Heading	;Print title line
	Mov	CX,Len_H
Next1:	Lodsb
	Cmp	AL,0			;Replace nulls
	Jne	Next2
	Mov	AL,' '
Next2:	Call	PutChar
	Loop	Next1
	Mov	Lcnt,2			;Reset line counter
	Ret

;
;	Initialize the printer

InitLPT	Proc	Near			;Initialize the printer
Init1:	Mov	CX,Reset_L		;Length of
	Mov	SI,Offset Reset		; initial codes
Init2:	Call	Next1
	Ret
InitLPT	Endp

NewPage	Endp

	Page
;
;	Format title line

GetName	Proc	Near			;Format title line
	Mov	SI,Offset Input		;Copy file name
	Mov	DI,Offset Filenm	; to heading
	Mov	CX,42			;Max for title
	Cld
	Repz	Movsb

	Mov	AX,5700h		;Return file's date and time
	Mov	BX,IHandle		;Input handle
	Int	21h

	Mov	DI,Offset Date		;Date field in title

	Mov	AX,DX			;Get month part
	And	AX,Mask Mo
	Mov	CL,Mo
	Call	Format
	Stosw
	Inc	DI			;Add delimiter

	Mov	AX,DX			;Get day part
	And	AX,Mask Dy
	Mov	CL,Dy
	Call	Format
	Stosw
	Inc	DI			;Add delimiter

	Mov	AX,DX			;Get year part
	And	AX,Mask Yr
	Mov	CL,Yr
	Call	Format
	Or	AL,'8'
	Stosw
	Ret
GetName	Endp

Format	Proc	Near			;Convert binary to ASCII
	Shr	AX,CL
	Aam
	Or	AX,'00'
	Xchg	AH,AL
	Ret
Format	Endp
	Page
;
;	Extract one char from record

Read	Proc	Near			;Read char into	AL
Read1:	Cmp	Ilen,0			;Any in	buffer?
	Je	Read2			; no, read next	block
	Mov	SI,Iptr			; yes, get offset in buf
	Lodsb
	Inc	Iptr			;Offset	for next one
	Dec	Ilen			;Decr buffer size left
	Ret				; and return

Read2:	Mov	BX,IHandle		;Read input
	Mov	CX,BufLen
	Mov	DX,InPtr		;Set up	DS:DX
	Mov	AH,3Fh
	Int	21h			;Read a	block
	Mov	DX,InPtr
	Mov	Iptr,DX			;Reset buffer ptr
	Mov	Ilen,AX			; and length
	Jc	Read8
	Or	AX,AX			;Anything read?
	Jnz	Read1			; yes, pick it up
	Mov	AL,EOF			; no, return EOF
	Ret

Read8:	Mov	DX,Offset Msg3		;Say I/O ERROR
	Jmp	Error

Msg3	Db	CR,LF,'I/O error',CR,LF,BEL,'$'
Read	Endp

;
;	Buffer characters to printer

PutChar	Proc	Near			;Write from AL
	Mov	DI,Optr			; Spot for next outchar
	Stosb
	Mov	Optr,DI
	Dec	Olen			; Is it full now?
	Jz	PutCh0			; yes, print the lot
	Ret

Flush:	Mov	AX,Olen			; Bytes left in output buffer
	Sub	Buflen,AX		;  to get count in buffer
	Jnz	PutCh0
	Ret

PutCh0:	Push	AX
	Push	BX
	Push	CX
	Push	DX
PutCh1:	Mov	BX,OHandle		; Printer file handle
	Mov	CX,Buflen
	Mov	Olen,CX			; Reset size remaining in bufr
	Mov	DX,OutPtr
	Mov	Optr,DX			; Reset ptr for next put
	Mov	AH,40h			; Print entire buffer
	Int	21h
	Jc	PutChe			; Successful?
	Cmp	AX,CX 			; Wrote it all?
	Je	PutCh9
PutChe:	Mov	DX,Offset MsgPut	; Printer error
	Or	MsgPute,AL
	Jmp	Error

MsgPut	Db	'Printer error -- program terminated -- RC = '
MsgPute	Db	'0',CR,LF,BEL,'$'

PutCh9:	Pop	DX
	Pop	CX
	Pop	BX
	Pop	AX
	Ret
PutChar	Endp
	Page
;
;	Get file names from parm

GetFile	Proc	Near			;Get file name(s)
	Mov	SI,80h			;Point to command line
	Sub	CX,CX			;Clear length reg
	Or	CL,Byte	Ptr [SI]	;Get command tail length
	Jz	GetF8			; none, ask for them
	Mov	DI,Offset Input		;Point fname target
	Inc	SI			;Bump command ptr

GetF1:	Lodsb				;Get next char
	Cmp	AL,' '			;Skip leading blanks
	Jne	GetF2
	Loope	GetF1
	Jcxz	GetF8			; all blank

GetF2:	Cmp	AL,CR			;End of parm?
	Je	GetF7			; yes, terminate fname
	Cmp	AL,' '			;Delimiter?
	Je	GetF4			; yes, look for swithes
	Cmp	AL,'/'			;Switch char?
	Je	GetF5
	Stosb				;Save fname char
	Lodsb
	Loop	GetF2
	Jmp	GetF7

GetF4:	Dec	CX
	Jz	GetF8
GetF4a:	Lodsb
	Cmp	AL,' '			;Skip intervening blanks
	Jne	GetF4b
	Loope	GetF4a
	Jcxz	GetF7			; just trailing blanks
GetF4b:	Cmp	AL,CR			;End of parm?
	Je	GetF7			; yes, no switches
	Jmp	Short GetF5b

GetF5:	Dec	CX
	Jz	GetF7
GetF5a:	Lodsb
GetF5b:	Cmp	AL,'/'			;Switch char?
	Jne	GetFx			; no, invalid
	Dec	SI			; yes, back up to it
	Call	GetParm			; and set switches

GetF7:
GetF8:	Cmp	Input,0			;Any input name?
	Jne	GetF9			; no, ask for it
	Call	AskIn
GetF9:	Ret

GetFx:	Mov	DX,Offset ErrMsg
	Jmp	Error
	Page
;
;	Determine switch parameters

GetParm	Proc	Near
	Push	DI
	Push	SI			;Offset to parm string
	Push	CX			;Length of string

	Mov	DI,SI			;Save string ptr
	Add	DI,CX      		; ending offset
GetP0:	Cmp	SI,DI			;Any left?
	Jb	GetP1
	Jmp	GetP9			; no, done

GetP1:	Lodsb
	Cmp	AL,'/'			;Switch char?
	Je	GetP2
	Jmp	Short GetP0

GetP2:	Cmp	SI,DI			;Any string left?
	Jae	GetPx			; no, invalid option
GetP2a:	Lodsb
	Cmp	AL,'L'			;Printer port?
	Je	GetPl
	Cmp	AL,'l'
	Je	GetPl
	Cmp	AL,'6'			; for 6 lpi?
	Je	GetP6
	Cmp	AL,'8'			; for 8 lpi?
	Je	GetP8
	Cmp	AL,'1'			; for cpi?
	Je	GetPc

GetPx:	Mov	DX,Offset ErrMsg	; no, say INVALID OPTIONS
	Jmp	Error

GetPl:	Cmp	SI,DI			;Have next char?
	Jae	GetPx
	Lodsb
	Cmp	AL,'1'			;Valid printer?
	Jb	GetPx
	Cmp	AL,'2'
	Ja	GetPx
	Mov	Msg2a,AL		; Put 'n' into message
	Mov	Output+3,AL		;  and into file name
	Sub	AL,'1'			; Form port address
	Sub	AH,AH
	Mov	LPTn,AX
	Jmp	GetP0			; try next field

GetP6:	Mov	LPP,60			;Set 6 lpi
	Mov	Lpi,54
	Jmp	GetP0

GetP8:	Mov	LPP,82			;Set 8 lpi
	Mov	Lpi,56
	Jmp	GetP0

GetPc:	Cmp	SI,DI			;Any string left?
	Jae	GetPx			; no, invalid
	Lodsb
GetPc12:
	Cmp	AL,'2'			;Is it 12?
	Jne	GetPc17
	Mov	Cpp,96			; chars per line
	Mov	Cpi,28			; printer control code
	Mov	Tabs17,CR
	Mov	Reset_L,Reset12
	Jmp	GetPc2
GetPc17:
	Cmp	AL,'7'			;Is it 17?
	Jne	GetPc10
	Mov	Cpp,136
	Mov	Cpi,29
	Mov	Reset_L,Reset17
	Jmp	GetPc2
GetPc10:
	Cmp	AL,'0'			;Is it 10?
	Jne	GetPx			; none of the above
	Mov	Cpp,80
	Mov	Cpi,30
	Mov	Tabs12,CR
	Mov	Reset_L,Reset10

GetPc2:
	Jmp	GetP0			; and try next switch

GetP9:	Pop	CX
	Pop	SI
	Pop	DI
	Ret
GetParm	Endp
	Page
;
;	Ask for input file name

AskIn	Proc	Near
Ask:	Mov	DX,Offset MsgIn		;Prompt	msg for	input
	Mov	AH,9			;Print string
	Int	21h

	Mov	InKey,64
	Mov	DX,Offset InKey		;Ptr to	keyboard buffer
	Mov	AH,10			;Buffered keyboard input
	Int	21h
	Sub	BX,BX			;Clear for insert
	Add	BL,InKey+1		;Get length read
	Jz	Ask			;If nothing read
	Mov	Byte Ptr Input[BX],0	;Set ASCIIZ stopper
	Mov	Word Ptr InKey,' :'	;Clear error message part
	Ret
AskIn	Endp

GetFile	Endp
	Page
;
;	Open files

Opens	Proc	Near
	Mov	DX,Offset Input
	Mov	AX,3D00h		;Open for input
	Int	21h
	Jnc	Openi
	Mov	DX,Offset Msg1
	Jmp	Error

Openi:	Mov	IHandle,AX		; Return input handle

	Mov	AX,4
	Cmp	LPTn,0			; Using standard printer?
	Je	Openo
	Mov	DX,Offset Output	; Open LPTn
	Mov	AX,3D01h		;  for output
	Int	21h
	Jnc	Openo
	Mov	DX,Offset Msg2		; Open failed
	Jmp	Error

Openo:	Mov	OHandle,AX		; Return output handle
	Ret
Opens	Endp


;
;	Check DOS version

Ver	Proc	Near
	Mov	AH,30h			;Get DOS version
	Int	21h
	Cmp	AL,2			;Rel 2 or later?
	Jae	Ver1			; if not
	Mov	DX,Offset Sorry
 	Jmp	Error

Ver1:	Mov	DX,Offset Version
	Mov	AH,9			;Display title
	Int	21h
	Ret

Ver	Endp
	Page
;
;	Allocate up to 32K for read buffer

Alloc	Proc	Near			;Allocate storage
	Mov	AH,4Ah			;Modify allocated memory
	Mov	BX,PgmSize		;Length of Code and Stack
	Int	21h

	Mov	BX,MaxSize		;Try for 32K each
Alloc1:	Mov	AH,48h
	Int	21h
	Jc	Alloc1			;Failed, get what there is

	Sub	BX,MinSize		;Safety pad
	Cmp	BX,MinSize		;Have enough?
	Jb	Alloc9

	Mov	DX,CS			;Get offset into DS
	Sub	AX,DX			; for input buffer
	Mov	CL,4
	Shl	AX,CL
	Mov	InPtr,AX 		; Read buffer start
	Mov	Iptr,AX			;  and current char offset
	Mov	OutPtr,AX		; Write buffer offset
	Mov	Optr,AX			;  and next char offset

	Shr	BX,1			; Split into two buffers
	Mov	CL,4			; Convert paras
	Shl	BX,CL			;  to bytes available
	Mov	Buflen,BX
	Mov	Olen,BX			; Bytes avail in output buffer
	Add	OutPtr,BX		; Re-adjust output buffer
	Add	Optr,BX

	Ret

Alloc9:	Mov	DX,Offset AlocMsg
	Jmp	Error
Alloc	Endp

LP	Endp

Lstack	Equ	$+128			;End of local stack

PgmSize	Equ	($-Cseg+16+128)/16	;Size of program in paragraphs
MaxSize	Equ	4096-PgmSize		;Paras left in segment
MinSize	Equ	32			;Minimum buffer needed

Cseg	Ends

	End	LP
