	Page	75,132
	Title	LP - Print File With Pagination

	Comment |

LP Command
________________

Purpose:  To print an ASCII file on the standard printer
	  device at either 66 or 88 lines per page. A title
	  is printed at the top of each page which contains
	  the file name, creation date, and page number.

Syntax:   LP [d][path]filename[.ext]	[/6][/8]
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
	Version 1.5, June 13, 1986.
		- minimal changes for HP LaserJet
	Version 1.6, June 19, 1986
		- expand tabs and use HP LJ printer codes
		- fine tune cpi and lpi
		- use Int 17h for quicker printing
________________							|

Cseg	Segment Public Para 'CODE'
	Assume	CS:Cseg, DS:Cseg
	Org	100h

LP	Proc	Far
	Jmp	Start    		; Put usage data up front
	Page
;
;	Constants and Data Areas

BEL	Equ	07
BS	Equ	08
TAB	Equ	09
LF	Equ	10
FF	Equ	12
CR	Equ	13
EOF	Equ	26
ESC	Equ	27
Stopper	Equ	'$'			; Ends text message strings

Dater	Record	Yr:7,Mo:4,Dy:5

	Db	BS,BS,BS
Version Db	CR,LF,'LP - Version 1.6l - V.Buerg',CR,LF,Stopper,BS,BS
	Db	CR,LF,'Usage:'
	Db	CR,LF,'	LP [d:][\path]filename[.ext]'
	Db	CR,LF,'	   [/6][/8]  [/L1][/L2] [/10][/12][/17]'
	Db	CR,LF,EOF

AlocMsg Db	CR,LF
	Db	'Not enough memory',CR,LF,BEL,Stopper
ErrMsg	Db	CR,LF
	Db	'Invalid command option(s)',CR,LF,BEL,Stopper
Sorry	Db	CR,LF
	Db	'Sorry, PC DOS 2.0 or later required',CR,LF,BEL,Stopper

EofMsg	Db	CR,LF
	Db	'End of file.',CR,LF,Stopper

Buflen	Dw	0			;I/O buffer size (variable)
Stk_Top Dw	0			;Stack ptr at entry

LPTn	Dw	0			;Printer port
Errlvl	Db	0			;Error level returned

Heading Db	ESC,'&a0C'		;Top line title
	Db	ESC,'&dD'               ; underlined
	Db	ESC,'(s3B'              ; bold (if available) title
FileNm	Db	60 Dup (' ')
Date	Db	'mm-dd-yy','    '
	Db	'Page  '
Pageno	Db	'1'
	Db	LF,ESC,'(s0B'           ; medium data
	Db	ESC,'&d@'               ; no more underlining
	Db	CR,LF

Len_H	Equ	This Byte - Heading
	Page
;
;	Printer intialization set-up commands

Lcnt	Db	0			; Line counter
Ccnt	Db	0			; Chars in current line

Cpp	Db	80			; Max chars per page
LPP	Db	61			; Max lines per page

Reset	Db	ESC,'E'                 ; Printer initialization codes
Margin	Db	ESC,'&a0L'              ; Left margin of 1
Wrap	Db	ESC,'&s0C'		; Enable line wrapping
Perf	Db	ESC,'&l0L'		; Perforation skip mode off

	Db	ESC,'&l2E'              ; Top margin
	Db	ESC,'&l'
PL	Db	'62F'                   ; Page length

	Db	ESC,'&l'
Lpi	Db	'6','D'                 ; Lines per inch

	Db	ESC,'&k'
Cpi	Db	'0S'                    ; Chars per inch

Reset_L Equ	$-Reset 		; Length of initial string
	Page
;
;	File variables and messages

MsgIn	Db	CR,LF,'Enter INPUT filename  $'
Msg1	Db	CR,LF,'Unable to open input'
InKey	Db	32,32			; Keyboard buffer
Input	Db	76 Dup (0),Stopper      ; Drive:path\name.ext
IHandle Dw	0			; Input file handle
Ilen	Dw	0			; Input block length
Iptr	Dw	Offset Buffer		; Offset to next char

Msg2	Db	CR,LF,'Unable to open LPT'
Msg2a	Db	'1$'
Output	Db	'LPT1:',0,Stopper       ;Printer name
OHandle Dw	0			;Output file handle
Olen	Dw	0			;Output block length
Optr	Dw	0			;Offset to next char
OutPtr	Dw	0			;Offset to output buffer

OutChar Db	0
	Page
;
;	Program initialization and main sequence

Start:
	Mov	SP,Offset CS:Lstack	;Use local stack

	Push	DS			;For DOS return
	Sub	AX,AX
	Push	AX
	Mov	Stk_Top,SP

	Call	Ver			; Check DOS version

	Call	Alloc			; Allocate memory

	Call	GetFile 		; Get file name

	Call	Opens			; Open input

	Call	InitLPT 		; Initialize printer

	Call	GetName 		; Format title line

	Call	Titles			; and print it

	Call	List			; Print the file

	Call	Flush			; Drain the output buffer

Eod:	Mov	DX,Offset EofMsg	; Say END-OF-FILE
	Jmp	Fini

Error:	Mov	CS:Errlvl,1
Fini:	Mov	AX,CS			; Insure final seg regs
	Mov	DS,AX
	Mov	SP,Stk_Top		; and stack

	Mov	AH,9			; Print error message
	Int	21h

	Mov	BX,IHandle		; Close input
	Mov	AH,3Eh
	Int	21h

Exit:
	Mov	AL,Errlvl		; Set ERROR LEVEL
	Mov	AH,4Ch			; and Exit
	Int	21h
	Page
;
;	Copy file to printer

List	Proc	Near

List1:	Call	Read			; Get one character
	And	AL,7FH			;  and hi-order bit (?)

	Cmp	AL,FF			; Is it form feed?
	Je	Eject

	Cmp	AL,LF			; Pass line feed
	Je	Passit

	Cmp	AL,CR			; Pass carriage return
	Je	Passit

	Cmp	AL,BS			; Pass back space
	Je	PassBS

	Cmp	AL,TAB			; Expand tab chars
	Je	PassTAB
	Inc	Ccnt			; Incr count of chars in line

	Cmp	AL,EOF			; End of file?
	Jne	Check32
	Jmp	Done
Check32:
	Cmp	AL,32			; Other control char?
	Jns	Passit
	Jmp	CtlChr

PassTAB:Mov	DL,Ccnt 		; Current column count
	Sub	DH,DH
	Add	Ccnt,8			; Round up to TAB column
	And	Ccnt,0F8h
	Mov	CL,CCnt
	Sub	CH,CH
	Sub	CX,DX			; Blanks to fill
	Mov	AL,' '
	Jcxz	Check_Wrap
PassTabs:
	Call	PutChar
	Loop	PassTabs
	Jmp	Check_Wrap

PassBS: Dec	Ccnt			;Account for backspace
	Jns	Passit
	Mov	Ccnt,0

Passit: Call	PutChar

Check_Wrap:
	Mov	AH,Cpp			; Max chars per line
	Cmp	Ccnt,AH 		;  filled up a line?
	Ja	Check_Wrap2
	Cmp	AL,LF			; Is it line feed?
	Jne	List1			; no, get next char

Check_Wrap2:
	Inc	Lcnt			; yes, incr line count
	Mov	Ccnt,0
	Mov	AL,Lcnt
	Cmp	AL,LPP			; End of page?
	Jbe	List1			; no, get next char

Eject:	Mov	Ccnt,0			; Reset char count in line
	Cmp	Lcnt,2			; Printed any lines yet?
	Ja	Eject1
	Jmp	List1			; no, ignore form feed

Eject1:
	Call	NewPage
	Jmp	List1			;Get next record

CtlChr: Cmp	AL,0			; Null char?
	Je	Blanks			; yes, make it a space
	Push	AX
	Mov	AL,'^'                  ; Indicate a control char
	Call	PutChar
	Inc	Ccnt
	Pop	AX			; Get char again
Blanks: Add	AL,20H			; Make it printable
	Jmp	Passit

Done:	Ret
List	Endp
	Page
;
;	Process end of page

NewPage Proc	Near
	Cmp	Lcnt,2			; Is it title line?
	Je	Titles			; yes, skip rest
	Mov	AL,FF			;        and send form feed
	Call	PutChar
	Mov	Lcnt,0			; Reset line counter

	Push	DI			; Format new page number
	Mov	DI,Offset Pageno
	Mov	AX,3A30h
Next:	Inc	Byte Ptr [DI]		; Incr page number
	Cmp	[DI],AL 		; End in zero?
	Js	Set1			; yes, make it a one
	Cmp	[DI],AH 		; Over nine?
	Jne	PgSet			; no, have good number
	Mov	[DI],AL 		; yes, make last digit zero
	Dec	DI			;      and incr hi-order
	Jmp	Next

Set1:	Mov	Byte Ptr [DI],'1'
PgSet:	Pop	DI

;
;	Print top line titles

Titles: Mov	SI,Offset Heading	; Print title line
	Mov	CX,Len_H
Next1:	Lodsb
	Cmp	AL,0			; Replace nulls in filename
	Jne	Next2			;  with spaces
	Mov	AL,' '
Next2:	Call	PutChar
	Loop	Next1
	Mov	Lcnt,2			; Reset line counter
	Ret

;
;	Initialize the printer

InitLPT Proc	Near			;Initialize the printer
Init1:	Mov	CX,Reset_L		; Length of
	Mov	SI,Offset Reset 	;   initial codes
Init2:	Call	Next1
	Ret
InitLPT Endp

NewPage Endp
	Page
;
;	Format title line

GetName Proc	Near			; Format title line
	Mov	SI,Offset Input 	; Copy file name
	Mov	DI,Offset Filenm	;   to heading
	Mov	CX,42			; Max for title
	Cld
	Repz	Movsb

	Mov	AX,5700h		; Return file's date and time
	Mov	BX,IHandle		; Input handle
	Int	21h

	Mov	DI,Offset Date		; Date field in title

	Mov	AX,DX			; Get month part
	And	AX,Mask Mo
	Mov	CL,Mo
	Call	Format
	Stosw
	Inc	DI			; Add delimiter

	Mov	AX,DX			; Get day part
	And	AX,Mask Dy
	Mov	CL,Dy
	Call	Format
	Stosw
	Inc	DI			; Add delimiter

	Mov	AX,DX			; Get year part
	And	AX,Mask Yr
	Mov	CL,Yr
	Call	Format
	Or	AL,'8'
	Stosw
	Ret
GetName Endp

Format	Proc	Near			; Convert binary to ASCII
	Shr	AX,CL
	Aam
	Or	AX,'00'
	Xchg	AH,AL
	Ret
Format	Endp
	Page
;
;	Extract one char from record

Read	Proc	Near			; Read char into AL
Read1:	Cmp	Ilen,0			; Any in buffer?
	Je	Read2			;  no, read next block
	Mov	SI,Iptr 		;  yes, get offset in buf
	Lodsb
	Inc	Iptr			; Offset for next one
	Dec	Ilen			; Decr buffer size left
	Ret				;   and return

Read2:	Mov	BX,IHandle		; Read input
	Mov	CX,BufLen
	Mov	DX,Offset Buffer	; Set up DS:DX
	Mov	AH,3Fh
	Int	21h			; Read a block

	Mov	DX,Offset Buffer
	Mov	Iptr,DX 		; Reset buffer ptr
	Mov	Ilen,AX 		;   and length
	Jc	Read8
	Or	AX,AX			; Anything read?
	Jnz	Read1			;  yes, pick it up
	Mov	AL,EOF			;  no, return EOF
	Ret

Read8:	Mov	DX,Offset Msg3		;Say I/O ERROR
	Jmp	Error

Msg3	Db	CR,LF,'I/O error',CR,LF,BEL,Stopper
Read	Endp

;
;	Use Int 17h to print a character

PutChar Proc	Near			;Write from AL
	Push	AX
	Push	DX
PutCh1:
	Mov	DX,LPTn		; Printer port number
	Mov	AH,0		; Print one char
	Int	17h		;  via BIOS

	Test	AH,025h		; Successful?
	Jnz	PutCh1		; no, wait for printer

	Pop	DX		; Recover registers
	Pop	AX
	Ret

Flush:	Mov	AL,FF		; Eject last page
	Call	PutChar
	Ret

PutChar Endp
	Page
;
;	Get file names from parm

GetFile Proc	Near			;Get file name(s)
	Mov	SI,80h			;Point to command line
	Sub	CX,CX			;Clear length reg
	Or	CL,Byte Ptr [SI]	;Get command tail length
	Jz	GetF8			; none, ask for them
	Mov	DI,Offset Input 	;Point fname target
	Inc	SI			;Bump command ptr

GetF1:	Lodsb				;Get next char
	Cmp	AL,' '                  ;Skip leading blanks
	Jne	GetF2
	Loope	GetF1
	Jcxz	GetF8			; all blank

GetF2:	Cmp	AL,CR			;End of parm?
	Je	GetF7			; yes, terminate fname
	Cmp	AL,' '                  ;Delimiter?
	Je	GetF4			; yes, look for swithes
	Cmp	AL,'/'                  ;Switch char?
	Je	GetF5
	Stosb				;Save fname char
	Lodsb
	Loop	GetF2
	Jmp	GetF7

GetF4:	Dec	CX
	Jz	GetF8
GetF4a: Lodsb
	Cmp	AL,' '                  ;Skip intervening blanks
	Jne	GetF4b
	Loope	GetF4a
	Jcxz	GetF7			; just trailing blanks
GetF4b: Cmp	AL,CR			;End of parm?
	Je	GetF7			; yes, no switches
	Jmp	Short GetF5b

GetF5:	Dec	CX
	Jz	GetF7
GetF5a: Lodsb
GetF5b: Cmp	AL,'/'                  ;Switch char?
	Jne	GetFx			; no, invalid
	Dec	SI			; yes, back up to it
	Call	GetParm 		; and set switches

GetF7:
GetF8:	Cmp	Input,0 		;Any input name?
	Jne	GetF9			; no, ask for it
	Call	AskIn
GetF9:	Ret

GetFx:	Mov	DX,Offset ErrMsg
	Jmp	Error
	Page
;
;	Determine switch parameters

GetParm Proc	Near
	Push	DI
	Push	SI			;Offset to parm string
	Push	CX			;Length of string

	Mov	DI,SI			;Save string ptr
	Add	DI,CX			; ending offset
GetP0:	Cmp	SI,DI			;Any left?
	Jb	GetP1
	Jmp	GetP9			; no, done

GetP1:	Lodsb
	Cmp	AL,'/'                  ;Switch char?
	Je	GetP2
	Jmp	Short GetP0

GetP2:	Cmp	SI,DI			;Any string left?
	Jae	GetPx			; no, invalid option
GetP2a: Lodsb
	Cmp	AL,'L'                  ;Printer port?
	Je	GetPl
	Cmp	AL,'l'
	Je	GetPl
	Cmp	AL,'6'                  ; for 6 lpi?
	Je	GetP6
	Cmp	AL,'8'                  ; for 8 lpi?
	Je	GetP8
	Cmp	AL,'1'                  ; for cpi?
	Je	GetPc

GetPx:	Mov	DX,Offset ErrMsg	; no, say INVALID OPTIONS
	Jmp	Error

GetPl:	Cmp	SI,DI			;Have next char?
	Jae	GetPx
	Lodsb
	Cmp	AL,'1'                  ;Valid printer?
	Jb	GetPx
	Cmp	AL,'2'
	Ja	GetPx
	Mov	Msg2a,AL		; Put 'n' into message
	Mov	Output+3,AL		;  and into file name
	Sub	AL,'1'                  ; Form port address
	Sub	AH,AH
	Mov	LPTn,AX
	Jmp	GetP0			; try next field

GetP6:	Mov	LPP,61			; Set 6 lpi
	Mov	Lpi,'6'
	Mov	Word Ptr PL,'36'
	Jmp	GetP0

GetP8:	Mov	LPP,81			; Set 8 lpi
	Mov	Lpi,'8'
	Mov	Word Ptr PL,'48'
	Jmp	GetP0

GetPc:	Cmp	SI,DI			; Any string left?
	Jae	GetPx			; no, invalid
	Lodsb
GetPc12:
	Cmp	AL,'2'                  ; Is it /12?
	Jne	GetPc17
	Mov	Cpp,96			; chars per line
	Mov	Cpi,'1'                 ; printer control code
	Jmp	GetPc2
GetPc17:
	Cmp	AL,'7'                  ; Is it /17?
	Jne	GetPc10
	Mov	Cpp,136
	Mov	Byte Ptr Cpi,'2'        ; Compressed for cpi
	Jmp	Short GetPc2
GetPc10:
	Cmp	AL,'0'                  ;Is it 10?
	Jne	GetPx			; none of the above
	Mov	Cpp,80
	Mov	Cpi,'0'                 ; Default font cpi

GetPc2:
	Jmp	GetP0			; and try next switch

GetP9:	Pop	CX
	Pop	SI
	Pop	DI
	Ret
GetParm Endp
	Page
;
;	Ask for input file name

AskIn	Proc	Near
Ask:	Mov	DX,Offset MsgIn 	;Prompt msg for input
	Mov	AH,9			;Print string
	Int	21h

	Mov	InKey,64
	Mov	DX,Offset InKey 	;Ptr to keyboard buffer
	Mov	AH,10			;Buffered keyboard input
	Int	21h
	Sub	BX,BX			;Clear for insert
	Add	BL,InKey+1		;Get length read
	Jz	Ask			;If nothing read
	Mov	Byte Ptr Input[BX],0	;Set ASCIIZ stopper
	Mov	Word Ptr InKey,' :'     ;Clear error message part
	Ret
AskIn	Endp

GetFile Endp
	Page
;
;	Open files

Opens	Proc	Near
	Mov	DX,Offset Input
	Mov	AX,3D00h		; Open for input
	Int	21h
	Jnc	Openi
	Mov	DX,Offset Msg1
	Jmp	Error

Openi:	Mov	IHandle,AX		; Return input handle
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
;	Allocate up to 64K for read buffer

Alloc	Proc	Near			; Allocate storage
	Mov	BX,Word Ptr DS:6	; Highest segment address
	Mov	CX,CS			; Program starting seg addr
	Sub	BX,CX			; Size of program segment
	Sub	BX,Pgmsize		;  less size of code

	Sub	BX,MinSize		; Minimum buffer request size
	Cmp	BX,MinSize		; Have enough?
	Jb	Alloc9

	Mov	CL,4			; Convert paras
	Shl	BX,CL			;  to bytes available
	Mov	Buflen,BX
	Ret

Alloc9: Mov	DX,Offset AlocMsg
	Jmp	Error
Alloc	Endp

LP	Endp

Lstack	Equ	$+128			; End of local stack
Minsize	Equ	256			; Require 4k minimum
Buffer	Equ	Lstack + 128		; Input buffer
PgmSize	Equ	($-Cseg+1024) / 16	; Program size in paragraphs

Cseg	Ends
	End	LP
