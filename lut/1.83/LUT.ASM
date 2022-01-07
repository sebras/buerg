	Page	80,132
	Title	'LUT - List LBR Directory'
	Comment	|

LUT Command
-----------

Purpose:   Displays the	contents of one	or more	library	(LBR) files
	   created by the LU or	LAR utility.

Format:	   LUT	[d:][path]filename[.ext]

Remarks:   If no operands are supplied,	all files with an
	   extension of	LBR in the current path	are listed.
	   Global filename characters *	and ? are allowed in
	   the filename	and extension.

Examples:
	1) List	directory of all LBR files on drive B
		LUT B:

	2) List	directories of all LBR files on	current	drive
		LUT

	3) List	all LBR	directories of filenames beginning with	XYZ
		LUT XYZ*.LBR -or- LUT XYZ?????.LBR

	4) List	all LBR	directories in subdirectory called ABC
		LUT \ABC

Notes:	   Written for the IBM PC using	DOS 2.0	or later.
	   Copyright 1984 Vernon Buerg.	For public domain use.

	Version 1.7, Aug 8, 1984
	Version 1.8, Aug 15,1984
				sorted directory list
				display member CRC and Index pointers
				calculate directory CRC
	Version 1.81, Aug 29, 1984
				added CP/M LU86 date/time formatting
	Version 1.82, Sep 4, 1984
				remove CRC display, use D_Pad
	Version 1.83, Sep 25, 1984
				correct command operands
----------|

	Page
DirNtry	Struc				;LU/LAR	directory entries
D_Stat	Db	0			;File status
D_File	Db	8 Dup (' ')		;File name (FCB	format)
D_Ext	Db	3 Dup (' ')		; and extension
D_Ptr	Dw	0			;Offset	to data	(mod 128)
D_Len	Dw	0			;Length, 128-byte sectors

D_CRC	Db	2 Dup (0)		;CRC check bytes \
D_Cdate	Db	2 Dup (0)		;Create date      \
D_Udate	Db	2 Dup (0)		;Update date       LU86 format
D_Ctime	Db	2 Dup (0)		;Create time      /
D_Utime	Db	2 Dup (0)		;Update time     /
D_Pad	Db	6 Dup (0)		;Pad bytes in last block
DirNtry	Ends

Active	Equ	0
Deleted	Equ	254
Unused	Equ	255
Dir_Len	Equ	Size DirNtry

CR	Equ	13
LF	Equ	10
Stopper	Equ	255

Dater	Record	Yr:7,Mo:4,Dy:5
Timer	Record	HH:5,MM:6,XX:5
	Page
	;*******************************;
	;    List LU/LAR Directory	;
	;*******************************;

Cseg	Segment	Public Para 'CODE'
	Assume	CS:Cseg,DS:Cseg,ES:Cseg
	Org	100h

Lut	Proc	Far
	Lea	SP,Stackx		;Use local stack
	Push	DS			;Standard entry
	Sub	AX,AX			; for DOS return
	Push	AX
	Mov	Stk_Top,SP		;Save for exit

	Call	Ver			;Display and check versions

	Call	Alloc			;Alloc I/O buffer

	Call	GetParm			;Get command parameters

Find:	Mov	DX,Offset FileNm	;Find first matching entry
	Sub	CX,CX
	Mov	AH,4Eh
	Int	21h
	Jc	Error4

Found:	Or	AL,AL			;Any found?
	Jnz	Done			; no, all done

	Call	ListDir			; yes, display it

	Mov	AH,4Fh			;Find next entry
	Int	21h
	Jmp	Short Found


Error4:	Mov	DX,Offset Msg4		;Say NO	MATCHING FILES

Errors:	Mov	AX,CS			;Insure DS
	Mov	DS,AX
	Mov	SP,Stk_Top		;Insure stack
	Call	PrintS			;Error message

Done:	Ret
	Page
;
;	Constants and work areas

Stk_Top	Dw	0			;Stack ptr upon entry
SecSize	Dw	128			;Logical sector	size
TotBlk	Dw	0			;Total blocks used
NumActv	Db	1			;Active	entries
NumDel	Db	0			;Deleted entries
ByteDel	Dw	0			;Blocks	deleted

Mode	Db	0			;New or	old format
;	   01 = ***DIR format	02 = CRC included
;	   04 = LU86 stamps	08 = CRC invalid

Entries	Dw	0
LenDir	Dw	0			;Total directory size

DirKey	Db	'********DIR'		;In new	format libs

Heading	Db	CR,LF,LF
	Db	'=== Library   '
LbrName	Db	13 Dup (0)
Blanks	Db	12 Dup (' ')
LuDate	Db	10 Dup (' ')
LuTime	Db	8 Dup (' '),Stopper

Header	Db	CR,LF,LF,'  Filename Ext   Bytes   Index  '
Headern	Db	'  --- Created --- '
Headerh	Db	'  --- Updated --- ',Stopper

Bmsg	Db	CR,LF,LF
TotByte	Db	'      ',' bytes used;'

Dmsg	Equ	This Byte
NumDir	Db	'      ',' alloc entries;'
TotActv	Db	'      ',' active;'
TotDel	Db	'      ',' deleted'
Dmsg_nd	Db	Stopper			; if none deleted
DelByte	Db	'      ',' bytes',Stopper

Line	Db	CR,LF,'  '		;DETAIL	print line
Member	Db	'filename ext','  '
NumByte	Db	8 Dup (32)
Index	Db	8 Dup (32)
L_End	Db	' '			; end of line if no stamps
C_Date	Db	'mm/dd/yy '
C_Time	Db	'hh:mm:ss'
C_End	Db	' '			; if no update stamp
U_Date	Db	'mm/dd/yy '
U_Time	Db	'hh:mm:ss',Stopper

S_Buf	Dw	0			;Segment addr of buffer
A_Buf	Dw	0			;Offset	to current entry
Handle	Dw	0			;File handle from open

FilePtr	Dw	Offset FileNm		;Offset to filename part
Default	Db	'*.LBR',0		;Default criteria

; Sort variables
Count1	Dw	0			;Number of entries
Count2	Dw	0			;Loop counter
First	Dw	0			;Offset to starting entry
Second	Dw	0			;Offset to next entry to comp
Len	Equ	32			;Length of each entry
KeyPtr	Equ	1			;Offset to key
KeyLen	Equ	11			;Length of key
	Page
Msg1	Db	CR,LF,LF,'Library not found  ',Stopper
BadCRC	Db	CR,LF,'Directory CRC invalid',7,CR,LF,Stopper
Msg3	Db	CR,LF,'I/O error',CR,LF,Stopper
Msg4	Db	CR,LF,'No matching files found',CR,LF,Stopper
Msg6	Db	CR,LF,LF,'Invalid LBR format  ',Stopper
Alocmsg	Db	CR,LF,'Not enough memory',Stopper
Sorry	Db	CR,LF,'PC DOS Version 2.x required',Stopper
Version	Db	'LUT - Version 1.8 - V.Buerg',CR,LF,Stopper
	Page
;
;	List directory for each	file

ListDir	Proc	Near

	Call	OpenLib			;Access next library
	Jnc	List1
	Mov	DX,Offset Msg1		;Say OPEN FAILED
	Jmp	Errmsg

List1:	Call	ReadMst			;Get master DIR entry
	Jnc	List2
	Mov	DX,Offset Msg3		;Say I/O ERROR
	Jmp	Errmsg

List2:	Call	Verify			;Validate master entry
	Jnc	List3
	Mov	DX,Offset Msg6		;Say INVALID LBR FORMAT
	Jmp	Errmsg

List3:	Call	ReadLib			;Read remainder of directory
	Jnc	List3a
	Mov	DX,Offset Msg3
	Jmp	ErrMsg

List3a:	Call	ChkCRC			;Validate directory CRC

	Call	GetDate			;Format file date/time

	Call	Sort			;Sort into name order

;	Display	the titles

	Lea	SI,DTA+30		;Copy filename to heading
	Mov	DI,Offset LbrName
	Mov	CX,13
List5:	Lodsb
	Cmp	AL,0			;End of name?
	Je	List6
	Stosb
	Loop	List5
List6:	Mov	AL,' '			; pad with blanks
	Rep	Stosb

	Mov	DX,Offset Heading	;Display titles
	Call	PrintS
	Test	Mode,8			;CRC okay?
	Jz	List6c
	Mov	DX,Offset BadCRC	; no, say so
	Call	PrintS
List6c:	Mov	DX,Offset Header	; and headings
	Call	PrintS

List7:	Mov	AX,Entries		;Format number of DIR entries
	Mov	DI,Offset NumDir
	Call	Format
	Page
;
;	Display each active entry

List10:	Mov	BX,A_Buf		;Current buffer position
	Cmp	[BX].D_Stat,Deleted	;Entry deleted?
	Jne	List12
	Mov	AX,[BX].D_Len		; yes, accumlate stats
	Add	ByteDel,AX
	Inc	NumDel
	Jmp	List19

List12:	Cmp	[BX].D_Stat,Active	;Is entry in use?
	Je	List13			; no, skip it
	Jmp	List19

List13:	Inc	NumActv
	Lea	SI,[BX].D_File		;Display file name
	Mov	DI,Offset Member
	Mov	CX,8			;Copy file name
	Rep	Movsb
	Inc	DI
	Mov	CX,3			; and extension
	Rep	Movsb

	Mov	AX,[BX].D_Len		;Number	of sectors
	Add	TotBlk,AX

	Mul	SecSize			;Calculate bytes
	Test	Mode,1			;DIR format?
	Jnz	List13a
	Test	Mode,6			;LU86 format?
	Jz	List13a
	Mov	CL,Byte Ptr [BX].D_Pad
	Sub	CH,CH
	Sub	AX,CX
	Sbb	DX,0
List13a:Mov	DI,Offset NumByte
	Call	Formatd			; and format

	Mov	AX,[BX].D_Ptr		;Format Index to data
	Mov	DI,Offset Index
	Call	Format

	Test	Mode,1			;LU86 format?
	Jnz	List17
	Test	Mode,4			; yes, has stamping?
	Jz	List18			; no, short lines

	Mov	DI,Offset C_Time	;Format LU86 create stamp
	Mov	DX,Word Ptr [BX].D_Ctime
	Call	FixTime
	Mov	DI,Offset C_Date
	Mov	DX,Word Ptr [BX].D_Cdate
	Call	CPM_Date

	Mov	DI,Offset U_Time	;Format LU86 update stamp
	Mov	DX,Word Ptr [BX].D_Utime
	Or	DX,DX
	Jnz	List14
	Mov	DX,Word Ptr [BX].D_Ctime
List14:	Call	FixTime
	Mov	DI,Offset U_Date
	Mov	DX,Word Ptr [BX].D_Udate
	Or	DX,DX
	Jnz	List15
	Mov	DX,Word Ptr [BX].D_Cdate
List15:	Call	CPM_Date
	Jmp	List18

List17:	Mov	CX,8			;New ASCII stamp format
	Lea	SI,[BX].D_CRC
	Mov	DI,Offset C_Date	; copy date
	Rep	Movsb
	Mov	CX,8			; and time
	Lea	SI,[BX].D_Utime
	Mov	DI,Offset C_Time
	Rep	Movsb

List18:	Mov	DX,Offset Line		;Display an entry
	Call	PrintS

List19:	Dec	Entries			;Dir count
	Jz	List20
	Add	BX,Dir_Len		; for next entry
	Mov	A_Buf,BX
	Jmp	List10

;
;	Display	totals

List20: Mov	AL,NumActv		;Format	use count
	Sub	AH,AH
	Mov	DI,Offset TotActv
	Call	Format

List22:	Mov	AL,NumDel		;Format	deleted	count
	Sub	AH,AH
	Mov	DI,Offset TotDel
	Call	Format

List23:	Mov	AX,TotBlk		;Format total size in bytes
	Mul	SecSize
	Mov	DI,Offset TotByte
	Call	Formatd

List24:	Cmp	NumDel,0		;Any deleted?
	Je	List25			; no, just active totals
	Mov	Dmsg_nd,''		; yes, expand totals msg
	Mov	AX,ByteDel
	Mul	SecSize			;Format	deleted	bytes
	Mov	DI,Offset DelByte
	Call	Formatd			; from double word

List25:	Mov	DX,Offset Bmsg		;Display Bmsg and Dmsg totals
	Call	PrintS
	Call	Close
	Ret

ErrMsg:	Call	PrintS			;Display error message
	Mov	DX,Offset FileNm	; with filename
	Call	PrintS

Close:	Mov	BX,Handle		;Close library
	Or	BX,BX
	Jz	Closed
	Mov	AH,3Eh
	Int	21h
Closed:	Mov	Handle,0		; indicate closed
	Ret

ListDir	Endp
	Page
;
;	Use next matching entry for Open

OpenLib	Proc	Near
	Lea	SI,DTA+30		;Move name from	DTA
	Mov	DI,FilePtr		; for OPEN
	Mov	CX,13
Move:	Lodsb
	Stosb
	Cmp	AL,0			; if end of name
	Loopne	Move
	Jcxz	Open
	Rep	Stosb

Open:	Mov	DX,Offset FileNm	;Open the library
	Mov	AX,3D00h		; for reading
	Int	21h
	Mov	Handle,AX
	Ret
OpenLib	Endp


ReadMst	Proc	Near
	Mov	BX,Handle		;Read master directory entry
	Mov	CX,32			; first 32-byte record
	Mov	DX,A_Buf
	Mov	AH,3Fh
	Int	21h
	Jc	Error3
	Cmp	AX,CX			;Got all of it?
	Jne	Error3
	Ret

ReadLib:				;Read remaining entries
	Mov	BX,A_Buf
	Mov	AX,Word Ptr [BX].D_Len	;Sectors for direc.
	Sub	DX,DX
	Mov	TotBlk,DX
	Mov	NumActv,DL		;Reset counters
	Mov	NumDel,DL

	Shl	AX,1			;Calc number of entries
	Shl	AX,1 			; four per sector
	Mov	Entries,AX

	Dec	AX			;Calc size remaining
	Mov	CL,5			; as 32-bytes each
	Shl	AX,CL
	Mov	CX,AX
	Mov	LenDir,CX		;Save length
	Add	LenDir,Dir_Len		; of entire directory

	Mov	BX,Handle		;Read rest of directory
	Mov	DX,A_Buf
	Add	DX,Dir_Len
	Mov	AH,3Fh
	Int	21h
	Jc	Error3
	Cmp	AX,CX			;Got all of it?
	Jne	Error3
	Ret

Error3:	Clc
	Ret
ReadMst	Endp
	Page
;
;	Validate master directory entry

Verify	Proc	Near
	Mov	BX,A_Buf
	Sub	AX,AX
	Cmp	Byte Ptr [BX].D_Stat,AL	;Active	first entry?
	Jne	NotLBR
	Cmp	Word Ptr [BX].D_Ptr,AX	;Valid index pointer?
	Jne	NotLBR

	Mov	Mode,AL			;Init LBR type and
	Mov	AL,Stopper
	Mov	Headern,AL		; line lengths
	Mov	Headerh,AL
	Mov	L_End,AL
	Mov	C_End,AL

	Mov	CX,11			;Check name of blanks
	Lea	SI,Word Ptr [BX].D_File
	Mov	DI,Offset Blanks
	Repe	Cmpsb
	Jne	Ver4

	Cmp	Word Ptr [BX].D_CRC,CX	;Any CRC?
	Je	Ver2
	Or	Mode,2			; yes...
Ver2:	Cmp	Word Ptr [BX].D_Ctime,CX
	Je	Ver9			;Any LU86 stamps?
	Or	Mode,4			; yes...
	Mov	C_End,' '
	Mov	Headerh,' '
	Jmp	Short Ver8

Ver4:	Mov	CX,11			;May be	new format
	Lea	SI,Byte Ptr [BX].D_File
	Mov	DI,Offset DirKey
	Repe	Cmpsb
	Jne	NotLBR
	Mov	Mode,1			;Indicate ***DIR format
Ver8:	Mov	Headern,' '
	Mov	L_End,' '

Ver9:   Clc				;Return CD=0
	Ret

NotLBR:	Stc				;or CF=1 if not LBR
	Ret
Verify	Endp
	Page
;
;	Check CRC for directory

ChkCRC	Proc	Near
	And	Mode,0FFh-8		;Clear error indication
	Test	Mode,2			;LU86 CRC included?
	Jz	ChkCRC9			; no, skip it
	Mov	SI,A_Buf		;Calculate directory CRC
	Mov	BX,SI
	Mov	CX,LenDir
	Mov	DX,Word Ptr [BX].D_CRC	;Save original CRC
	Or	DX,DX			; any used?
	Jz	ChkCRC9			; nope, skip check
	Mov	Word Ptr [BX].D_CRC,0

	Call	GetCRC			;CRC for directory block
	Call	UpdCRC			; and for end-of-block

	Mov	Word Ptr [BX].D_CRC,DX
	Cmp	AX,DX			;CRC correct?
	Je	ChkCRC9
	Or	Mode,8			; no, indicate error
ChkCRC9:Ret
ChkCRC	Endp
	Page
;
;	Calculate CRC for a block from CCIT polynomial
;
;	CRC = x^16 + x^12 + x^5 + 1

GetCRC	Proc	Near			;SI points to data
	Push	BX			;CX contains length
	Push	DX

	Sub	BX,BX			;Zero resultant CRC
GetCRCs:Mov	DX,CX

GetCRC0:Mov	CX,8			; bits in a byte
	Lodsb				; get next byte
GetCRC1:Rol	AL,1			;MSB -> carry
	Rcl	BX,1			;    -> CRC LSB
	Jnc	GetCRC2
	Xor	BX,1021h
GetCRC2:Loop	GetCRC1
	Dec	DX
	Jnz	GetCRC0

	Mov	AX,BX			;Return CRC in AX
	Pop	DX
	Pop	BX
	Ret
GetCRC	Endp

;	Update CRC at end of block

UpdCRC	Proc	Near			;CRC in AX
	Push	BX
	Push	DX
	Mov	BX,AX			;Current CRC
	Mov	CX,2			;Last two bytes
	Mov	SI,Offset Zero		; of zero
	Jmp	Short GetCRCs
Zero	Dw	0
UpdCRC	Endp
	Page
;
;	Get Library file date/time

GetDate	Proc	Near			;Determine original date
	Mov	BX,Handle
	Mov	AX,5700h		;Get LBR file date/time
	Int	21h			; in DX:CX
	Push	CX
	Mov	DI,Offset LuDate	;Convert DOS date
	Call	FixDate
	Pop	DX			;Convert DOS time
	Mov	DI,Offset LuTime
	Call	FixTime
	Ret

;	Format DOS date

FixDate:Mov	AX,DX			;Get month part
	And	AX,Mask Mo
	Mov	CL,Mo
	Call	Cnvrt
	Stosw
	Mov	AL,'/'
	Stosb				;Add delimiter

	Mov	AX,DX			;Get day part
	And	AX,Mask Dy
	Call	Cnvrt1
	Stosw
	Mov	AL,'/'
	Stosb				;Add delimiter

	Mov	AX,DX			;Get year part
	And	AX,Mask Yr
	Mov	CL,Yr
	Call	Cnvrt
	Or	AL,'8'
	Stosw
	Ret

;	Format DOS time

FixTime:Mov	AX,DX			;Get hour part
	And	AX,Mask Hh
	Mov	CL,Hh
	Call	Cnvrt
	Stosw
	Mov	AL,':'
	Stosb				;Add delimiter

	Mov	AX,DX			;Get min part
	And	AX,Mask Mm
	Mov	CL,Mm
	Call	Cnvrt
	Stosw
	Mov	AL,':'
	Stosb				;Add delimiter

	Mov	AX,DX			;Get secs part
	And	AX,Mask Xx
	Add	AX,AX
	Call	Cnvrt1
	Stosw
	Ret

Cnvrt:	Shr	AX,CL			;Convert to ASCII
Cnvrt1:	Aam
	Or	AX,'00'
	Xchg	AH,AL
	Ret
GetDate	Endp
	Page
;
;	Format CPM date

CPM_Date Proc	Near			;Convert CP/M date
	Push	AX
	Push	CX
	Push	SI

	Mov	AX,DX			;Days since 12/31/77
	Sub	CX,CX			;Years since
	Mov	DX,OneYear
CD1:	Sub	AX,DX			; for 1978
	Jle	CD2
	Inc	CL
	Sub	AX,DX			; for 1979
	Jle	CD2
	Inc	CL
	Inc	DX
	Sub	AX,DX			; for next leap year
	Jle	CD2
	Dec	DX
	Inc	CL
	Sub	AX,DX			; and year after
	Jle	CD2
	Inc	CL
	Jmp	Short CD1

CD2:	Add	AX,DX
	Mov	DX,AX			;Save days left over

CD3:	Mov	AX,CX			;Adjust year
	Add	AL,78			; plus base year

	Mov	Days+1,28		;Days in Feb
	Test	AL,3			;Is it leap year?
	Jnz	CD4			; no, has 28
	Mov	Days+1,29		; yes, has one more

CD4:	Call	Cnvrt1			;Format year
	Mov	Word Ptr 6[DI],AX

	Mov	SI,Offset Days		; point to days/month
	Sub	AX,AX
	Mov	CL,1			; month number
CD5:	Lodsb
	Sub	DX,AX			; days into month
	Jle	CD6			; within month
	Inc	CL
	Jmp	Short CD5

CD6:	Add	DX,AX
CD7:	Mov	AX,CX			;Format month
	Call	Cnvrt1
	Mov	Word Ptr [DI],AX

	Mov	AX,DX			;Format day
	Call	Cnvrt1
	Mov	Word Ptr 3[DI],AX

	Pop	SI
	Pop	CX
	Pop	AX
	Ret

Days	Db 	31,28,31,30,31,30,31,31,30,31,30,31
OneYear	Equ	365			;Days in normal year
CPM_Date Endp
	Page
;
;  Format a double word	value

Format	Proc	Near			;Format	a block	number
	Sub	DX,DX
Formatd:Push	AX			;Value in DX:AX
	Push	DI			;Offset	to target
	Push	BX
	Push	CX
	Push	SI

	Mov	BX,DI			;Save target offset
	Mov	CX,6			;Clear target to blanks
	Mov	SI,Offset Blanks
	Rep	Movsb

	Mov	CX,4			;Divide	sucessively by
	Sub	SI,SI			; powers of ten
	Mov	DI,BX			;Restore target	ptr
Form1:	Or	AX,AX			;It is zero?
	Jnz	Form1d
	Or	DX,DX
	Jz	Form2
Form1d:	Div	TenK[SI]
	Aam				;Make AL into BCD
Form2:	Or	AX,'00'			; and to ASCII
	Xchg	AL,AH
	Or	Byte Ptr [DI],AL
	Mov	Byte Ptr [DI]+1,AH
	Inc	DI			;Next digit
	Add	SI,2			;Next divisor
	Mov	AX,DX			;Copy remainder
	Sub	DX,DX			; and clear hi-word
	Loop	Form1

	Aam				;Make AL into BCD
	Or	AX,'00'			; and to ASCII
	Xchg	AL,AH
	Mov	Byte Ptr [DI]+1,AH
	Mov	CL,5			;Suppress leading zeros
	Mov	DI,BX			;Get target offset back
	Mov	AL,' '
Form3:	Cmp	Byte Ptr [DI],'0'
	Jne	Form4
	Stosb
	Loop	Form3

Form4:	Pop	SI
	Pop	CX
	Pop	BX
	Pop	DI
	Pop	AX
	Ret

TenK	Dw	10000,1000,100,10	;For converting	numbers
Format	Endp
	Page
;
;	Print String

PrintS	Proc	Near			;Print string like Int 21h (9)
	Push	BX			;DX points to string
	Push	BP
	Push	SI
	Mov	SI,DX
PS1:	Lodsb
	Cmp	AL,0			;Skip zeros
	Je	PS1
	Cmp	AL,Stopper		;String	ends in	a hex FF
	Je	PS9			; so can print $
	Mov	AH,2			;Display output	to standrd dev
	Mov	DL,AL
	Int	21h
	Jmp	Short PS1

PS9:	Pop	SI
	Pop	BP
	Pop	BX
	Ret
PrintS	Endp

;
;	Display and check versions

Ver	Proc	Near
	Mov	DX,Offset Version	;Display program name
	Call	PrintS

	Mov	AH,30h			;Check DOS version
	Int	21h
	Cmp	AL,2
	Jb	Err2
	Ret
Err2:	Mov	DX,Offset Sorry
	Jmp	Errors
Ver	Endp
	Page
;
;	Allocate Directory Buffer

Alloc	Proc	Near
	Mov	BX,Paras		;Shrink	memory
	Mov	AH,4Ah
	Int	21h

	Mov	BX,512			;Ask for 8K
	Mov	AH,48h
	Int	21h
	Jnc	Alloc9
	Mov	DX,Offset Alocmsg
	Jmp	Errors

Alloc9:	Mov	S_Buf,AX		;Save gotten buffer addr
	Mov	CX,CS			;Offset into DS:DX
	Sub	AX,CX
	Mov	CL,4
	Shl	AX,CL
	Mov	A_Buf,AX
	Ret
Alloc	Endp
	Page
;
;	Get Library Filename

GetParm	Proc	Near			;Operand is LBR name
	Mov	DI,Offset FileNm
	Mov	CX,38
	Sub	AX,AX			;Clear filename
	Rep	Stosb			; to zeros
	Mov	AL,Stopper
	Stosb				; and append stopper

	Mov	SI,82h			;Point to command tail
	Mov	DI,Offset FileNm	; and target
	Or	CL,DS:[80h]		;Length of parameters
	Jnz	Copy1
	Jmp	Copy7			; none, list all LBR

Copy1:	Lodsb				;Skip leading blanks
	Cmp	AL,' '			; while copying LBR name
	Loope	Copy1

Copy2:	Stosb				;Copy non-blanks
	Lodsb
	Cmp	AL,0Dh			;End of parameters?
	Je	Copy3			; yes, done
	Cmp	AL,' '			; no, have blank as delimiter?
	Loopne	Copy2			; if not, just copy

Copy3:	Mov	SI,Offset FileNm+75	;Find drive or path
	Mov	CX,76
	Std
Copy4:	Lodsb
	Cmp	AL,'\'			;Final path name?
	Jne	Copy5
	Add	SI,2			;Save end of path ptr
	Mov	FilePtr,SI
	Jmp	Short Copy9

Copy5:	Cmp	AL,':'			;Drive?
	Loopne	Copy4
	Cld
	JCXZ	Copy9
	Add	SI,2
	Mov	FilePtr,SI
	Cmp	Byte Ptr [SI],0		;Just drive?
	Jne	Copy9 			; no, leave as-is

	Mov	DI,SI			; yes, append wild cards
Copy7:	Mov	SI,Offset Default
	Cld
	Mov	CX,6
	Rep	Movsb

Copy9:	Cld
	Lea	DX,DTA			;Establish a DTA
	Mov	AH,1Ah
	Int	21h

	Mov	DX,Offset FileNm
	Call	PrintS
	Ret
GetParm	Endp

	Subttl	--- SORT Subroutine ---
	Page
;
;	Bubble sort of directory names, CX=number of entries

Sort	Proc	Near			;Nothing fancy here
	Mov	CX,Entries		;Sort into name order
	Mov	Count1,CX		;Record count
	Mov	DI,A_Buf		;Offset to array

	Mov	AX,CX			;Get count
	Dec	AX			; less one as loop limit
	Jz	Sort0			;Only one
	Js	Sort0			; or none
	Mov	Count2,AX		;Save loop limit
	Jmp	Short Sortit

Sort0:	Jmp	Sorted			;None to sort

Sortit:	Mov	First,DI		;Offset to first entry
	Mov	Second,DI

Sort1:	Mov	DX,Count2		;Save limit count

Sort2:	Mov	SI,First		;First entry to
	Add	SI,KeyPtr
	Mov	DI,Second		; compare to next entry
	Add	DI,Len
	Mov	Second,DI
	Add	DI,KeyPtr
	Mov	CX,KeyLen
	Repe	Cmpsb			;Compare elements
	Jbe	Sort3			; if in order, no swap

Swap:	Mov	DI,Second		; else swap
	Mov	BX,DI
	Mov	SI,First		;Copy first to temp
	Mov	DI,Offset Temp
	Mov	CX,Len
	Rep	Movsb

	Mov	SI,BX			;Copy second to first
	Mov	DI,First
	Mov	CX,Len
	Rep	Movsb

	Mov	SI,Offset Temp		;Copy temp to second
	Mov	DI,BX
	Mov	CX,Len
	Rep	Movsb

Sort3:	Dec	DX
	Jnz	Sort2
	Dec	Count2
	Jz	Sorted
	Mov	AX,Len			;Bump to next entry
	Add	AX,First		; for next loop
	Mov	First,AX
	Mov	Second,AX
	Jmp	Sort1

Sorted:	Ret
Sort	Endp
	Page
Storage	Equ	This Byte
Stackx	Equ	Storage+256		;Local stack end
DTA	Equ	Storage+256+0		;Data transfer area
FileNm	Equ	Storage+256+48		;Requested file name
Temp	Equ	Storage+256+48+77	;Sort exchange area

Paras	Equ	($-Cseg+2048)/16	;Paragraphs in program
					;including stack and patch area
Lut	Endp

Cseg	Ends
	End	Lut
