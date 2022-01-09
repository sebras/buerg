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
	Version 1.90, Nov 10, 1984
				default extension to LBR
	Version 1.91, Feb 9, 1985
				correct CHDIR problem
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


Cseg	Segment	Public Para 'CODE'
	Assume	CS:Cseg,DS:Cseg,ES:Cseg
	Org	100h

Lut	Proc	Far
	Lea	SP,Stackx		;Use local stack
	Push	DS			;Standard entry
	Sub	AX,AX			; for DOS return
	Push	AX
	Mov	Stk_Top,SP		;Save for exit
	Jmp	Ver
	Page
;
;	Constants and work areas

Mode	Db	0			;New or	old format
;	   01 = ***DIR format	02 = CRC included
;	   04 = LU86 stamps	08 = CRC invalid

TotBlk	Dw	0			;Total blocks used
NumDel	Db	0			;Deleted entries
ByteDel	Dw	0			;Blocks	deleted
Entries	Dw	0			;Entries in dir
LenDir	Dw	0			;Total directory size

A_Buf	Dw	Offset DirBuf		;Offset	to current entry
Handle	Dw	0			;File handle from open
CurDisk	Db	255			;Current disk
Stk_Top	Dw	0			;Stack ptr upon entry

SecSize	Dw	128			;Logical sector	size
NumActv	Db	1			;Active	entries

FilePtr	Dw	Offset FileNm		;Offset to filename part
Filend	Dw	Offset FileNm		; next char in file name
Default	Db	'*.LBR'			;Default criteria
Zero	Dw	0       		; with ASCIIZ stopper

DirKey	Db	'********DIR'		;In new	format libs

Heading	Db	CR,LF,LF
	Db	'=== Library   '
LbrName	Db	13 Dup (0)
Blanks	Db	11 Dup (' ')
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

Msg1	Db	CR,LF,'No files found ',Stopper
BadCRC	Db	CR,LF,'Dir CRC invalid',7,CR,LF,Stopper
Msg3	Db	CR,LF,'I/O error',CR,LF,Stopper
Msg6	Db	CR,LF,LF,'Invalid LBR format: ',Stopper
Alocmsg	Db	CR,LF,'Not enough memory',Stopper
Sorry	Db	CR,LF,'PC DOS Version 2.x required',Stopper
Version	Db	'LUT - Version 1.91 - V.Buerg',Stopper
	Page
;
;	Display and check versions

Ver:	Mov	DX,Offset Version	;Display program name
	Call	PrintS
	Mov	AH,30h			;Check DOS version
	Int	21h
	Cmp	AL,2
	Jae	Alloc
	Mov	DX,Offset Sorry
	Jmp	Errors

;	Allocate Directory Buffer

Alloc:	Mov	BX,Paras		;Shrink	memory
	Mov	AH,4Ah  		; to see if have engouh memory
	Int	21h
	Jnc	GetDta
	Mov	DX,Offset Alocmsg
	Jmp	Errors

GetDta:	Mov	DX,Offset DTA		;Establish a DTA
	Mov	Byte Ptr LstPath,255
	Mov	AH,1Ah
	Int	21h

	Call	GetParm			;Get command parameters

	Mov	DX,FilePtr		;Find first matching entry
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
	Page
;
;	Exits and error routines

Error4:	Mov	DX,Offset Msg1		;Say NO	FILE(S) FOUND
	Call	PrintS
	Mov	DX,FilePtr		; with filename

Errors:	Mov	AX,CS			;Insure DS
	Mov	DS,AX
	Mov	SP,Stk_Top		;Insure stack
	Call	PrintS			;Error message

Done:	Cmp	Byte Ptr LstPath,255	; Was path changed?
	Je	Done2
Done1:	Mov	AH,3Bh			; Restore target drive path
	Mov	Byte Ptr OldPath,'\'
	Mov	DX,Offset Oldpath
	Int	21h

Done2:	Mov	AH,0Eh			;Restore current disk
	Mov	DL,CurDisk
	Cmp	DL,255			; was it changed?
	Je	Exit
	Int	21h

Exit:	Ret				;Far return to DOS
	Page
;
;	List directory for each	file

ListDir	Proc	Near

	Call	OpenLib			;Access next library
	Jc	Err1

	Call	ReadMst			;Get master DIR entry
	Jc	Err3

	Call	Verify			;Validate master entry
	Jc	Err6

	Call	ReadLib			;Read remainder of directory
	Jc	Err3

	Call	ChkCRC			;Validate directory CRC

	Call	GetDate			;Format file date/time

	Call	Sort			;Sort into name order
	Jmp	Short List1       	; and display directory

;	Error messages

Err3:	Mov	DX,Offset Msg3		;Say I/O error
	Jmp	Short ErrMsg

Err1:	Mov	DX,Offset Msg1		;Say OPEN FAILED
	Jmp	Short ErrMsg

Err6:	Mov	DX,Offset Msg6		;Say INVALID LBR FORMAT

ErrMsg:	Call	PrintS			;Display error message
	Mov	DX,FilePtr		; with filename
	Call	PrintS

Close:	Mov	BX,Handle		;Close library
	Or	BX,BX
	Jz	Closed
	Mov	AH,3Eh
	Int	21h
Closed:	Mov	Handle,0		; indicate closed
	Ret
	Page
;	Display	the titles

List1:	Mov	SI,Offset DTA+30	;Copy filename to heading
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
List6c:	Mov	DX,Offset Header	;Display headings
	Call	PrintS

List7:	Mov	AX,Entries		;Format number of DIR entries
	Mov	DI,Offset NumDir
	Call	Format

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
	Jmp	Short List18

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
	Page
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

ListDir	Endp
	Page
;
;	Use next matching entry for Open

OpenLib	Proc	Near
	Mov	SI,Offset DTA+30	;Move name from	DTA
	Mov	DI,FilePtr		; for OPEN
	Mov	CX,13
Move:	Lodsb
	Stosb
	Cmp	AL,0			; if end of name
	Loopne	Move
	Jcxz	Open
	Rep	Stosb

Open:	Mov	DX,FilePtr		;Open the library
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

	Add	AX,AX			;Calc number of entries
	Add	AX,AX			; four per sector
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
	Mov	AL,'/'
	Stosb				;Add delimiter

	Mov	AX,DX			;Get day part
	And	AX,Mask Dy
	Call	Cnvrt1
	Mov	AL,'/'
	Stosb				;Add delimiter

	Mov	AX,DX			;Get year part
	And	AX,Mask Yr
	Mov	CL,Yr
	Shr	AX,CL
	Add	AL,80
	Jmp	Cnvrt1

;	Format DOS time

FixTime:Mov	AX,DX			;Get hour part
	And	AX,Mask Hh
	Mov	CL,Hh
	Call	Cnvrt
	Mov	AL,':'
	Stosb				;Add delimiter

	Mov	AX,DX			;Get min part
	And	AX,Mask Mm
	Mov	CL,Mm
	Call	Cnvrt
	Mov	AL,':'
	Stosb				;Add delimiter

	Mov	AX,DX			;Get secs part
	And	AX,Mask Xx
	Add	AX,AX
	Jmp	Short Cnvrt1

Cnvrt:	Shr	AX,CL			;Convert to ASCII
Cnvrt1:	Aam
	Or	AX,'00'
	Xchg	AH,AL
	Stosw
	Ret
GetDate	Endp
	Page
;
;	Format CPM date

CPM_Date Proc	Near			;Convert CP/M date
	Push	AX			; DI points to target
	Push	CX			; DX contains CPM date
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

CD4:	Push	AX			;Save year
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

	Mov	AX,DX			;Format day
	Inc	DI
	Call	Cnvrt1

	Pop	AX			;Format year
	Inc	DI
	Call	Cnvrt1

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
	Inc	SI			;Next divisor
	Inc	SI
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
	Page
;
;	Get command operands

GetParm	Proc	Near			;Operand is LBR name
	Mov	DI,Offset FileNm
	Mov	CX,38
	Sub	AX,AX			;Clear filename
	Rep	Stosw			; to zeros
	Mov	AL,Stopper
	Stosb				; and append stopper

	Mov	SI,82h			;Point to command tail
	Mov	DI,Offset FileNm	; and target
	Or	CL,DS:[80h]		;Length of parameters
	Jnz	Copy1
	Jmp	Copy8			; none, list all LBR

Copy1:	Lodsb				;Skip leading blanks
	Cmp	AL,' '			; while copying LBR name
	Loope	Copy1
Copy2:	Stosb				;Copy non-blanks
	Lodsb
	Cmp	AL,0Dh			;End of parameters?
	Je	Copy3			; yes, done
	Cmp	AL,' '			; no, have blank at end?
	Loopne	Copy2			; if not, just copy

; Set new disk from specified drive

Copy3:	Mov	Filend,DI		;Save end of name ptr
	Cmp	FileNm+1,':'		;If a drive is specified,
	Jne	Copy4

	Mov	AH,19h			;Save current disk
	Int	21h
	Mov	CurDisk,AL

	Mov	DL,Byte Ptr FileNm	;Set new current disk
	And	DL,0DFh
	Sub	DL,'A'
	Mov	AH,0Eh
	Int	21h
	Mov	FilePtr,Offset FileNm+2

; Determine if any path specified in command

Copy4:	Mov	SI,FilePtr		;First possible filename char
	Lodsb
	Cmp	AL,0			;Just drive?
	Je	Copy8			; yes, append default fname
	Cmp	AL,'\'			;Was a path specified?
	Je	CopyP
	Cmp	AL,'/'
	Jne	Copy9			; no, see if fname has ext

CopyP:	Mov	AH,47h			; yes, save original path
	Sub	DL,DL			; for target drive
	Mov	SI,Offset Oldpath+1
	Int	21h

; Set new current directory from command's path

Copy5:	Mov	AH,3Bh			;Set new path
	Mov	DX,FilePtr
	Int	21h
	Jnc	Copy7			; if path only
	Mov	SI,Filend		;Have filename after path
	Std
	Mov	CX,SI			;Length so far
	Sub	CX,FilePtr
Copy6:	Lodsb
	Cmp	AL,'\'			;Last path name?
	Loopne  Copy6
	Inc	SI			; yes, mark filename spot
	Mov	Byte Ptr [SI],0		; and reset ASCIIZ path name
	Inc	SI
	Mov	DX,FilePtr
	Mov	FilePtr,SI		;Ptr to filename part
	Mov	AH,3Bh
	Int	21h
	Jmp	Short Copy9		; and check ext
Copy7:
	Mov	SI,Filend		;Filename ptr at
	Mov	FilePtr,SI		; end of path name

;	Append *.LBR if no fname

Copy8:	Cld
	Mov	SI,FilePtr
	Cmp	Byte Ptr [SI],0
	Jne	Copy9
	Mov	DI,Filend		;Append default spec
	Mov	SI,Offset Default	; after path-only name
	Mov	CX,6
	Rep	Movsb
	Jmp	Short CopyC		; all done

;	Append LBR extension if none supplied

Copy9:	Cld
	Mov	SI,FilePtr		;Find any EXT
	Mov	CX,13			; in filename
CopyA:	Lodsb
	Cmp	AL,' '
	Ja	CopyB			; no ext
	Dec	SI
	Mov	Word Ptr [SI],'L.'	; default to .LBR
	Mov	Word Ptr 2[SI],'RB'
	Jmp	Short CopyC

CopyB:	Cmp	AL,'.'			;Found extension?
	Loopne	CopyA			; not yet

CopyC:;	Mov	DX,Offset FileNm
;	Call	PrintS
	Ret
GetParm	Endp

	Subttl	--- SORT Subroutine ---
	Page
;
;	Bubble sort of directory names, CX=number of entries

;	Sort variables

Count2	Dw	0			;Loop counter
First	Dw	0			;Offset to starting entry
Second	Dw	0			;Offset to next entry to comp
Len	Equ	32			;Length of each entry
KeyLen	Equ	11			;Length of key

Sort	Proc	Near			;Nothing fancy here
	Mov	AX,Entries		;Sort into name order
	Mov	DI,A_Buf		;Offset to array

	Dec	AX			; less one as loop limit
	Jz	Sorted			;Only one
	Js	Sorted			; or none
	Mov	Count2,AX		;Save loop limit

Sortit:	Mov	First,DI		;Offset to first entry
	Mov	Second,DI

Sort1:	Mov	DX,Count2		;Save limit count

Sort2:	Mov	SI,First		;First entry to
	Inc	SI
	Mov	DI,Second		; compare to next entry
	Add	DI,Len
	Mov	Second,DI
	Inc	DI
	Mov	CX,KeyLen
	Repe	Cmpsb			;Compare elements
	Jbe	Sort3			; if in order, no swap

Swap:	Mov	DI,Second		; else swap
	Mov	SI,First
	Mov	CX,Len
Xchng:
	Mov	AH,Byte Ptr [SI]
	Mov	AL,Byte Ptr [DI]
	Xor	AH,AL
	Xor	AL,AH
	Xor	AH,AL
	Mov	Byte Ptr [SI],AH
	Stosb
	Inc	SI
	Loop	Xchng

Sort3:	Dec	DX
	Jnz	Sort2
	Dec	Count2
	Jz	Sorted
	Mov	AX,Len			;Bump to next entry
	Add	AX,First		; for next loop
	Mov	First,AX
	Mov	Second,AX
	Jmp	Short Sort1

Sorted:	Ret
Sort	Endp
	Page
Storage	Equ	This Byte
Stackx	Equ	Storage+256		; Local stack end
DTA	Equ	Stackx+4		; Data transfer area
FileNm	Equ	DTA+78			; Requested file name
Oldpath	Equ	FileNm+78		; Target disk original path
LstPath Equ	OldPath+1
DirBuf	Equ	OldPath+78		; 8K directory buffer

Paras	Equ	($-Cseg+10240)/16	; Paragraphs in program
					;  including stack and patch area
Lut	Endp

Cseg	Ends
	End	Lut
