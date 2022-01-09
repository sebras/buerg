	Page	80,132
	Title	- LUU - Update LBR File

	Comment | Version 1.64, March 3, 1985

LUU Command
-----------

Purpose:   Add or replace members in an LU or LAR type library.

Format:    LUU	[d:][path]filename[.ext] filename[.ext]

Remarks:   The library name and at input member file name must
	   be supplied. Only one member name is allowed, so far.

Notes:	   Written for the IBM PC using DOS 2.0 or later.
	   Copyright 1984 Vernon Buerg, for public domain use.

	   LUU duplicates the A(dd) and U(pdate) functions of LU.

----------|

;	Library directory entry description

DirNtry Struc				;LU/LAR directory entries
D_Stat	Db	0			; File status
D_File	Db	'        '              ; File name (FCB format)
D_Ext	Db	'   '                   ; Extension part
D_Ptr	Dw	0			; Offset to data (mod 128)
D_Len	Dw	0			; Length, 128-byte sectors
					; CP/M formatted fields
D_CRC	Dw	0			;  Cyclic Redundancy Check value
D_Cdate Dw	0			;  Create date
D_Udate Dw	0			;  Update date
D_Ctime Dw	0			;  Create time

D_Utime Dw	0			;  Update time
D_Pad	Dw	0,0,0			;  Unused/reserved
DirNtry Ends

;	Equates

Active	Equ	0
Deleted Equ	254
Unused	Equ	255

Dir_Len Equ	Size DirNtry		; Size of a directory entry

CR	Equ	13
LF	Equ	10
Stopper Equ	255			; Ends a PrintS string

MaxDir	Equ	256			; Maximum directory entries
DirSize Equ	Dir_Len * MaxDir	;  and total size
BufSize Equ	12*1024 		; Minimum I/O buffer size

Dater	Record	Yr:7,Mo:4,Dy:5		; Mask for DOS date
Timer	Record	Hh:5,Mm:6,Xx:5		;  and time
	Page
	;
	;   Update an LBR Library file

Cseg	Segment Public Para 'CODE'
	Assume	CS:Cseg,DS:Cseg,ES:Cseg,SS:Cseg
	Org	100h

Luu	Proc	Far
	Push	DS			; Standard entry
	Sub	AX,AX			;  for DOS return
	Push	AX
	Mov	StkTop,SP

	Call	Alloc			; Get buffers

	Call	GetParm 		; Get Library file name

	Call	OpenLbr 		; Open library

	Call	LoadDir 		; Load directory

	Call	Search			; Add or replace member(s)

	Call	CloseLbr		; Close the library

Done:	Mov	DX,Offset EofMsg	; Say "Done"

Error:	Mov	SP,StkTop		; Insure stack is proper
	Call	PrintS			; Display final message

	Ret				; Return to DOS
	Page
;
;	Load entire directory

LoadDir Proc	Near

	Cmp	NumDir,0		;Already loaded by Create?
	Je	Load1
	Ret

Load1:	Mov	DX,MstPtr		;Read master directory entry
	Call	ReadLib 		; of one 32-byte sector

	Mov	BX,MstPtr
	Cmp	Byte Ptr [BX].D_Stat,0	;Active first entry?
	Jne	NotLBR
	Cmp	Byte Ptr [BX].D_Ptr,0	;Index pointer must be zero
	Jne	NotLBR

	Mov	CX,11			;Check name of blanks
	Lea	SI,Byte Ptr [BX].D_File
	Mov	DI,Offset Blanks
	Rep	Cmpsb
	Je	Load2

	Mov	CX,11			;May be ********DIR name
	Lea	SI,Byte Ptr [BX].D_File
	Mov	DI,Offset DirKey
	Rep	Cmpsb
	Jne	NotLBR
	Mov	CL,0			; Indicate LUPC format
	Jmp	Short Load3

NotLBR: Mov	DX,Offset Msg6		; Say not valid format
	Jmp	Errors

Load2:	Mov	CL,1			; Indicate CP/M format in use
	Sub	AX,AX
	Mov	Word Ptr [BX].D_CRC,AX
	Cmp	Word Ptr [BX].D_Cdate,AX
	Jne	Load3			; or original LU format
	Mov	CL,2

Load3:	Mov	Mode,CL 		; Set library format type
Load4:	Mov	AX,Word Ptr [BX].D_Len	; Number of dir sectors
	Add	AX,AX			;  to num entries
	Add	AX,AX
	Dec	AL			; less master entry
	Mov	NumDir,AX
	Mov	CL,5			; Get size of directory
	Shl	AX,CL			;  in bytes

	Mov	CX,AX			; Remaining direc size
	Mov	DX,DirPtr		; Load rest of directory
	Call	ReadLb
	Ret
LoadDir Endp

	Page
;
;	Search for requested file

Search	Proc	Near			; Name is in "MEMBER"

	Mov	DX,Offset MyDTA 	; Establish data xfer area
	Mov	AH,1Ah
	Int	21h

	Call	OpnIn			; Get first file
	Jz	Srch3			; no more files?
	Mov	DX,Offset Version	; member name(s) missing
	Jmp	Error

Srch3:	Mov	BX,DirPtr		; First DIR entry
	Mov	DX,NumDir

Srch5:	Cmp	Byte Ptr [BX].D_Stat,Active
	Jne	Srch7			; entry not active

	Lea	DI,Byte Ptr [BX].D_File
	Mov	SI,Offset Member	; Selected member name
	Mov	CX,11
	Rep	Cmpsb			; found member
	Je	Srch8

Srch7:	Add	BX,Dir_Len		; next entry
	Dec	DX
	Jnz	Srch5

	Call	Add			; Not found, add it
	Jmp	Short Srch9

Srch8:	Call	Replace 		; Matched, replace it

Srch9:	Call	OpenNxt 		; Get next matching file name
	Jz	Srch3
	Ret
Search	Endp
	Page
;
;	Determine the name of the next input file and open it

OpnIn	Proc	Near
	Push	BX

OpenIt1:Call	GetNext 		; Get next member operand,
	Jnz	OpenIt			; set ZF if no more names
	Inc	SI
	Jmp	OpnIn9

OpenIt: Mov	AH,4Eh			; Find first matching entry
	Mov	DX,Offset FileNm
	Sub	CX,CX
	Int	21h
	Jc	Err9			; member not found
	Jmp	OpnIn1

OpenNxt:Push	BX			; get next file
OpnIn0: Mov	AH,4Fh
	Int	21h
	Jc	OpenIt1
	Or	AL,AL			; Any found?
	Jnz	OpenIt1 		; no, try next operand

OpnIn1: Or	AL,AL			; Any found?
	Jnz	OpnIn9			; no, ZF=0

	Mov	SI,Offset MyDTA+30	; Copy found name
	Mov	BX,FilePtr		;  in ASCIIZ format
	Mov	DI,Offset Member	;  and FCB format
	Mov	CX,13
OpnIn2: Lodsb
	Cmp	AL,0			; End of name?
	Je	OpnIn5
	Mov	Byte Ptr [BX],AL
	Inc	BX
	Cmp	AL,'.'                  ; Start of extension?
	Je	OpnIn3
	Stosb
	Jmp	Short OpnIn4

OpnIn3: Mov	AL,' '                  ;  yes, pad fname with blanks
	Rep	Stosb
	Mov	DI,Offset Ext		;  yes, point to ext
	Mov	CL,4
OpnIn4: Loop	OpnIn2
	Jcxz	OpnIn7
OpnIn5: Mov	AL,' '                  ; Pad FCB ext with blanks
	Rep	Stosb
OpnIn7: Mov	DI,BX			; Append ASCIIZ stopper
	Mov	AX,0FF00h		;  to input file name
	Stosw

	Cmp	Word Ptr Ext,'BL'       ; Don't allow LBR as member
	Jne	OpnIn6
	Cmp	Byte Ptr Ext+2,'R'
	Jne	OpnIn6
	Jmp	OpnIn0

OpnIn6: Mov	AX,3D00h		; Open member file for reading
	Mov	DX,Offset FileNm
	Int	21h
	Mov	IHandle,AX
	Jnc	OpnIn8
Err9:	Mov	DX,Offset Msg9		; Open failed
	Call	PrintS
	Mov	DX,Offset FileNm
	Jmp	Error

OpnIn8: Sub	AX,AX			; Indicate file open
OpnIn9: Pop	BX
	Ret
OpnIn	Endp

;
;	Get free directory entry

GetDir	Proc	Near			; Returns BX
	Mov	BX,DirPtr		; First dir entry
	Mov	DX,NumDir		; Number of entries
GetDir1:
	Cmp	Byte Ptr [BX].D_Stat,Unused
	Je	GetDir4 		; not active or deleted

	Add	BX,Dir_Len		; Next directory entry
	Dec	DX			; Number of dir entries
	Jnz	GetDir1 		; more, try next entry
	Cmp	DX,BX			; Indicate no free entries
GetDir4:Ret
GetDir	Endp
	Page
;
;	Replace the requested file

Replace Proc	Near			; BX points to directory entry
	Mov	Action,'R'
	Call	GetSize 		; Get member file sectors

	Cmp	Word Ptr [BX].D_Len,AX	; Same size or smaller?
	Jae	Rep0			;  yes, in place
	Push	AX			; Save number of sectors
	Push	BX			;  and original dir entry
	Call	GetDir			; See if last used member
	Mov	CX,BX
	Pop	BX
	Sub	CX,Dir_Len
	Cmp	BX,CX			; last one?
	Pop	AX			; Get sectors back
	Jne	Rep1			;  no, add to end

Rep0:	Mov	Word Ptr [BX].D_Len,AX	; Change size

	Call	RepDir			; Replace directory entry

	Mov	AX,Word Ptr [BX].D_Ptr	; Get location
	Sub	DX,DX
	Mul	C128			; into bytes
	Xchg	DX,AX
	Mov	CX,AX

	Mov	AL,0
	Call	Lseek1			; Point to original member

	Mov	DX,Offset MsgR		; Say REPLACING
	Call	PrintS
	Mov	DX,Offset FileNm
	Call	PrintS
	Jmp	Add2			; Copy the replacement file

Rep1:	Mov	Byte Ptr [BX].D_Stat,Unused ; Mark original as free
	Call	RepDir			; Replace directory entry
	Mov	DX,Offset MsgU		; Say UPDATING
	Jmp	Short Addit

RepDir:
	Call	GetDate 		; Get Create stamp
RepDir1:
	Push	AX			; Re-write a directory entry
	Push	BX
	Push	CX
	Push	DX

	Mov	DX,BX			; Reposition library
	Sub	DX,MstPtr		;  to dir entry
	Mov	AL,0
	Call	Lseek0
	Call	WriteL			; Rewrite entry
	Mov	Updated,255

	Pop	DX
	Pop	CX
	Pop	BX
	Pop	AX
	Ret
	Page
;
;	Add new member to end of library

Add:	Mov	DX,Offset MsgA		; Say ADDING
	Mov	Action,'A'
Addit:	Call	PrintS
	Mov	DX,Offset FileNm
	Call	PrintS

	Call	GetDir			; Get free dir entry
	Jz	Add1
	Mov	DX,Offset Msg5		; No free entries
	Jmp	Error

Add1:	Mov	SI,Offset Member	; Place name in dir
	Lea	DI,Byte Ptr [BX].D_File
	Mov	CX,11
	Rep	Movsb

	Sub	DX,DX			; Pos lbr to EOF
	Call	Lseek
	Add	AX,127			; Round up size
	Adc	DX,0
	Div	C128			;  make into sector
	Mov	Word Ptr [BX].D_Ptr,AX

	Call	GetSize 		; Get member file sectors
	Mov	Word Ptr [BX].D_Len,AX

Add2:	Mov	AL,0			; Position member to start
	Call	Iseek0

Add3:	Mov	CX,BufLen		; Buffer size
	Call	Read			; Read a block
	Jc	Add7

	Mov	AX,ReadSiz		; Bytes to write
	Add	AX,127			;  rounded up
	Mov	CL,7
	Shr	AX,CL
	Shl	AX,CL
	Mov	CX,AX
	Call	Write			; Write a block

	Jmp	Short Add3

Add7:	Mov	Byte Ptr [BX].D_Stat,0	; Mark active

	Call	RepDir			; Replace directory entry

	Mov	BX,IHandle		; Close input
	Call	Close
	Ret
Replace Endp

	Subttl	--- Read/Write routines
	Page
;
;	Read a directory entry

R_W	Proc	Near
ReadLib:Mov	CX,Dir_Len		; Read a block, length in CX
ReadLb: Mov	BX,LHandle		; DX points to buffer
	Mov	AH,3Fh
	Int	21h
	Jnc	Readl0			; Read okay?
	Jmp	Err2			;  no, say I/O error

Readl0: Or	AX,AX			; Any data read?
	Jnz	Readl9
	Jmp	NotLBR			; EOF unexpected, invalid LBR
Readl9: Ret

;	Read Blocks Subroutine

Read:	Push	BX			; Read next block, length in CX
	Mov	BX,IHandle		; File handle
	Mov	DX,BufPtr
	Mov	AH,3Fh			; Read from file
	Int	21h
	Jc	Err2
	Or	AX,AX			;Any data read?
	Jnz	Read2			; no, send message
	Stc
	Jmp	Short Rexit

Read2:	Mov	ReadSiz,AX		;Save size read
	Sub	CX,AX			; bytes not read
	Jz	Rexit
	Mov	DI,AX
	Add	DI,BufPtr		; byte after read data
	Mov	AL,1Ah			; pad with EOF (1A)
	Rep	Stosb
Rexit:	Pop	BX
	Ret

Err2:	Mov	DX,Offset Msg2		;Say I/O error reading
	Jmp	Error
	Page
;
;	Write a Sector Subroutine

Write:	Push	BX			; Write a sector, length in CX
	Push	DX
	Mov	DX,BufPtr
Write1: Mov	AH,40h			; Write to a file
	Mov	BX,LHandle		; File handle
	Int	21h
	Jc	Err3
	Cmp	AX,CX			; Wrote it?
	Jne	Err4			;  no, full
	Pop	DX
	Jmp	Short Rexit

WriteD: Mov	CX,DirLen		; Re-write entire directory
	Jmp	Short Write2

WriteL: Mov	CX,Dir_Len		; Re-write one dir entry
Write2: Push	BX
	Push	DX
	Mov	DX,BX
	Jmp	Short Write1

Err3:	Mov	DX,Offset Msg3		; Say I/O error writing
	Jmp	Error
Err4:	Mov	DX,Offset Msg4		; Say DISK FULL
	Jmp	Error
R_W	Endp

	Subttl	--- Open or Create Library
	Page
;
;	Open Library Subroutine

OpenLbr Proc	Near			; Open the library
	Mov	DX,Offset LbrName	; LBR file name
	Mov	AX,3D02h		; Open LBR file for updating
	Int	21h
	Jc	Err1			; Open okay?
	Mov	LHandle,AX		;  yes, save handle
	Ret

Err1:	Cmp	AL,3			; Was it found
	Ja	Err7
	Call	Create			;  no, make new one
	Jmp	OpenLbr

Err7:	Mov	DX,Offset Msg7		; Say open failed
Errors: Call	PrintS
	Mov	DX,Offset LbrName
	Jmp	Error
OpenLbr Endp



;	Create Library Subroutine

Create	Proc	Near			;Create output file

Creat0: Mov	DX,Offset AskDir	;Get number of entries
	Call	PrintS
	Mov	AH,0Ah			;Read kybd buffer
	Mov	DX,Offset Reply
	Int	21h
	Mov	CL,Reply+1		;Get reply length
	Sub	CH,CH
	Mov	SI,Offset Reply+2
	Call	ASC2BIN 		; and make it numeric
	Jc	Creat2
	Cmp	AX,MaxDir		; want over 256
	Ja	Creat0
	Mov	NumDir,AX
	Or	AX,AX			; zero to quit?
	Jnz	Creat1
	Jmp	Done

Creat1: Sub	CX,CX			;Normal attribute
	Mov	DX,Offset LbrName	;New file name
	Mov	AH,3Ch			;Create a file
	Int	21h
	Jnc	Creat2
	Mov	DX,Offset Msg8		;Say CREATE failed
	Jmp	Error

Creat2: Mov	LHandle,AX		;Save file handle
	Mov	AX,NumDir
	Add	AX,4			;Round up including master
	And	AX,01FCh		; in fours
	Mov	NumDir,AX
	Mov	DX,AX
	Mov	CL,5			;Get size of directory
	Shl	DX,CL			; in bytes
	Mov	DirLen,DX
	Dec	NumDir			; actual entries
	Mov	CL,2			; into sectors
	Shr	AX,CL
	Mov	BP,AX			; save dir count
	Page
;
;	Clear the new directory entries

	Mov	BX,MstPtr		; First member entry
	Mov	DX,NumDir
	Inc	DX			; Include master entry
	Sub	AL,AL
Creat4: Mov	CX,Dir_Len
	Mov	DI,BX
	Rep	Stosb
	Mov	Byte Ptr [BX].D_Stat,Unused
	Add	BX,Dir_Len
	Dec	DX
	Jnz	Creat4

;	Initialize newly created library

Creat5: Mov	BX,MstPtr		; Initalize master entry
	Mov	Word Ptr [BX].D_Len,BP	; Number of DIR sectors
	Mov	Byte Ptr [BX].D_Stat,Active

	Mov	SI,Offset Blanks	; Master member name
	Lea	DI,Word Ptr [BX].D_File ;  is all blank
	Mov	CX,11
	Rep	Movsb

	Call	LibDate 		; Get LBR create date/time

	Mov	BX,MstPtr		; Format create date/time
	Call	GetDat2

Creat6: Mov	CX,DirLen		;Write all entries
	Mov	BX,MstPtr		; starting with master dir
	Call	WriteD
	Mov	Updated,0

;	Close the library

CloseLbr:
	Cmp	Mode,1			; Is it LU86 format?
	Jne	CloseL			;  no, leave master entry alone
	Cmp	Updated,0		; Any updates?
	Je	CloseL			;  no, skip it
	Call	LibDate 		; Get LBR update date/time

	Mov	BX,MstPtr		; Format update date/time
	Mov	Action,'R'              ;  in master dir entry
	Call	CPM_Dat 		; Get CP/M date
	Call	RepDir1 		; Replace master dir entry

CloseL: Mov	BX,LHandle
Close:	Mov	AH,3Eh			; DOS close handle
	Int	21h
	Ret
Create	Endp


	Subttl	'--- Format original file datestamp'
	Page
;
;	Put original file date/time into directory entry

GetDate Proc	Near			;Determine original date
	Cmp	Mode,2			; Date stamps supported?
	Jne	GetDat1 		; no, leave as zeros
	Ret

GetDat1:
	Call	FilDate 		; Get DOS file date
GetDat2:
	Cmp	Mode,0			; Is it LUPC format?
	Jne	GetDat3 		; no, must be CP/M
	Call	SetDate 		; yes, set ASCII stamps
	Ret
GetDat3:				; Stamps are CP/M format
	Call	CPM_Dat 		; Get days in AX, time in CX
	Ret
GetDate Endp


FilDate Proc	Near			; Return DOS file date
	Push	BX
	Mov	BX,IHandle
	Mov	AX,5700h		; Get input file date/time
	Int	21h			;  in DX:CX
	Pop	BX
	Ret
FilDate Endp


LibDate Proc	Near
	Mov	BX,LHandle		; Get LBR create date/time
	Mov	AX,5700h		;  in DX:CX
	Int	21h
	Ret
LibDate Endp

	Subttl	'--- Convert date to CP/M format'
	Page
CPM_Dat Proc	Near
;	Push	BX			; BX points to dir entry
	Push	CX			; CX contains file time
;	Push	DX			; DX contains DOS-file year
;	Push	AX			; AX returns CP/M days

	Mov	[BX].D_CRC,0		; No CRC value yet

;	Convert DOS-file date to mm/dd/yy values

	Mov	SI,DX			; Get month part
	And	SI,Mask Mo
	Mov	CL,Mo
	Shr	SI,CL

	Mov	BP,DX			; Get day part
	And	BP,Mask Dy

	Mov	DI,DX			; Get year part
	And	DI,Mask Yr
	Mov	CL,Yr
	Shr	DI,CL
;	Add	DI,80			; IBM PC DOS base year

;	Get number of days since Jan 1, 1978

	Cmp	SI,2			; If Month > 2 Then
	Jbe	Cd1
	Sub	SI,3			;      Month=Month-3
	Add	DI,4			;      Year=Year-76
	Jmp	Short Cd2

Cd1:	Add	SI,9			; Else Month=Month+9
	Add	DI,3			;      Year=Year-77

Cd2:	Mov	AX,DI			; Leaps = (1461*Year)\4
	Sub	DX,DX
	Imul	C1461
	Shr	AX,1
	Shr	AX,1
	Mov	CX,AX

Cd3:	Mov	AX,SI			; Days = (153*Month)/5
	Sub	DX,DX
	Imul	C153
	Sub	DX,DX
	Add	AX,4
	Idiv	C5
	Add	AX,CX			; C_Date = Day-671+Leaps+Days
	Add	AX,BP
	Sub	AX,671

Cd4:	Pop	CX			; Recover time
	Cmp	Action,'A'              ; Adding or replacing?
	Je	Cd5
	Mov	[BX].D_Udate,AX 	; Set update stamps
	Mov	[BX].D_Utime,CX
	Ret

Cd5:	Mov	[BX].D_Cdate,AX 	; Set create stamps
	Mov	[BX].D_Ctime,CX
	Ret

C1461	Dw	1461			; Days in 4-years
C5	Dw	5			; Average days per month
C153	Dw	153
CPM_Dat Endp

	Subttl	'--- Convert date/time to ASCII (LUPC) format'
	Page
SetDate Proc	Near			;Place ASCII date/time in entry
	Push	CX			; save time
	Lea	DI,Byte Ptr [BX].D_CRC	; Target for formatted date	file date

	Mov	AX,DX			; Get month part
	And	AX,Mask Mo
	Mov	CL,Mo
	Call	Format
	Mov	AL,'/'
	Stosb				; Add delimiter

	Mov	AX,DX			; Get day part
	And	AX,Mask Dy
	Call	Format1
	Mov	AL,'/'
	Stosb				; Add delimiter

	Mov	AX,DX			; Get year part
	And	AX,Mask Yr
	Mov	CL,Yr
	Add	AX,80*512		; Base date 1980
	Call	Format

	Pop	DX			; Recover file time
	Lea	DI,Byte Ptr [BX].D_Utime

	Mov	AX,DX			; hours part
	And	AX,Mask Hh
	Mov	CL,Hh
	Call	Format
	Mov	AL,':'
	Stosb				; add delimiter

	Mov	AX,DX			; minutes part
	And	AX,Mask Mm
	Mov	CL,Mm
	Call	Format
	Mov	AL,':'
	Stosb				; add delimiter

	Mov	AX,DX			; seconds part
	And	AX,Mask Xx
	Add	AX,AX
	Call	Format1
	Ret

Format: Shr	AX,CL			;Convert binary to ASCII
Format1:Aam
	Or	AX,'00'
	Xchg	AH,AL
	Stosw
	Ret
SetDate Endp

	Subttl	---  Subroutines
	Page
GetSize Proc	Near
	Call	Iseek			; Seek to EOF to get size
	Push	AX
	Shl	AL,1			; Get bytes in last sector
	Shr	AL,1
	Sub	AH,AH
	Cmp	AL,0			; Full sector?
	Je	GetSz1			;  yup, no pad bytes
	Mov	AH,128
	Sub	AH,AL
GetSz1: Mov	Byte Ptr [BX].D_Pad,AH
	Pop	AX

	Add	AX,127			; Round up size to sectors
	Adc	DX,0
	Div	C128
	Ret
GetSize Endp

Lseek	Proc	Near			;Reposition library
	Mov	AL,02h			; to EOF
Lseek0: Sub	CX,CX			; to offset in DX:CX
Lseek1: Push	BX
	Mov	BX,LHandle
	Jmp	Short Iseek1

Iseek:	Mov	AL,02h			; Reposition to EOF
Iseek0: Sub	CX,CX			;  or to beginning
	Sub	DX,DX
	Push	BX
	Mov	BX,IHandle
Iseek1: Mov	AH,42h			; DOS Lseek disk
	Int	21h
	Pop	BX
	Ret
Lseek	Endp

;	Print String - Display a message

PrintS	Proc	Near			;Print string like Int 21h (9)
	Push	BX			;DX points to string
	Push	SI
	Mov	SI,DX
PS1:	Lodsb
	Cmp	AL,0			;Skip zeros
	Je	PS1
	Cmp	AL,255			;String ends in a hex FF
	Je	PS9			; so can print $
	Mov	AH,14			;Use TTY write
	Mov	BX,7
	Int	10h
	Jmp	PS1

PS9:	Pop	SI
	Pop	BX
	Ret
PrintS	Endp
	Page
;
;	Convert an ASCII string to a binary value

ASC2BIN Proc	Near			;ASCII numbers to binary in AX
	Push	DI			; DS:SI has pointer to string
	Push	DX			; CX has length of string

	Sub	DI,DI			; Zero result
	Sub	DX,DX			; Clear for multiplies
Cnvrt1: Lodsb
	Cmp	AL,'0'                  ; valid digit?
	Jb	Cnvrt2
	Cmp	AL,'9'
	Ja	Cnvrt2
	Sub	AL,'0'                  ; digit to binary
	Cbw
	Add	DI,AX
	Dec	CX
	Jz	Cnvrt3
	Mov	AX,DI
	Mul	Ten
	Mov	DI,AX
	Jmp	Cnvrt1

Cnvrt2: Stc				; Invalid arg
	Jmp	Short Cnvrt4

Cnvrt3: Mov	AX,DI			;Save result
	Clc
Cnvrt4: Pop	DX
	Pop	DI
	Ret
ASC2BIN Endp
	Page
;
;	Allocate memory for buffers

Alloc	Proc	Near

	Mov	AH,30h			; Get DOS version
	Int	21h
	Cmp	AL,2			; Insure 2.0 or later
	Jae	Alloc0
	Mov	DX,Offset Sorry
	Jmp	Error

Alloc0: Mov	BX,SP			; Use memory from end of program
	Mov	AX,Offset PgmEnd	; to beginning of stack for buffers
	Sub	BX,AX			; with this many bytes available
	Sub	BX,512			; less a stack size
	Cmp	BX,BufSize+DirSize+256
	Jb	Alloc1			; if not enough

	Mov	MstPtr,AX		; Assign master directory entry
	Add	AX,Dir_Len
	Sub	BX,Dir_Len

	Mov	DirPtr,AX		; Assign directory buffer
	Add	AX,DirSize-Dir_Len	; Bump to I/O buffer
	Sub	BX,DirSize-Dir_Len

	Mov	BufPtr,AX		; Assign I/O buffer
	Mov	CL,7			; Round up to 128-byte sector
	Shr	BX,CL
	Shl	BX,CL
	Mov	BufLen,BX		; and use what's left for it
	Ret

Alloc1: Mov	DX,Offset Msg1		; Say 'Not enough memory'
	Jmp	Error
Alloc	Endp
	Page
;
;	Get Command Tail Operands
;
;	Input:	DS must point to program PSP
;	Output:
;		Carry flag if any errors encountered, message sent
;		LbrName - receives the first operand, library file name
;		FileNm	- receives the second operand, a member name
;		FilePtr - points to the first member name

GetParm Proc	Near			; First operand is LBR name
	Mov	SI,82h			; Second is requested member
	Sub	CX,CX
	Or	CL,DS:[80h]		; Length of command operands
	Jnz	Parm0

Parm_Error:				; Library name missing
	Mov	DX,Offset Version	;  or member name(s) missing
	Jmp	Error			;  so send usage message

Parm0:	Mov	DI,Offset ParmFld	; Save command operands
	Rep	Movsb
	Mov	AL,CR
	Stosb
	Mov	SI,Offset ParmFld
	Mov	CL,DS:[80h]

Parm1:	Lodsb				; Skip leading blanks
	Cmp	AL,' '                  ;  while finding LBR name
	Loope	Parm1

	Mov	DI,Offset LbrName	; Copy library name operand
Parm2:	Stosb
	Lodsb
	Cmp	AL,0Dh			; The library name operand may end
	Je	Parm_Error		; in a blank but not a CR, because
	Cmp	AL,'.'                  ; a CR means there are no filenames
	Je	Parm2a
	Cmp	AL,' '                  ; Copy the first operand and check for
	Loopne	Parm2			; an extension delimiter.

;	Add default LBR extension

	Jcxz	Parm_Error		; If no member list
	Mov	AX,'L.'                 ; If no extension is supplied,
	Stosw				; supply a default of .LBR
	Mov	AX,'RB'
	Stosw
	Jmp	Short Parm2d

;	Copy the library name extension

Parm2a: Stosb
	Lodsb
	Cmp	AL,0Dh
	Je	Parm_Error
	Cmp	AL,' '
	Loopne	Parm2a

Parm2d: Mov	AX,0FF00h		; Append ASCIIZ and print stopper
	Stosw
	Mov	ParmNxt,SI		; Set pointer to next operand
	Clc
	Ret
	Page
;
;	Get pointer to next command operand

GetNext:				; Returns ZF if there's an operand
	Mov	DI,Offset FileNm	; Copy the next operand as a
	Mov	SI,ParmNxt		; member file name
Parm3a: Lodsb
	Cmp	AL,' '                  ; Skip leading blanks
	Loope	Parm3a
	Dec	SI
Parm3:	Lodsb
	Mov	ParmNxt,SI
	Cmp	AL,' '                  ; Multiple member names are separated
	Je	Parm4			; by blanks. The last one ends in a CR.
	Cmp	AL,CR
	Je	Parm4
	Stosb
	Jmp	Short Parm3

Parm4:	Mov	AX,0FF00h		; Append ASCIIZ and print stopper
	Stosw

;	Get pointer to file name part of member name operand

	Mov	SI,DI			; Each member filename may include
	Std				; a drive and/or path names, need to
	Dec	SI			; the address of the filename part
Parm5:	Lodsb
	Cmp	AL,':'                  ; Check for drive
	Je	Parm6
	Cmp	AL,'\'                  ; Check for paths
	Je	Parm6
	Cmp	AL,'/'
	Je	Parm6
	Cmp	SI,Offset Filenm-1
	Ja	Parm5
	Dec	SI
Parm6:	Inc	SI			; Save a pointer to the filename
	Inc	SI
Parm7:	Mov	FilePtr,SI		; part of the member name
	Cld
	Clc
	Cmp	Byte Ptr FileNm,0	; Set ZF to indicate whether
	Ret				; there is a file name

GetParm Endp
	Page
;
;	Error messages

Version Db	'LUU - Version 1.64 - V.Buerg',CR,LF
Msg0	Db	CR,LF,'Usage:  LUU library[.LBR] filename(s)',Stopper
Msg1	Db	CR,LF,'Not enough memory',255
Msg2	Db	CR,LF,'Read error',CR,LF,255
Msg3	Db	CR,LF,'Write error',CR,LF,255
Msg4	Db	CR,LF,'Disk full, last update incomplete',CR,LF,255
Msg5	Db	CR,LF,'Directory is full, no update',CR,LF,255
Msg6	Db	CR,LF,'Invalid LBR format: ',255
Msg7	Db	CR,LF,"Can't open library: ",255
Msg8	Db	CR,LF,'CREATE failed',CR,LF,255
Msg9	Db	CR,LF,'File not found  ',255

EofMsg	Db	CR,LF,'All done!',255
AskDir	Db	CR,LF,'How many directory entries? (3-255,0 to quit)  ',255

Sorry	Db	CR,LF,'Wrong DOS version',255
	Page
Reply	Db	4,0,'    '              ; Reply buffer

Updated Db	0			; Non-zero if changes made

Mode	Db	1			; Directory format:
					;  0 = IBM/PC, LUPC stamps
					;  1 = CP/M stamps
					;  2 = no stamps
Action	Db	'A'                     ; Transaction type: A or R

IHandle Dw	0			; Input file handle
LHandle Dw	0			; Library file handle

NumDir	Dw	0			; Number of directory entries
DirLen	Dw	0			; Length of dir in bytes

FilePtr Dw	0			; Ptr to filename part
ParmNxt Dw	0			; Pointer to next operand

MstPtr	Dw	0			; Offset to master entry
DirPtr	Dw	0			; Offset to directory
BufPtr	Dw	0			; Offset to buffers
BufLen	Dw	0			; Size of I/O buffer
ReadSiz Dw	0			; Bytes read

Ten	Db	10			; Some constants
C128	Dw	128
StkTop	Dw	0

Blanks	Db	13 Dup (' ')            ; Name in old format files
DirKey	Db	'********DIR'           ;  in new format libs

Member	Db	8 Dup (' ')             ; Requested member file
Ext	Db	3 Dup (' '),' ',255

MsgU	Db	CR,LF,'Updating   ',255 ; Cooking messages
MsgR	Db	CR,LF,'Replacing  ',255
MsgA	Db	CR,LF,'Adding     ',255

LbrName Equ	$
ParmFld Equ	LbrName+78		; Member name operands
MyDTA	Equ	ParmFld+132		; DTA for DOS
FileNm	Equ	MyDTA+128		; Requested member files(s)

PgmEnd	Equ	FileNm+80		; Last byte in program file
Luu	Endp

Cseg	Ends
	End	Luu

