	Page	80,132

	Title	LUE - Extract LBR Member

	Comment | Version 1.93, February 22, 1985

LUE Command
-----------

Purpose:   Extract a file (member) from an LU or LAR type library.

Format:    LUE	[d:][path]filename[.ext] filename[.ext]

Remarks:   The library name must be supplied. If the member file
	   name is omitted, all files are extracted.

Notes:	   Written for the IBM PC using DOS 2.0 or later.
	   Copyright 1984 Vernon Buerg, for public domain use.

	   LUE duplicates the A and E function of LU. The advantages
	   of LUE are:
		- smaller, so a copy can be kept on the "system" disk
		- faster, mucho
		- handles paths and wildcards.
		- retains input file or member date/time

	   1.7 updates:
		- checks for CRC in bytes 16-17
		- allocate more memory for buffers, up to 60K
	   1.8 updates:
		- extracts members in LU86 format
	   1.9 updates:
		- default library extension to LBR
		- allow multiple filenames on command line

----------|

DirNtry Struc				;LU/LAR directory entries
D_Stat	Db	0			;File status
D_File	Db	8 Dup (' ')             ;File name (FCB format)
D_Ext	Db	3 Dup (' ')             ;Extension part
D_Ptr	Dw	0			;Offset to data (mod 128)
D_Len	Dw	0			;Length, 128-byte sectors

D_CRC	Dw	0			;CRC check bytes
D_Cdate Dw	0			;Create date
D_Udate Dw	0			;Update date
D_Ctime Dw	0			;Create time
D_Utime Dw	0			;Update time
D_Pad	Dw	0,0,0			;Pad bytes in last block
DirNtry Ends
	Page
;
;	Extract an LU member file

Cseg	Segment Public Para 'CODE'
	Assume	CS:Cseg,DS:Cseg,ES:Cseg,SS:Cseg
	Org	100h

Lue	Proc	Far
	Lea	SP,Stackx		; Use local stack
	Push	DS			; Standard entry
	Sub	AX,AX			;  for DOS return
	Push	AX
	Mov	StkTop,SP		; Save stack ptr for return

	Call	ChkVer			; Check DOS version

	Call	Alloc			; Get buffers

	Call	GetParm 		; Get LBR and file name

	Call	OpenLbr 		; Access library

	Call	LoadDir 		; Load directory

	Call	Search			; Find and extract file(s)

	Call	CloseLbr		; Final close

	Mov	DX,Offset EofMsg
Error:	Mov	AX,CS			;Insure DS
	Mov	DS,AX
	Mov	SP,StkTop		;Insure stack is proper
	Call	PrintS			;Display a message

	Ret				;Return to DOS
	Page
;
;	Messages, Constants, and Work Areas

Active	Equ	0
Deleted Equ	254
Unused	Equ	255

Dir_Len Equ	Size DirNtry
Sector	Equ	128			; Logical sector size

MaxPara Equ	(60*1024)/16		; Maximum buffer size
MinPara Equ	(12*1024)/16		; Minumum buffer size

CR	Equ	13
LF	Equ	10
Stopper Equ	255			; Ends message text

Mode	Db	0			;Library format
;	   01 = ***DIR format	02 = CRC included
;	   04 = LU86 format	08 = CRC invalid

IHandle Dw	0			;Input file handle
OHandle Dw	0			;Output file handle
SecSize Dw	Sector
BufSize Dw	0			;Block size to use

BufSec	Dw	0			;Sectors in a block
S_Dir	Dw	0			;Addr of DIR segment
S_Buf	Dw	0			;Addr of buffer segment

StkTop	Dw	0
ParmNxt Dw	0			; Pointer to next filename operand
FilePtr Dw	0			; Pointer to current filename
FileNm	Db	13 Dup (0)		; File name from command line
LbrPtr	Dw	Offset LbrName		; Offset to file name part

Entries Dw	0			; Number of directory entries
Counter Dw	0			;  for search loop
NumSecs Dw	0			; Number of data sectors
DirPtr	Dw	0			; Points to next dir entry
LenDir	Dw	0			; Total directory size

Blanks	Db	13 Dup (' ')            ; Name in old format files
DirKey	Db	'********DIR'           ;  in new format libs
Year	Dw	0

Msg10	Db	CR,LF,'Requested member file not found  '
Member	Db	8 Dup (' ')             ;Requested member file
Ext	Db	3 Dup (' '),0,255

MsgE	Db	CR,LF,'Extracting  '
NewName Db	13 Dup (0),255,' - from ',Stopper

;
;	Error messages

Msg2	Db	CR,LF,'I/O error reading',CR,LF,255
Msg7	Db	CR,LF,'LSEEK failed',CR,LF,255
Msg8	Db	CR,LF,'CREATE failed for ',255
EofMsg	Db	CR,LF,'End of file',CR,LF,255
	Page
;
;	Insure Usable DOS version

ChkVer	Proc	Near
	Mov	DX,Offset Version	; Show current program version
	Call	PrintS

	Mov	AH,30h			; Get DOS version
	Int	21h
	Cmp	AL,2			; Insure 2.0 or later
	Jb	VerBad
	Ret

VerBad: Mov	DX,Offset Sorry
	Jmp	Error

Sorry	Db	CR,LF,'Sorry, PC DOS Version 2 required',CR,LF,255
Version Db	'LUE - Version 1.92 - V.Buerg',CR,LF,Stopper
ChkVer	Endp
	Page
;
;	Allocate directory and I/O buffer

Alloc	Proc	Near
	Mov	BX,Paras_C		;Add up program size
	Mov	AH,4Ah			;Shrink memory
	Int	21h

Alloc1: Mov	BX,MaxPara		;Maximum memory requested
	Mov	AH,48h
	Int	21h
	Jc	Alloc1			;Get what there is

	Cmp	BX,MinPara		;Have enough?
	Jb	Alloc6
	Mov	S_Dir,AX		;Set directory segment

	Mov	CX,512			;Paras in DIR
	Add	AX,CX			;Bump over 8k
	Mov	S_Buf,AX		; as I/O buffer
	Sub	BX,CX			;Paras in buffer
	Mov	CL,3			; into sectors
	Shr	BX,CL
	Mov	BufSec,BX

	Mov	AX,CS			; Get offset to directory
	Mov	DX,S_Dir		;  rather than use segment addresses
	Sub	DX,AX
	Mov	CL,4
	Shl	DX,CL
	Mov	S_Dir,DX
	Mov	DirPtr,DX
	Ret

Alloc6: Mov	DX,Offset AlocMsg	;Insufficient memory
	Jmp	Error

AlocMsg Db	CR,LF,'Insufficient memory',255
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
	Jmp	Parm_Error		; Library name missing

Parm0:	Mov	DI,Offset ParmFld	; Save command operands
	Rep	Movsb
	Mov	CX,129			;  and pad with CRs
	Sub	CL,DS:[80h]
	Mov	AL,CR
	Rep	Stosb

	Mov	SI,Offset ParmFld	; Point to operands
	Mov	CL,DS:[80h]		; and get length

Parm1:	Lodsb				; Skip leading blanks
	Cmp	AL,' '                  ; while Parming LBR name
	Loope	Parm1

	Mov	DI,Offset LbrName	; Copy library name operand
Parm2:	Stosb
	Lodsb
	Cmp	AL,0Dh			; The library name operand may end
	Je	Parm20			; in a blank but not a CR, because
	Cmp	AL,'.'                  ; a CR means there are no filenames
	Je	Parm2a
	Cmp	AL,' '                  ; Copy the first operand and check for
	Loopne	Parm2			; an extension delimiter.
	Jcxz	Parm_Error
Parm20:
        Mov	AX,'L.'                 ; If no extension is supplied,
	Stosw				; supply a default of .LBR
	Mov	AX,'RB'
	Stosw
	Jmp	Short Parm2d

Parm2a: Stosb				; Copy the extension
	Lodsb
	Cmp	AL,0Dh			; End of lbr name?
	Je	Parm2d
	Cmp	AL,' '
	Loopne	Parm2a

Parm2d: Mov	AX,0FF00h		; Append ASCIIZ and print stopper
	Stosw
Parm2e: Mov	ParmNxt,SI		; Set pointer to next operand

	Mov	SI,DI			; Look for path or drive
	Sub	SI,2
	Mov	CX,SI
	Sub	CX,Offset LbrName
	Std
Parm23: Lodsb
	Cmp	AL,':'                  ; drive specifier?
	Je	Parm24			;  yes, may be start of file name part
	Cmp	AL,'\'                  ; path specifier?
	Je	Parm24
	Loop	Parm23
	Mov	SI,Offset LbrName	; Simple filename
	Jmp	Short Parm25

Parm24:	Add	SI,2
Parm25: Mov	LbrPtr,SI		;  followed by a filename
	Cld
	Clc
	Ret

Parm_Error:				; Library name missing
	Mov	DX,Offset Usage 	; or member name(s) missing
	Jmp	Error			; Send usage message

Usage	Db	CR,LF,'Usage:  LUE  library[.LBR]  filename(s)',CR,LF,Stopper
GetParm Endp
	Page
;
;	Open the Library

OpenLbr Proc	Near			;Open the library
	Mov	DX,Offset MyDta 	; Set local data transfer area
	Mov	AH,1Ah
	Int	21h

	Mov	AH,4Eh			; Find first matching file
	Mov	DX,Offset LbrName
	Sub	CX,CX
	Int	21h
	Jc	Error9			; Library file not found

	Mov	CX,13			; Copy first file name
	Mov	SI,Offset MyDta+30
	Mov	DI,LbrPtr
Openl1: Lodsb				; Copy until null found
	Stosb
	Cmp	AL,0
	Loopne	Openl1
	Mov	AL,Stopper
	Stosb

	Mov	AX,3D00h		; Open library file for reading
	Mov	DX,Offset LbrName
	Int	21h
	Jc	Error1			; Library failed to open
	Mov	IHandle,AX		; yes, save handle
	Mov	DX,Offset MsgU		; Show name of library in use
	Call	PrintS
	Mov	DX,Offset LbrName
	Call	PrintS
	Ret				; and return

Error9: Mov	DX,Offset Msg9		; Say LIBRARY not found
	Jmp	Short Errorl

Error1: Mov	DX,Offset Msg1		; Say OPEN FAILED
Errorl: Call	PrintS
	Mov	DX,Offset LbrName	;  and add file name
	Jmp	Error

Msg9	Db	CR,LF,'Library not found: ',Stopper
Msg1	Db	CR,LF,'Unable to open:',Stopper
MsgU	Db	CR,LF,'Using: ',Stopper
OpenLbr Endp
	Page
;
;	Get pointer to next command operand

GetNext Proc	Near			; Returns ZF if there's an operand
	Mov	Filenm,0
	Mov	CX,14
	Mov	DI,Offset FileNm	; Copy the next operand as a
	Mov	SI,ParmNxt		; member file name
	Cmp	Byte Ptr [SI],CR	; No more operands?
	Je	Parm7
Parm3a: Lodsb
	Cmp	AL,' '                  ; Skip leading blanks
	Loope	Parm3a
	Dec	SI
Parm3:	Mov	ParmNxt,SI
	Lodsb
	Cmp	AL,' '                  ; Multiple member names are separated
	Je	Parm4			; by blanks. The last one ends in a CR.
	Cmp	AL,CR
	Je	Parm4
	Stosb
	Loop	Parm3

Parm4:	Mov	AX,0FF00h		; Append ASCIIZ and print stopper
	Stosw
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

GetNext Endp
	Page
;
;	Load entire directory into memory

LoadDir Proc	Near

	Call	ReadMst 		;Get master DIR entry
	Jnc	Load2
	Mov	DX,Offset Msg3		;Say I/O ERROR
	Jmp	Errmsg

Load2:	Call	Verify			;Validate master entry
	Jnc	Load3
	Mov	DX,Offset Msg6		;Say INVALID LBR FORMAT
	Jmp	Errmsg

Load3:	Call	ReadLib 		;Read remainder of directory
	Jnc	Load4
	Mov	DX,Offset Msg3
	Jmp	ErrMsg

Load4:	Call	ChkCRC			;Validate directory CRC
	Test	Mode,8			; is it okay?
	Jz	Load5			; yup
	Mov	DX,Offset CRC_Bad
	Call	PrintS

Load5:	Ret

ErrMsg: Call	PrintS			;Display error message
	Mov	DX,Offset LbrName
	Jmp	Error

Msg3	Db	CR,LF,'I/O error writing',CR,LF,Stopper
Msg6	Db	CR,LF,'Invalid LBR format: ',Stopper
CRC_Bad Db	CR,LF,'Directory CRC invalid',CR,LF,Stopper
LoadDir Endp
	Page
;
;	Search for requested file

Search	Proc	Near			; First member from FilePtr

	Call	GetNext 		; Any members specified?
	Jz	Search0 		;  no, extract all members
	Call	Fcbname 		;  yes, change name to FCB format

Search0:
	Mov	AX,S_Dir		; Offset to DIR in memory
	Add	AX,Dir_Len		;  bump over master entry
	Mov	DirPtr,AX
	Mov	AX,Entries		; Reset directory entries counter
	Mov	Counter,AX

Search1:
	Mov	BX,DirPtr		;Point to current entry

	Cmp	[BX].D_Stat,Deleted	;Entry deleted?
	Je	Search2 		; yes, skip it

	Cmp	[BX].D_Stat,Active	;Is entry in use?
	Jne	Search2 		; no, skip it

	Cmp	Member,' '              ; Want all files?
	Je	Search3 		;  yes, extract it

	Lea	DI,[BX].D_File-1	; Directory file name
	Mov	SI,Offset Member	; Selected member name
	Mov	CX,11
Search7:Lodsb
	Inc	DI
	Cmp	AL,'?'                  ; Wildcard?
	Je	Search5 		;  yup, consider a match
	Cmp	AL,Byte Ptr [DI]
	Jne	Search2
Search5:Loop	Search7 		; No match

Search3:Call	Extract 		; Matched, extract it

Search2:Add	DirPtr,Size DirNtry	; Next directory entry
	Dec	Counter 		; Number of dir entries
	Jnz	Search1 		; not found, try next entry
	Cmp	NewName,0		; Extracted any files?
	Jne	Search4 		;  yes, normal exit
	Mov	DX,Offset Msg10 	;  no, say file not found
	Jmp	Error

Search4:
	Call	GetNext 		; Any more to select?
	Jz	Search9 		;  no, done
	Call	FcbName
	Jmp	Search0 		;  yes, all again

Search9:
	Ret
Search	Endp

	Page
;
;	Extract the requested file

Extract Proc	Near			;BX points to directory entry

	Mov	AX,[BX].D_Len		;Number of sectors
	Mov	NumSecs,AX
	Mov	AX,[BX].D_Ptr		;Get offset to data
	Mul	SecSize
	Mov	CX,DX			; in CX:DX for LSEEK
	Mov	DX,AX

	Call	Lseek			;Reposition input

	Call	FixName 		;Format FCB file name

	Call	Create			;Create output file

	Mov	DX,Offset MsgE		;Say extracting
	Call	PrintS

Ext3:	Mov	AX,NumSecs		;Total data sectors
	Cmp	AX,BufSec		;Will fit in one buffer?
	Jbe	Ext4			; yes, just one r/w
	Mov	AX,BufSec		; no, set max size to read

Ext4:	Mul	SecSize 		;Sectors*size = bytes to read
	Mov	BufSize,AX

	Call	Read			;Read a block

	Mov	AX,BufSec
	Cmp	NumSecs,AX		;Last block?
	Ja	Ext6			; no, full block
	Test	Mode,4			;LU86 format?
	Jz	Ext6			; no, use entire size
	Mov	DL,Byte Ptr [BX].D_Pad	; yes, less pad
	Sub	DH,DH
	Sub	BufSize,DX

Ext6:	Call	Write			;Write a block

	Mov	AX,BufSec
	Sub	NumSecs,AX		;Get number of sectors left
	Js	Ext7			; no more, return
	Jnz	Ext3			; more, read next block

Ext7:	Call	GetDate 		;Original member date

	Call	SetDate 		; as new file date

	Call	CloseO			;Close output

	Ret
Extract Endp

	Subttl	---  Subroutines
	Page
;
;	Read a Sector Subroutine

Read	Proc	Near			;Read a sector
	Push	BX
	Mov	BX,IHandle		;File handle
	Mov	CX,BufSize		;Number of bytes
	Mov	DX,S_Buf
	Push	DS
	Mov	DS,DX
	Sub	DX,DX
	Mov	AH,3Fh			;Read from file
	Int	21h
	Pop	DS
	Jc	Err2
	Or	AX,AX			;Any data read?
	Jz	Err2			; no, send message
	Pop	BX
	Ret
Err2:	Mov	DX,Offset Msg2		;Say I/O error reading
	Jmp	Error
Read	Endp

;
;	 Write a Sector Subroutine

Write	Proc	Near			;Write a sector
	Push	BX
	Mov	BX,OHandle		;File handle
	Mov	CX,BufSize		;Bytes to write
	Push	DS
	Mov	DX,S_Buf
	Mov	DS,DX
	Sub	DX,DX
	Mov	AH,40h			;Write to a file
	Int	21h
	Pop	DS
	Jc	Err3
	Pop	BX
	Ret
Err3:	Mov	DX,Offset Msg3		;Say I/O error writing
	Jmp	Error
Write	Endp

;
;	Create File Subroutine

Create	Proc	Near			;Create output file
	Sub	CX,CX			;Normal attribute
	Mov	DX,Offset NewName	;New file name
	Mov	AH,3Ch			;Create a file
	Int	21h
	Jc	Err8
	Mov	OHandle,AX		;Save file handle
	Ret				; and return
Err8:	Mov	DX,Offset Msg8		;Say CREATE failed
	Call	PrintS
	Mov	DX,Offset NewName
	Jmp	Error
Create	Endp

;
;	Position File Subroutine

Lseek	Proc	Near
	Push	BX
	Mov	AX,4200h		;Reposition to member data
	Mov	BX,IHandle
	Int	21h			; pointed to by CX:DX
	Jc	Err7
	Pop	BX
	Ret
Err7:	Mov	DX,Offset Msg7		;Say LSEEK FAILED
	Jmp	Error
Lseek	Endp

;
;	Close file handle

CloseLbr Proc	Near			;Close input (library)
	Push	BX
	Mov	BX,Ihandle
	Mov	AH,3Eh
	Int	21h
	Pop	BX
	Ret
CloseLbr Endp

CloseO	Proc	Near			;Close output
	Push	BX
	Mov	BX,OHandle
	Mov	AH,3Eh
	Int	21h
	Pop	BX
	Ret
CloseO	Endp

	Page
;
;	Get original member/file date/time

GetDate Proc	Near			;Determine original date
	Push	BX
	Test	Mode,5			;Date in directory?
	Jz	GetDat1 		; no, use LBR file date
	Test	Mode,1			;ASCII stamps?
	Jnz	GetDat2 		; no, maybe LU86 format

	Mov	CX,Word Ptr [BX].D_Utime
	Mov	DX,Word Ptr [BX].D_Udate
	Or	CX,CX			;Any update time?
	Jnz	GetDat3
	Mov	CX,Word Ptr [BX].D_Ctime
	Mov	DX,Word Ptr [BX].D_Cdate
GetDat3:Call	CPM_Date
	Pop	BX
	Ret

;	Convert ASCII date/time to DOS date format

GetDat2:Sub	Byte Ptr [BX].D_Ctime,'8' ;Adjust year
	Mov	AX,Word Ptr [BX].D_Ctime
	Call	Cnvrt
	Mov	DH,AL
	Shl	DH,1

	Mov	AX,Word Ptr [BX].D_CRC	; Month
	Call	Cnvrt
	Mov	DL,AL
	Mov	CL,5
	Shl	DL,CL
	Mov	CL,3
	Shr	AL,CL
	Or	DH,AL

	Mov	AX,Word Ptr [BX].D_CRC+3	; Day
	Call	Cnvrt
	Or	DL,AL
	Push	DX

	Mov	AX,Word Ptr [BX].D_Utime	; Hour
	Call	Cnvrt
	Mov	CL,3
	Shl	AL,CL
	Mov	DH,AL

	Mov	AX,Word Ptr [BX].D_Utime+3	; Minute
	Call	Cnvrt
	Mov	DL,AL
	Mov	CL,5
	Shl	DL,CL
	Mov	CL,3
	Shr	AL,CL
	Or	DH,AL

	Mov	AX,Word Ptr [BX].D_Utime+6	; Second
	Call	Cnvrt
	Or	DL,AL
	Mov	CX,DX
	Pop	DX
	Pop	BX
	Ret

GetDat1:
	Mov	BX,IHandle
	Mov	AX,5700h		;Get input file date/time
	Int	21h			; in DX:CX
	Pop	BX
	Ret
GetDate Endp
	Page
;
;	Set output file date/time

SetDate Proc	Near			;Set output date/time
	Push	BX			; from DX:CX
	Mov	BX,OHandle
	Mov	AX,5701h		;Change output file date
	Int	21h
	Pop	BX
	Ret
SetDate Endp


Cnvrt	Proc	Near			;Convert ASCII to binary
	Xchg	AH,AL
	And	AH,0Fh
	And	AL,0Fh
	Aad
	Ret
Cnvrt	Endp
	Page
;
;	Convert CPM date

CPM_Date Proc	Near			;Convert CP/M date
	Push	AX			; to DOS format in DX
	Push	BX
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

CD4:	Mov	Year,AX 		;Save year

	Mov	SI,Offset Days		; point to days/month
	Sub	AX,AX
	Sub	BX,BX
	Mov	BL,1			; month number
CD5:	Lodsb
	Sub	DX,AX			; days into month
	Jle	CD6			; within month
	Inc	BL
	Jmp	Short CD5

CD6:	Add	DX,AX
	Mov	AX,Year 		;Combine into DOS format
	Sub	AX,80
	Mov	CL,9
	Shl	AX,CL
	Mov	CL,5
	Shl	BX,CL
	Add	AX,BX			; year and month
	Add	DX,AX			; and day

	Pop	SI
	Pop	CX
	Pop	BX
	Pop	AX
	Ret

Days	Db	31,28,31,30,31,30,31,31,30,31,30,31
OneYear Equ	365			;Days in normal year
CPM_Date Endp
	Page
;
;	Format new file name

FixName Proc	Near
	Mov	DI,Offset NewName	;Clear target name
	Mov	SI,Offset Blanks
	Mov	CX,12
	Rep	Movsb
	Lea	SI,[BX].D_File		;Must convert FCB name format
	Mov	DI,Offset NewName	; to ASCIIZ format for Int 21
	Mov	CX,8
Fix5:	Lodsb				;Copy name part
	Cmp	AL,' '
	Je	Fix7
	Stosb
	Loop	Fix5

Fix7:	Cmp	Byte Ptr [BX].D_Ext,' '
	Je	Fix9			;If not extension
	Mov	AL,'.'                  ;Otherwise, dlimit the parts
	Stosb
	Mov	CX,3
	Lea	SI,[BX].D_Ext		;Extension part in dir name
Fix8:	Lodsb
	Cmp	AL,' '                  ;Copy non-blank chars
	Je	Fix9
	Stosb
	Loop	Fix8
Fix9:	Mov	AL,0			;Final ASCIIZ stopper
	Stosb
	Ret
FixName Endp

;
;	Change filename to FCB format

FcbName Proc	Near
	Mov	SI,Offset Blanks	; Clear target MEMBER field
	Mov	DI,Offset Member
	Mov	CX,11
	Rep	Movsb

	Mov	SI,Offset FileNm	; Reformat to FCB style
	Mov	DI,Offset Member
	Mov	CX,9
Fcbnm1: Lodsb				; Next filename char
	Cmp	AL,'a'                  ; Insure in upper case
	Jb	FcbNm2
	Cmp	AL,'z'
	Ja	FcbNm2
	Sub	AL,32			; Make it upper case
FcbNm2: Cmp	AL,'.'
	Je	Fcbnm3
	Cmp	AL,'*'			; Wildcard?
	Je	FcbNm8			;  yes, expand it
	Cmp	AL,0			; End of ASCIIZ name?
	Je	FcbNm7
	Stosb				; Copy name part
	Loop	Fcbnm1
FcbNm7:	Jmp	Short Fcbnm9		; If no extension

FcbNm8:	Mov	AL,'?'			; Expand * wildcard
	Rep	Stosb
	Lodsb
	Cmp	AL,'.'			; Is there one?
	Jne	FcbNm9			;  no, have it all

Fcbnm3: Mov	DI,Offset Ext		; Copy extension
	Mov	CX,3
Fcbnm4: Lodsb				; Copy extension
	Cmp	AL,'a'                  ; Insure in upper case
	Jb	FcbNm5
	Cmp	AL,'z'
	Ja	FcbNm5
	Sub	AL,32			; Make it upper case
FcbNm5: Cmp	AL,'*'			; Have wildcard?
	Je	FcbNm6			;  yes, expand it
	Cmp	AL,0			; End of ASCIIZ name?
	Je	FcbNm9
	Stosb
	Loop	Fcbnm4
	Jmp	Short FcbNm9

FcbNm6:	Mov	AL,'?'			; Expand ext wildcards
	Rep	Stosb
Fcbnm9: Ret
FcbName Endp
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
	Cmp	AL,255			;String ends in a hex FF
	Je	PS9			; so can print $
	Mov	AH,2			;Use std output device
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
;	Build directory in memory

ReadMst Proc	Near
	Mov	BX,Ihandle		;Read master directory entry
	Mov	CX,32			; first 32-byte record
	Mov	DX,S_Dir
	Mov	AH,3Fh
	Int	21h
	Jc	Error3
	Cmp	AX,CX			;Got all of it?
	Jne	Error3
	Ret

ReadLib:				;Read remaining entries
	Mov	BX,S_Dir
	Mov	AX,Word Ptr [BX].D_Len	;Sectors for direc.
	Sub	DX,DX

	Shl	AX,1			;Calc number of entries
	Shl	AX,1			; four per sector
	Dec	AX			; less master entry
	Mov	Entries,AX

	Mov	CL,5			;Calc size remaining
	Shl	AX,CL
	Mov	CX,AX
	Mov	LenDir,CX		;Save length
	Add	LenDir,Dir_Len		; of entire directory

	Mov	BX,IHandle		;Read rest of directory
	Mov	DX,S_Dir
	Add	DX,Dir_Len
	Mov	AH,3Fh
	Int	21h
	Jc	Error3
	Cmp	AX,CX			;Got all of it?
	Jne	Error3
	Ret

Error3: Clc
	Ret
ReadMst Endp
	Page
;
;	Validate master directory entry

Verify	Proc	Near
	Mov	BX,S_Dir
	Sub	AX,AX
	Cmp	Byte Ptr [BX].D_Stat,AL ;Active first entry?
	Jne	NotLBR
	Cmp	Word Ptr [BX].D_Ptr,AX	;Valid index pointer?
	Jne	NotLBR

	Mov	Mode,AL 		;Init LBR type and

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
	Jmp	Short Ver9

Ver4:	Mov	CX,11			;May be new format
	Lea	SI,Byte Ptr [BX].D_File
	Mov	DI,Offset DirKey
	Repe	Cmpsb
	Jne	NotLBR
	Mov	Mode,1			;Indicate ***DIR format

Ver9:	Clc				;Return CD=0
	Ret

NotLBR: Stc				;or CF=1 if not LBR
	Ret
Verify	Endp
	Page
;
;	Check CRC for directory

ChkCRC	Proc	Near
	And	Mode,0FFh-8		;Clear error indication
	Test	Mode,2			;LU86 CRC included?
	Jz	ChkCRC9 		; no, skip it
	Mov	SI,S_Dir		;Calculate directory CRC
	Mov	BX,SI
	Mov	CX,LenDir
	Mov	DX,Word Ptr [BX].D_CRC	;Save original CRC
	Or	DX,DX			; any used?
	Jz	ChkCRC9 		; nope, skip check
	Mov	Word Ptr [BX].D_CRC,0

	Call	GetCRC			;CRC for directory block
	Call	UpdCRC			; and for end-of-block

	Mov	Word Ptr [BX].D_CRC,DX
	Cmp	AX,DX			;CRC correct?
	Je	ChkCRC9
	Or	Mode,8			; no, indicate error
ChkCRC9:Ret
ChkCRC	Endp


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

Lue	Endp

Storage Equ	This Byte
Stackx	Equ	Storage+256		; Local stack end
ParmFld Equ	Stackx+4		; Command line operands
MyDta	Equ	ParmFld+128		; Disk data transfer area
LbrName Equ	MyDta+48
WorkEnd Equ	LbrName+77

Paras_C Equ	(WorkEnd-Cseg+2048)/16	      ; Paragraphs in program and stack

Cseg	Ends

	End	Lue
