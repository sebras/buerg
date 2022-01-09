Title	AUTODATE --- Display and reset Date and	Time
	Page	63,132
;=====================================================================
; Name:	    AUTODATE, automatic	date routine.
; Function: Set	the date and time from user or file input.
; Input:    1) after re-boot, the date and time	are read
;	       from "AUTODATE.DAT",
;	    2) otherwise, DOS functions	return current date and	time.
; Output:   1) the date	and time are set via DOS function calls,
;	    2) the date	and time are saved in file "AUTODATE.DAT".
; Notes:
;	Written for the IBM PC by Vernon Buerg, October 1983,
;	and is supplied for public domain use.
;	Revised 01-01-84 to fix some bugs.
;=====================================================================
;
Cseg	Segment	Para Public 'CODE'
	Assume	CS:Cseg,DS:Cseg,ES:Cseg
	Org	100h
Autodate	Proc	Far
	Push	DS			;save for linkage
	Xor	AX,AX			;clear for return
	Push	AX			;put in	stack

	Push	DS			;Modify	diskette parameters
	Mov	DS,AX			;Offset	into disk table
	Lds	DI,Dword Ptr DS:78h	;Addr of disk table
	Mov	Byte Ptr [DI],239	;Modify	step rate
	Mov	Byte Ptr [DI+2],80	;And motor stop	delay
	Int	13h			;Reset diskette	system
	Pop	DS

	Call	Open			;open for input/output

	Call	Getdate			;get current date

; If the current date is 01-01-1980, power was turned off

	Mov	SI,Offset Ipldate	;date if new boot
	Mov	CX,10			; its length
	Mov	DI,Offset Month		;the current date
	Rep	Cmpsb
	Jne	Print1			;no, display date/time

	Call	Read			;Read DAT file

	Jmp	Print2			;now prompt

Print1:	Call	Gettime			;current time if not read

Print2:	Mov	DX,Offset Pr_date	;prompt	for date
	Lea	BX,Month		;where to reply
	Call	Console			;Read the DATE

	Call	Setdate			;Set the date

	Mov	DX,Offset Pr_time	;prompt	for TIME
	Lea	BX,Hour			;overlay with reply
	Call	Console			;Read the TIME

	Call	Settime			;Set the time
	Page

;	 Re-write Date/Time Records

	Mov	AX,0D0Ah		;End-of-record
	Mov	Word Ptr End_date,AX
	Mov	Word Ptr End_time,AX

	Sub	CX,CX			;new file offset of zero
	Sub	DX,DX
	Mov	AL,0			;to use	CX:DX offset
	Mov	BX,Handle		;supply	file handle
	Mov	AH,42h			;To move file pointer
	Int	21h

	Call	Write			;Re-write DATE and TIME

	Mov	AH,3Eh			;CLOSE the file
	Mov	BX,Handle
	Int	21h
	Ret
	Page

;	 GET CURRENT DATE
;
Getdate	Proc	Near
	Push	AX
	Push	CX
	Push	DX
	Mov	AH,2Ah			;DOS DATE function
	Int	21h

	Mov	AX,CX			;Get Year(19xx)
	Sub	AX,1900
	Aam
	Xchg	AL,AH
	Or	Year,AX
	Mov	AL,DH			;get month
	Aam
	Xchg	AL,AH
	Or	Month,AX
	Mov	AL,DL			;get day
	Aam
	Xchg	AL,AH
	Or	Day,AX
	Pop	DX
	Pop	CX
	Pop	AX
	Ret
Getdate	Endp
	Page

;	 GET CURRENT TIME

Gettime	Proc	Near
	Push	AX
	Push	CX
	Push	DX
	Mov	AH,2Ch			;DOS time function
	Int	21h

	Mov	AL,CH			;get hours
	Aam
	Xchg	AL,AH
	Or	Hour,AX
	Mov	AL,CL			;get minutes
	Aam
	Xchg	AL,AH
	Or	Minute,AX
	Mov	AL,DH			;get seconds
	Aam
	Xchg	AL,AH
	Or	Second,AX

	Pop	DX
	Pop	CX
	Pop	AX
	Ret
Gettime	Endp
	Page

;	 SETTIME

Settime	Proc	Near
	Push	AX
	Push	BX
	Push	CX
	Push	DX

Settimer:
	Sub	CX,CX			;Clear AF flag
	Mov	AX,Word	Ptr Hour	;get ASCII hours
	Aaa				;adjust	AL to ASCII
	Xchg	AL,AH			;switch	to other byte
	Aaa				;adjust	other byte
	Aad				;Convert to binary
	Add	CH,AL			;copy hours
	Mov	AX,Word	Ptr Minute	;get ASCII minutes
	Aaa
	Xchg	AL,AH
	Aaa
	Aad
	Add	Cl,AL			;copy minutes
	Mov	AX,Word	Ptr Second	;get ASCII seconds
	Aaa
	Xchg	AL,AH
	Aaa
	Aad
	Sub	DX,DX			;no hundreths
	Mov	DH,AL

	Mov	AH,2Dh			;Set time
	Int	21h

	Cmp	AL,0			;Set okay?
	Je	Timeset			;yes, all done

Timebad:
	Mov	AH,9			;no, print message
	Mov	DX,Offset Timemsg
	Int	21h
	Mov	DX,Offset Pr_time	;prompt	for TIME
	Lea	BX,Hour			;overlay with reply
	Call	Console			;Read the TIME
	Jmp	Settimer		;try again

Timeset:
	Pop	DX
	Pop	CX
	Pop	BX
	Pop	AX
	Ret
Settime	Endp
	Page

;	 SETDATE

Setdate	Proc	near
	Push	AX
	Push	BX
	Push	CX
	Push	DX

Setdates:
	Cmp	Byte Ptr Month[2],'-'	;proper	delimiter?
	Jne	datebad			;no, prompt again
	Cmp	Byte Ptr Day[2],'-'
	Jne	Datebad

	Sub	DX,DX			;Clears	AF for AAA
	Mov	AX,Word	Ptr Month	;get ASCII month
	Aaa
	Xchg	AL,AH
	Aaa
	Aad
	Add	DH,AL			;put month in DH,clear AF
	Mov	AX,Word	Ptr Day		;get ASCII day
	Aaa
	Xchg	AL,AH
	Aaa
	Aad
	Add	Dl,AL			;put day in DL,clear AF
	Mov	AX,Word	Ptr Year	;get ASCII year
	Aaa
	Xchg	AL,AH
	Aaa
	Aad
	Mov	CX,1900			;adjust	date
	Add	CL,AL			;put year in CL

	Mov	AH,2Bh			;Set date function
	Int	21h

	Cmp	AL,0			;Set okay?
	Je	Dateset			;yes, all done
datebad:
	Mov	AH,9			;no, print message
	Mov	DX,Offset Datemsg
	Int	21h

	Mov	DX,Offset Pr_date	;prompt	for DATE
	Lea	BX,Month		;where to reply
	Call	Console			;Read the DATE

	Jmp	Setdates		;and try it again

Dateset:
	Pop	DX
	Pop	CX
	Pop	BX
	Pop	AX
	Ret
Setdate	Endp
	Page
;	CONSOLE
;
; Input:  DX, offset to	prompt
;	  BX, LEA of reply
; Output: field	at BX has text
; Notes:  no editing performed

Console	Proc	Near
	Push	AX
	Push	CX

	Mov	AH,9
	Int	21h			;prompt	for response
Cons1:
	Mov	AH,1			;Read console character
	Int	21h

	Cmp	AL,0			;extended code?
	Jne	Cons2			;no, have one character
	Mov	AH,1Ch			;yes, get next code
	Int	21h
	jmp	Cons1			;ignore	it
Cons2:
	Cmp	AL,8			;is it BackSpace?
	Jne	Cons3
	Dec	BX			;yes, decr buffer ptr
	Jmp	Cons1			;and read next char
Cons3:	Cmp	AL,13			;is it ENTER?
	Je	Consend			;yes, all over
	Mov	[BX],AL			;copy inputted character
	Inc	BX			;increment target offset
	Jmp	Cons1			;and get next character

Consend:
	Pop	CX
	Pop	AX
	Ret
Console	Endp
	Page
Open	Proc	Near
	Push	AX
	Push	CX

	Mov	AL,2			;for read/write
	Mov	AH,3Dh			;open a	file
	Mov	DX,Offset Filename	;file to open
	Int	21h
	Mov	Handle,AX		;save file handle

	Jnc	Openend
	Aam				;format error code
	Xchg	AL,AH
	Or	Opencode,AX
	Mov	DX,Offset Openmsg
	Mov	AH,9
	Int	21h

	Mov	AH,3Ch			;So make a new one
	Sub	CX,CX
	Mov	DX,Offset FileName
	Int	21h
	Jc	OpenEnd			;Oops, now what?
	Mov	Handle,AX
	Call	Write
Openend:
	Pop	CX
	Pop	AX
	Ret
Open	Endp
	Page

	;  Read DAT file date and time	;

Read	Proc	Near
	Push	AX
	Push	DX

	Mov	CX,12			;Read date record
	Mov	DX,Offset Month
	Mov	BX,Handle
	Mov	AH,3Fh
	Int	21h

	Mov	CX,10			;Read time record
	Mov	DX,Offset Hour
	Mov	BX,Handle
	Mov	AH,3Fh
	Int	21h

Readend:
	Pop	DX
	Pop	AX
	Ret
Read	Endp

	; Write date and time to DAT file ;

Write	Proc	Near
	Push	AX
	Push	DX

	Mov	DX,Offset Month		;Re-write date
	Mov	BX,Handle
	Mov	CX,12
	Mov	AH,40h
	Int	21h

	Mov	DX,Offset Hour		;Re-write time
	Mov	BX,Handle
	Mov	CX,10
	Mov	AH,40h
	Int	21h

	Pop	DX
	Pop	AX
	Ret
Write	Endp
	Page
;		Constants and work areas

Pr_date	Db	27,'[2J'
	Db	'Current date is: '
Month	Dw	'00'
	Db	'-'
Day	Dw	'00'
	Db	'-19'
Year	Dw	'00'
End_date Dw	2020h
	Db	27,'[2;1H','Enter new date: '
	Db	'$'
Pr_time	Db	27,'[3;1H'
	Db	'Current time is: '
Hour	Dw	'00'
	Db	':'
Minute	Dw	'00'
	Db	':'
Second	Dw	'00'
End_time	Dw	0
	Db	27,'[4;1H','Enter new time: '
	Db	'$'

Ipldate	Db	'01-01-1980'
Datemsg	Db	27,'[3;1H','Date invalid',7,'$'
Timemsg	Db	27,'[5;1H','Time invalid',7,'$'
Ten	Db	10

Filename Db	'a:autodate.dat',0	;drive:filename.ext
Handle	Dw	0			;file handle from open

Openmsg	Db	'Open failed, RC='
Opencode Dw	'00'
	Db	' $'
Numbytes Dw	0			;bytes to read
Bytes	Dw	0			;bytes read
Recaddr	Dw	0			;addr of i/o area
Rec	Db	80 dup(0)		;file record area

Autodate	Endp

Cseg	Ends
	End	Autodate
