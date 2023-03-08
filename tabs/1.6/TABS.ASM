	Page	82,132
	Title	TABS - Align ASCII File

	Comment	| Version 1.6, June 27,	1984

TABS Command
-----------------

Purpose:   Replace blanks with TAB character(s); or expand TABs.

Format:	   TABS	 [d:[input.ext]] [d:[output.ext]] [/D]

Remarks:   Any TAB characters found are	first expanded.	If TABS
	appear within quoted strings - out of context -	they will
	not be expanded.

	The /D option may be used to remove TABs from a	file,

	The maximum logical record size	is 255,	see MAXREC equate.
	Defacto	tab columns are	9,17,25,...

	Written	by Vernon Buerg	for the	IBM PC using DOS 2.
	For public domain use.

Notes:  Version 1.6 includes a correction for the use of wildcards
	to name the output file the same as the input file if only
	a drive was supplied for the output file name.
-----------------					|

CSeg	Segment	Public Para 'CODE'
	Assume	CS:Cseg,DS:Cseg,ES:CSeg
	Org	100h

Tabs	Proc	Far
	Push	DS			;DOS convention
	Sub	AX,AX
	Push	AX

	Mov	CS:Stk_Top,SP		;Save stack ptr	to insure return

	Call	ChkVer			;Check for DOS 2

	Call	Alloc			;Get maximum I/O buffers

	Call	GetFile			;Get file names

	Call	OpenIn			;Open input

	Call	OpenOut			; and output

	Call	Inform			;Display "cooking" message

	Call	GenTab			;Generate tabs

	Call	Flush			;Empty the output buffer

	Mov	DX,Offset EofMsg	;Say END-OF-FILE
Error:	Mov	SP,Stk_Top		;Insure	proper return
	Call	PrintS			;Print any message

	Call	Close			;Close files

	Ret				;Return	to DOS
	Page

Buflen	Dw	0			;I/O buffer size
MinCore	Dw	512			;Minimum of one sector
Maxrec	Equ	255			;Longest logical record

S_Quote	Equ	34			;Single	quote
D_Quote	Equ	39			;Double	quote
Tab	Equ	9
Lf	Equ	10
Cr	Equ	13
EOF	Equ	1Ah

Rec	Db	Maxrec Dup (0)		;Current record
Sw	Db	0			;Number	of blanks skipped
Qsw	Db	0			;Quote switch
Detab	Db	0			;Non-zero for detab function
Stk_Top	Dw	0			;SP at entry

MsgIn	Db	Cr,Lf,'Enter INPUT file name-  ',255
Msg1	Db	Cr,Lf,'Input failed to open, '
InKey	Db	32,32			;Keyboard buffer
Input	Db	76 Dup (0),0,255	;Drive:path\name.ext
IHandle	Dw	0			;Input file handle
Ilen	Dw	0			;Input block length
Iptr	Dw	0			;Offset	to next	char
In_Ptr	Dw	0			;Seg offset

MsgOut	Db	Cr,Lf,'Enter OUTPUT file name- ',255
Msg2	Db	Cr,Lf,'Output failed to open, '
OutKey	Db	32,32
Output	Db	76 Dup (0),0,255
OHandle	Dw	0			;Output	file handle
Olen	Dw	0			;Bytes in output buffer
Optr	Dw	0			;Offset	to next	char
Out_Ptr	Dw	0			;Seg offset

DTA	Db	48 Dup (0)
	Page
Sorry	Db	Cr,Lf,'Sorry, PC DOS Version 2 required',Cr,Lf,255
Msg3f	Db	Cr,Lf,'I/O error reading',Cr,Lf,255
Msg40	Db	Cr,Lf,'I/O error writing',Cr,Lf,255
Msg4a	Db	Cr,Lf,'Insufficient memory',Cr,Lf,255
Msg4e	Db	Cr,Lf,'No matching file(s) found',Cr,Lf,255
InformD	Db	'DE-'
Cooking	Db	'TABS:     ',255
	Db	'Version 1.6 by Vernon Buerg, '
	Db	'June 27, 1984, public domain.'
Mark	Db	' => ',255
EofMsg	Db	Cr,Lf,'End of File',Cr,Lf,255
NewLine	Db	CR,LF,255

Code2	Db	'File not found ',255
Code3	Db	'Path not found ',255
Code4	Db	'Too many files ',255
Code5	Db	'Access denied  ',255
	Page
;
;	Replace	blanks with tabs

GenTab	Proc	Near
Loop:	Call	GetRec			;Get a record, length in CX
	Sub	BX,BX			;Output	column
	Mov	Sw,BL			;No blanks yet
	Mov	Qsw,BL			;No quotes yet
	Or	CX,CX			;Any data in record?
	Jz	Null			; no, just CR-LF

Set1:	Mov	SI,Offset Rec		;Look for blanks and
Wloop:	Lodsb				; replace strings of blanks
	Inc	BX			; with tab characters
	Cmp	AL,D_Quote		;Don't count blanks
	Jne	Chk1			; within single	or double
	Xor	Qsw,2			; quoted strings
	Jmp	Chk2

Chk1:	Cmp	AL,S_Quote		;Insert	TABs for any
	Jne	Chk3			; blanks skipped before
	Xor	Qsw,1			; a quote
Chk2:	Cmp	Sw,0			;Must re-insert
	Je	Check			; any blanks skipped
	Jmp	Insert			; if not enough	for a TAB

Chk3:	Cmp	Detab,0			;Leave expanded	record as-is
	Jne	Check			; if de-tabbing
	Cmp	AL,' '			;Tis a blank?
	Jne	Check			; no, see if eof
	Test	Qsw,3			;Within	quotes?
	Jnz	Check
	Inc	Sw
	Test	BL,07h			;Ready for a tab?
	Jnz	Tloop			; no, keep going
	Mov	AL,Tab			; yes, send one
	Jmp	Copy

Check:	Cmp	AL,EOF			;End of	file?
	Je	Done			; yes, all done
	Cmp	Detab,0
	Jne	Copy
	Test	Qsw,3			;When a	non-blank is
	Jnz	Copy			; encountered, insert a	TAB
	Cmp	Sw,0			; if there were	blanks
	Je	Copy			; before it
	Mov	DX,BX
	Dec	DL
	Test	DL,07h			;If the	non-blank is not
	Jnz	Insert			; in a TAB column, then
	Push	AX			; keeps	all the	blanks
	Mov	AL,Tab
	Call	PutChar
	Pop	AX
Copy:	Call	PutChar			; and write it
	Mov	Sw,0			;Ind not blank
Tloop:	Loop	Wloop
Null:	Mov	AL,Cr			;Append	CR
	Call	PutChar
	Mov	AL,Lf			; and LF
	Call	PutChar
	Jmp	Loop

Insert:	Push	AX			;Insert	any blanks that
	Mov	DL,Sw			; didn't line up on
Blanks:	Cmp	DL,1			; a TAB	column
	Jb	None
	Mov	AL,' '
	Call	PutChar
	Dec	DL			;Decr insert count
	Jmp	Blanks			; and continue
None:	Pop	AX			;Get char back
	Jmp	Copy

Done:	Ret
GenTab	Endp
	Page
;
;	Build a	logical	record with TABs expanded

GetRec	Proc	Near
;	Push	DI
	Sub	DI,DI			;Target	record offset
	Mov	Qsw,0			;Quote indicator

Get1:	Call	GetChar			;Build up a logical record
	Cmp	AL,Cr			; by looking for a CR or LF
	Je	Get1			; as end-of-record
	Cmp	AL,Lf
	Je	Get7
	Cmp	AL,S_Quote		;Don't expand tabs
	Jne	Get2			; found	within a
	Xor	Qsw,1			; quoted string
Get2:	Cmp	AL,D_Quote
	Jne	Get3
	Xor	Qsw,2
Get3:	Cmp	AL,Tab			;Is it TAB?
	Jne	Get5			; no, pass it
	Test	Qsw,3			;Within	quotes?
	Jnz	Get5			; yes, pass it as-is
Get4:	Mov	Rec[DI],' '		;Expand	embedded tabs
	Inc	DI			; with blanks
	Test	DI,0007h
	Jz	Get1
	Jmp	Get4

Get5:	Mov	Rec[DI],AL		;Build the record by
	Inc	DI			; copying each character
	Cmp	DI,Maxrec		; or TABs expanded to blanks
	Jae	Get6
	Cmp	AL,EOF			;Is it EOF?
	Je	Get6			; yes, all done
	Jmp	Get1			; no, continue
Get6:	Mov	CX,DI			;Final record length
;	Pop	DI
	Ret

Get7:	Cmp	Rec-1[DI],' '		;Omit trailing blanks
	Jne	Get6
	Dec	DI
	Jz	Get6
	Jmp	Get7

GetRec	Endp
	Page
;
;	Extract	one char from record

GetChar	Proc	Near			;Read char into	AL
Read1:	Dec	Ilen			;Any in	buffer?
	Js	Read			; no, read next	block
	Mov	SI,Iptr			; yes, get offset in buf
	Lodsb
	Mov	Iptr,SI			;Offset	for next one
	Cmp	AL,EOF
	Je	Read2			;Ignore	EOF marks
	Ret
Read2:	Mov	AL,' '
	Ret

Read:	Push	CX
	Mov	BX,IHandle		;Read a	block of data
	Mov	CX,BufLen		; into Input (segment) buffer
	Mov	DX,In_Ptr
	Mov	Iptr,DX
	Mov	AH,3Fh
	Int	21h
	Pop	CX
	Mov	Ilen,AX			; and length
	Jc	Read3
	Or	AX,AX			;Anything read?
	Jnz	Read1			; yes, pick it up
	Mov	AL,EOF			; no, return EOF
	Ret

Read3:	Mov	DX,Offset Msg3f		;Say I/O ERROR
	Jmp	Error
GetChar	Endp
	Page
;
;	Block output records

PutChar	Proc	Near			;Write from AL
	Push	CX
;	Push	DI
	Mov	DI,Optr			;Offset	in buffer
	Stosb
	Mov	Optr,DI			;New buffer ptr
	Inc	Olen
	Mov	CX,Buflen
	Cmp	Olen,CX			;Full block?
	Jae	Write3			; yes, write it
;rite1:	Pop	DI
Write1:	Pop	CX
	Ret

Flush:	Push	CX			;Write data left over
;	Push	DI			; in output buffer
	Mov	CX,Olen			;Any left in output?
	Or	CX,CX
	Jnz	Write3
	Jmp	Write1

Write3:	Push	AX
	Push	BP
	Push	BX
	Push	DX
	Mov	BX,OHandle		;Get file handle
	Mov	BP,CX			;Save size requested
	Mov	DX,Out_Ptr
	Mov	Optr,DX
	Mov	AH,40h			;Write the block
	Int	21h
	Jc	Writer			;Write OK?
	Sub	BP,AX			;Wrote all data?
	Mov	Olen,BP
	Jz	Write2			; yes, good
Writer:	Mov	DX,Offset Msg40		; no, say I/O error
	Jmp	Error

Write2:	Pop	DX
	Pop	BX
	Pop	BP
	Pop	AX
;	Pop	DI
	Pop	CX
	Ret
PutChar	Endp
	Page

;	Open input file

OpenIn	Proc	Near
	Mov	DX,Offset Input
	Mov	AL,0			;For input
	Mov	AH,3Dh			;Open a	file
	Int	21h
	Jnc	Openi
	Mov	DX,Offset Msg1
	Jmp	OpenErr

Openi:	Mov	IHandle,AX
	Ret
OpenIn	Endp

;	Open output file

OpenOut	Proc	Near
	Mov	DX,Offset Output
	Sub	CX,CX			;Normal	file attribute
	Mov	AH,3Ch			;Create	a file
	Int	21h
	Jnc	Openo
	Mov	DX,Offset Msg2
	Jmp	OpenErr

Openo:	Mov	OHandle,AX
	Ret
OpenOut	Endp

;	Determine why OPEN failed

OpenErr:Cmp	AL,2			;AL has	reason code
	Jb	Opene
	Cmp	AL,5
	Ja	Opene
	Sub	BX,BX			;Get offset to reason
	Mov	BL,AL			; text for open	failure
	Mov	CL,4
	Shl	BX,CL
	Call	PrintS			;Say OPEN FAILED
	Mov	DX,Offset NewLine
	Call	PrintS
	Lea	DX,Code2-32[BX]
Opene:	Jmp	Error

;	Close input/output

Close	Proc	Near			;Close files
	Mov	BX,OHandle		; output
	Mov	AH,3Eh
	Int	21h
	Mov	BX,IHandle		; input
	Mov	AH,3Eh
	Int	21h
	Ret
Close	Endp
	Page
;
;	Find first matching file, just cuz I'm lazy

Find	Proc	Near			;Find first matching file
	Mov	DX,Offset DTA		;Set data xfer area
	Mov	AH,1Ah
	Int	21h
	Mov	DX,Offset Input		;Input path\filename.ext
	Sub	CX,CX			;Search	for first normal file
	Mov	AH,4Eh
	Int	21h
	Jnc	Find1
Find0:	Mov	DX,Offset Msg4e		;Say NO	MATCHING FILE
	Jmp	Error

Find1:	Or	AL,AL			;Set ZF	for return
	Jnz	Find0			; if none found
	Mov	DI,Offset Input
	Cmp	Byte Ptr [DI+1],':'	;If drive was supplied
	Jne	Find2			; leave	it in file name
	Add	DI,2
Find2:	Cmp	Byte Ptr [DI],'\'	;If path was supplied
	Jne	Find5			; try to leave it in Input name
	Mov	SI,Offset Input+75
	Std
	Mov	CX,76
Find3:	Lodsb
	Cmp	AL,'\'			;Find the last separator
	Je	Find4			; which	is the filename	spec
	Loop	Find3
	Mov	SI,DI

Find4:	Mov	DI,SI
	Add	DI,2
Find5:	Mov	CX,13			;Copy found name to Input name
	Cld
	Mov	SI,Offset DTA+30	; after	drive and first	path name
Find7:	Lodsb
	Stosb
	Cmp	AL,0			;Don't want crud in message
	Je	Find9
	Loop	Find7
Find9:	Ret
Find	Endp
	Page
;
;	Get file names from command line

GetFile	Proc	Near			;Get file name(s)
	Mov	SI,80h			;Point to command line
	Sub	CX,CX			;The PSP may contain one or two
	Or	CL,Byte	Ptr DS:[SI]	; filenames separated by blanks
	Jz	GetF6
	Lea	DI,ES:Input		;Target	is infile for
	Inc	SI			; first	command	operand

GetF1:	Lodsb				;Copy command line to file names
	Cmp	AL,' '			; by skipping leading blanks
	Jne	GetF1a			; until	a CR is	found
	Loope	GetF1
	JCXz	GetF6			;If all	blank

GetF1a:	Cmp	AL,Cr			;Is it CR, end of line?
	Je	GetF5			; yes, terminate fname
	Cmp	AL,'/'			;Or option string?
	Je	GetF1c
	Cmp	AL,' '			;Ending	blank?
	Je	GetF2
	Stosb
	Lodsb
	Loop	GetF1a
	Jmp	GetF5

GetF1c:	Mov	AX,0FF00h		;Terminate fname operand
	Stosw
	Lodsb				;Get option letter
	Cmp	AL,'D'			;Set /D	option for detabbing
	Je	GetF1d
	Cmp	AL,'d'
	Jne	GetF3
GetF1d:	Mov	Detab,255
GetF3:
	Jmp	GetF6

GetF2:	Mov	AX,0FF00h		;Terminate fname operand
	Stosw
	Lea	DI,ES:Output		;Process second	fname
GetF2a:	Lodsb
	Cmp	AL,' '			;Skip intervening blanks
	Jne	GetF2b
	Loope	GetF2a
	JCXz	GetF6			;If no operand

GetF2b:	Cmp	AL,Cr			;Is it CR, end of line?
	Je	GetF5			; yes, end of command
	Cmp	AL,'/'			;Or option string?
	Je	GetF1c			; yes, copy it
	Cmp	AL,' '			;Or ending blank?
	Je	GetF2c
	Stosb				;Copy second operand
GetF2c:	Lodsb
	Loop	GetF2b

GetF5:	Mov	AX,0FF00h		;Append	zero and dollar	sign
	Stosw

GetF6:	Mov	AX,CS			;When done, set	up
	Mov	DS,AX			; segment registers
	Mov	ES,AX

GetF7:	Cmp	Input,0			;Any input name?
	Jne	GetF8			; yes, try output name
	Mov	DI,Offset MsgIn		; no, ask for one
	Mov	SI,Offset InKey
	Call	AskName			;Get the input file name

GetF8:
	Call	Find			;Find first matching file
GetF8a:	Cmp	Output,0		;Any output name?
	Jne	GetF9			; yes, that was	easy
	Mov	DI,Offset MsgOut	; no, ask for it
	Mov	SI,Offset OutKey
	Call	AskName			;Get the output	name

GetF9:	Cmp	Word Ptr Output+1,003Ah	;If just a drive is given
	Jne	GetFend			; for the output,
	Mov	CX,74			; use the input	filename
	Mov	DI,Offset Output+2
	Mov	SI,Offset Input
	Cmp	Input+1,':'		;If drive was given for
	Jne	GetF10			; input, must skip over	it
	Sub	CL,2			;Adjust	pointers passed	drive
	Add	SI,2
GetF10:	Rep	Movsb

GetFend:Ret
GetFile	Endp
	Page
;
;	Ask for	file name(s)

AskName	Proc	Near			;Ask for input file name
	Push	DI			;Ptr to	prompt msg
	Push	SI			;Ptr to	reply buffer
	Mov	Byte Ptr [SI],76	;Reply length
Ask1:	Mov	DX,DI
	Call	PrintS			;Print the prompt msg
	Mov	DX,SI			;Read console reply
	Mov	AH,10
	Int	21h
	Sub	BX,BX			;If a reply is given,
	Add	BL,1[SI]		; append a zero	as the
	Jz	Ask1			; ASCIIZ name stopper
	Mov	Word Ptr 2[SI][BX],0FF00h
	Mov	Word Ptr 0[SI],'  '	;Clear error message part
	Pop	SI
	Pop	DI
	Ret
AskName	Endp

;	Display	"cooking" message

Inform	Proc	Near
	Mov	DX,Offset NewLine
	Call	PrintS
	Mov	DX,Offset Cooking
	Cmp	Detab,0
	Je	Inform1
	Mov	DX,Offset InformD
Inform1:Call	PrintS
	Mov	DX,Offset Input
	Call	PrintS
	Mov	DX,Offset Mark
	Call	PrintS
	Mov	DX,Offset Output
	Call	PrintS
	Ret
Inform	Endp

ChkVer	Proc	Near
	Mov	AH,30h
	Int	21h			;Verify	DOS 2.0	or later
	Cmp	AL,2
	Jae	Chk9
	Mov	DX,Offset Sorry
	Jmp	Error
Chk9:	Ret
ChkVer	Endp

PrintS	Proc	Near			;Print string like Int 21h (9)
	Push	BX			;DX points to string
	Push	SI
	Mov	SI,DX
PS1:	Lodsb
	Cmp	AL,255			;String	ends in	a hex FF
	Je	PS9			; so can display dollar	sign
	Cmp	AL,0			;Ignore	zeros
	Je	PS1
	Mov	BX,7
	Mov	AH,14			;TTY write
	Int	10h
	Jmp	PS1

PS9:	Pop	SI
	Pop	BX
	Ret
PrintS	Endp

	Page
;
;	Allocate up to 32K per buffer by modifying memory
;	to use all of the 64K allowed for a COM program.
;	This is more complicated than using data segments
;	for the buffers, but has the advantages of allowing
;	for variable buffer sizes depending upon the amount
;	of memory available. It also allows DS and ES to remain
;	static. Besides, the COM version is under 2K bytes.

Alloc	Proc	Near			;Get I/O buffers
	Mov	BX,PgmSize		;Paras in program
	Mov	AH,4Ah			; and modify allocated memory
	Int	21h			; using ES from entry
	Jnc	Alloc1
Alloc0:	Mov	DX,Offset Msg4a
	Jmp	Error

Alloc1:	Mov	BX,MaxCore		;Get rest of 64k
Alloc2:	Mov	AH,48h
	Int	21h
	Jc	Alloc2			; but settle for what there is
	Mov	In_Ptr,AX		;Seg addr for input buffer
	Sub	BX,32			;Size less stack and PSP
	Js	Alloc0
	Sar	BX,1			;Paras for each buffer
	Add	AX,BX
	Mov	Out_Ptr,AX		;Seg addr for output buffer

	Mov	AX,BX
	Mov	CL,4
	Shl	AX,CL			;Convert to bytes
	Mov	BufLen,AX
	Cmp	AX,MinCore		;Have enough?
	Jb	Alloc0

	Mov	DX,DS			;Convert ptrs to offsets
	Mov	AX,In_Ptr
	Sub	AX,DX
	Shl	AX,CL
	Mov	In_Ptr,AX
	Mov	Iptr,AX

	Mov	AX,Out_Ptr
	Sub	AX,DX
	Shl	AX,CL
	Mov	Out_Ptr,AX
	Mov	Optr,AX
	Ret
Alloc	Endp

Tabs	Endp

PgmSize	Equ	($-Cseg+16)/16		;Cseg and stack length
MaxCore	Equ	4096-PgmSize		;Max 64k COM

Cseg	Ends

	End	Tabs
