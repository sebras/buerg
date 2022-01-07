	Page	74,132
	Title	TABS - Align ASCII File

	Comment	| Version 2.1, Oct 14, 1986

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

Notes:	Version	1.6 includes a correction for the use of wildcards
	to name	the output file	the same as the	input file if only
	a drive	was supplied for the output file name.

	Version	1.7 fixes a problem regarding the EOF character. It
	now considers the EOF as the end of a file and will no longer
	copy data after	that point. Also, if wildcards are used, all
	matching files are processed.

	Version	1.8 cleans up the messages displayed.

	Version 1.9 requires the ouput file on a different drive,
	or in a different path.

	Version 2.0 improves performance, adds EOF to end of file.
	Version 2.1 ignore EOF (1Ah ) in input files.

-----------------					|

CSeg	Segment	Public Para 'CODE'
	Assume	CS:Cseg,DS:Cseg,ES:CSeg
	Org	100h

Tabs	Proc	Far
	Mov	CS:Stk_Top,SP		;Save stack ptr	to insure return

	Call	ChkVer			;Check for DOS 2

	Call	Alloc			;Get maximum I/O buffers

	Call	GetFile			;Get file names

Again:
	Call	OpenIn			;Open input

	Call	OpenOut			; and output

	Call	Inform			;Display "cooking" message

	Call	GenTab			;Generate tabs

	Call	Flush			;Empty the output buffer

	Call	Close			;Close files

	Call	Next			;Get next matching file
	Or	AL,AL
	Jz	Again
	Sub	AL,AL			;All done
	Jmp	Short Exit


Error:	Mov	SP,Stk_Top		;Insure	proper return
	Call	PrintS			;Print any message

	Mov	AL,1			;Set ERRORLEVEL	to 1
Exit:	Mov	AH,4Ch
	Int	21h			;Return	to DOS
	Page
;
;	Constants, equates, and	work areas

BufLen	Dw	0			;I/O buffer size
MinCore	Equ	512			;Minimum of one	sector
Maxrec	Equ	255			;Longest logical record

S_Quote	Equ	34			;Single	quote
D_Quote	Equ	39			;Double	quote
Tab	Equ	9
LF	Equ	10
CR	Equ	13
EOF	Equ	1Ah
Stopper	Equ	255

Sw	Db	0			;Number	of blanks skipped
Qsw	Db	0			;Quote switch
Detab	Db	0			;Non-zero for detab function
Stk_Top	Dw	0			;SP at entry

Msg1	Db	CR,LF,'Input failed to open, '
Input	Db	76 Dup (0),0,Stopper	;Drive:path\name.ext
IHandle	Dw	0			;Input file handle
Ilen	Dw	0			;Input block length
Iptr	Dw	0			;Offset	to next	char
In_Ptr	Dw	0			;Seg offset

Msg2	Db	CR,LF,'Output failed to open, '
Output	Db	76 Dup (0),0,CR,LF,Stopper
OHandle	Dw	0			;Output	file handle
Olen	Dw	0			;Bytes in output buffer
Optr	Dw	0			;Offset	to next	char
Out_Ptr	Dw	0			;Seg offset

Spaces	Db	8 Dup (' ')
FilePtr	Dw	Offset Input		;Addr of file name part
NewPtr	Dw	Offset Output		;Spot for output file name
DTA	Db	48 Dup (0)		;DOS data transfer area
	Page
;
;	Messages

Version	Db	'TABS - Version 2.1 - V.Buerg',CR,LF,CR,LF
	Db	'Usage:  TABS  infile  outfile  [/D]',CR,LF
	Db	' o  infile and outfile may include drive and path names',CR,LF
	Db	' o  use ending /D to expand tabs to spaces.',CR,LF
	Db	' o  Oct 14, 1986; public domain.',Stopper

Sorry	Db	CR,LF,'Wrong PC DOS Version',Stopper
Msg3f	Db	CR,LF,'Read error',Stopper
Msg40	Db	CR,LF,'Write error or Disk full.',Stopper
Msg4a	Db	CR,LF,'Not enough memory',Stopper
Msg4e	Db	CR,LF,'No matching file(s) found',Stopper
InformD	Db	'de-'
Cooking	Db	'TABS:',9,Stopper
Mark	Db	9,'-> ',Stopper
NewLine	Db	CR,LF,Stopper

Code2	Db	'File not found ',Stopper
Code3	Db	'Path not found ',Stopper
Code4	Db	'Too many files ',Stopper
Code5	Db	'Access denied  ',Stopper
	Page
;
;	Replace	blanks with tabs

GenTab	Proc	Near
Loop:	Call	GetRec			; Get a record, length in CX
	Jnc	Init_Rec		; Was it end of file?
	Jmp	Done
Init_Rec:
	Sub	BX,BX			;Output	column
	Mov	Sw,BL			;No blanks yet
	Mov	Qsw,BL			;No quotes yet
	Or	CX,CX			;Any data in record?
	Jz	Null			; no, just CR-LF

Set1:	Mov	SI,Offset Rec		;Look for blanks and
Wloop:	Lodsb				; replace strings of blanks
	Inc	BX			; with tab characters
	Cmp	AL,D_Quote		;Don't count blanks
	Je	Chk2d			; within single	or double

Chk1:	Cmp	AL,S_Quote		;Insert	TABs for any
	Je	Chk3d			; blanks skipped before

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
Chk3d:
	Xor	Qsw,1			; a quote
Chk2:	Cmp	Sw,0			;Must re-insert
	Je	Check			; any blanks skipped
	Jmp	Insert			; if not enough	for a TAB
Chk2d:
	Xor	Qsw,2			; quoted strings
	Jmp	Chk2

Check: 	Cmp	Detab,0
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

Null:	Mov	AL,CR			;Append	CR
	Call	PutChar
	Mov	AL,LF			; and LF
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
	Sub	DI,DI			;Target	record offset
	Mov	Qsw,0			;Quote indicator

Get1:	Call	GetChar			; Build up a logical record
	Jc	GetEof 			; End of file?
	Cmp	AL,CR			; Looking for a CR or LF
	Je	Get1			;  as end-of-record
	Cmp	AL,LF
	Je	Get7
	Cmp	AL,EOF			; Ignore EOF control char
	Jne	Get1e
	Mov	AL,' '
Get1e:	Cmp	AL,S_Quote		; Don't expand tabs
	Jne	Get2			;  found within a
	Xor	Qsw,1			;  quoted string
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
	Jmp	Get1			; no, continue
Get6:	Clc
GetEof:	Mov	CX,DI			;Final record length
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
Read1:	Cmp	Ilen,0			;Any in	buffer?
	Je	Read			; no, read next	block
	Mov	SI,Iptr			; yes, get offset in buf
	Lodsb
	Mov	Iptr,SI			;Offset	for next one
	Dec	Ilen
	Clc
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
	Or	AX,AX			; Anything read?
	Jnz	Read1			;  yes, pick it up
	Stc				;  no, return EOF
	Ret

Read3:	Mov	DX,Offset Msg3f		;Say I/O ERROR
	Jmp	Error
GetChar	Endp
	Page
;
;	Block output records

PutChar	Proc	Near   			;Write from AL
	Mov	DI,Optr			;Offset	in buffer
	Stosb
	Mov	Optr,DI			;New buffer ptr
	Dec	Olen    		;Full buffer?
	Jz	PutChars
	Ret
PutChars:
	Call	Write			;  yes, write it
   	Ret
PutChar	Endp


Write	Proc	Near
	Push	CX			;Write full buffer
	Mov	CX,BufLen		;Buffer size

Write3:	Push	AX
	Push	BP
	Push	BX
	Push	DX
	Mov	BX,OHandle		;Get file handle
	Mov	BP,CX			;Save size requested
	Mov	DX,Out_Ptr
	Mov	Optr,DX
	Mov	AX,BufLen		;Reset buffer size free
	Mov	Olen,AX
	Mov	AH,40h			;Write the block
	Int	21h
	Jc	Writer			;Write OK?
	Sub	BP,AX			;Wrote all data?
	Jz	Write2			; yes, good
Writer:	Mov	DX,Offset Msg40		; no, say I/O error
	Jmp	Error

Flush:	Mov	AL,EOF			;Append EOF for funny programs
	Call	PutChar
	Push	CX			;Write data left over
	Mov	CX,BufLen
	Sub	CX,Olen			;Any left in output?
	Jnz	Write3
	Pop	CX
	Ret

Write2:	Pop	DX
	Pop	BX
	Pop	BP
	Pop	AX
	Pop	CX
	Ret
Write	Endp
	Page

;	Open input file

OpenIn	Proc	Near
	Mov	DX,Offset Input
	Mov	AX,3D00h		;For input
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
	Mov	DX,Offset Msg2		;Oops, can't open output
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
;	Get file names from command line

GetFile	Proc	Near			;Get file name(s)
	Mov	SI,80h			;Point to command line
	Sub	CX,CX			;The PSP may contain one or two
	Or	CL,Byte	Ptr DS:[SI]	; filenames separated by blanks
	Jnz	GetF0
GetUse:	Mov	DX,Offset Version	;None, display usage message
	Jmp	Error

GetF0:	Mov	DI,Offset Input		;Target	is infile for
	Inc	SI			; first	command	operand

GetF1:	Lodsb				;Copy command line to file names
	Cmp	AL,' '			; by skipping leading blanks
	Jne	GetF1a			; until	a CR is	found
	Loope	GetF1
	JCXz	GetUse			;If all	blank

GetF1a:	Cmp	AL,CR			;Is it CR, end of line?
	Je	GetF5			; yes, terminate infile	name
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
GetF1d:	Mov	Detab,Stopper
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

GetF2b:	Cmp	AL,CR			;Is it CR, end of line?
	Je	GetF5			; yes, end of name
	Cmp	AL,'/'			;Or option string?
	Je	GetF1c			; yes, copy it
	Cmp	AL,' '			;Or ending blank?
	Je	GetF2c
	Stosb				;Copy second operand
	Mov	NewPtr,DI
GetF2c:	Lodsb
	Loop	GetF2b

GetF5:	Mov	AX,0FF00h		;Append	zero and dollar	sign
	Stosw

GetF6:
GetF7:	Cmp	Input,0			;Any input name?
	Jne	GetF8			; yes, try output name
	Jmp	GetUse			; no, display usage

GetF8:
	Call	Find			;Find first matching file
GetF8a:	Cmp	Output,0		;Any output name?
	Jne	GetF9			; yes, further check name
	Cmp	Input+1,':'		;Make sure don't over-write
	Je	GetFo			; the input file
	Jmp	GetUse

GetF9:	Cmp	Word Ptr OutPut+1,003Ah	;If just a drive is given
	Jne	GetFp			; for the output
	Mov	DI,Offset OutPut+2	;Skip over drive
	Mov	Newptr,DI
	Jmp	Short GetFo		; and copy as outfile name

GetFp:	Cmp	Word Ptr Output+1,'\:'	;Drive and path?
	Je	GetFs			; yes, append infile name
	Cmp	Byte Ptr Output,'\'	;Just a	path?
	Jne	GetFend			; no, outfile is a filename

GetFs:	Mov	DI,NewPtr		;Append	path delimiter
	Mov	AL,'\'
	Stosb
	Mov	NewPtr,DI
GetFo:	Mov	CX,74			;Copy the input	filename
	Mov	DI,NewPtr		; after	the outfile spec
	Mov	SI,FilePtr
	Rep	Movsb
GetFend:Ret
GetFile	Endp
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
	Jne	Find4a			; try to leave it in Input name
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
Find4a:	Mov	FilePtr,DI		;Save addr of filename part
Find5:	Mov	CX,13			;Copy found name to Input name
	Mov	DI,FilePtr
	Cld
	Mov	SI,Offset DTA+30	; after	drive and first	path name
Find7:	Lodsb
	Stosb
	Cmp	AL,0			;Don't want crud in message
	Loopne	Find7
Find9:	Mov	AL,Stopper
	Stosb
	Sub	AL,AL			;Set good return code
	Ret

Next:	Mov	AH,4Fh			;Get next matching file
	Int	21h
	Or	AL,AL			; any more?
	Jnz	Nexted			; no, just return

	Mov	Qsw,0			;Re-initialize
	Mov	Sw,0
	Mov	AX,BufLen
	Mov	Olen,AX			;Reset buffer counts
	Mov	Ilen,0
	Mov	AX,Out_Ptr		;Reset buffer ptrs
	Mov	Optr,AX
	Mov	AX,In_Ptr
	Mov	Iptr,AX
	Mov	AX,Offset Output	;Was output name supplied?
	Cmp	AX,Newptr
	Jne     Next1
	Mov	Output,0		;Reset output file name
Next1:
	Mov	CX,8			;Clear message prefix
	Mov	SI,Offset Spaces
	Mov	DI,Offset InformD
	Rep	Movsb
	Mov	Cooking,CR
	Mov	Cooking+1,LF

	Mov	DI,NewPtr		;Copy input name as output name
	Mov	CX,13
	Mov	SI,Offset DTA+30
Next7:	Lodsb
	Stosb
	Cmp	AL,0			;Don't want crud in message
	Loopne	Next7
	Mov	AL,Stopper
	Stosb
	Jmp	Find5			; yes, copy the	name
Nexted:	Ret
Find	Endp

	Page
;
;	Display	"cooking" message

Inform	Proc	Near
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
	Cmp	AL,Stopper		;String	ends in	a hex FF
	Je	PS9			; so can display dollar	sign
	Cmp	AL,0			;Ignore	zeros
	Je	PS1
	Mov	DL,AL
	Mov	AH,2			;Display to standard device
	Int	21h
	Jmp	PS1

PS9:	Pop	SI
	Pop	BX
	Ret
PrintS	Endp

	Page
;
;	Allocate up to 32K per buffer by modifying memory
;	to use all of the 64K allowed for a COM	program.
;	This is	more complicated than using data segments
;	for the	buffers, but has the advantages	of allowing
;	for variable buffer sizes depending upon the amount
;	of memory available. It	also allows DS and ES to remain
;	static.	Besides, the COM version is under 2K bytes.

Alloc	Proc	Near			;Get I/O buffers
	Mov	CX,PgmSize		;Program size in paragraphs
	Mov	BX,Word	Ptr DS:[2]	;DOS ending seg	address
	Mov	AX,CS			;My starting seg address
	Sub	BX,AX			;Paragraphs for	this COM program
	Sub	BX,CX			; less code size
	Add	AX,CX			;Next available	segment	addr

	Cmp	BX,Maxcore		;Can only use 64k
	Jbe	Alloc0
	Mov	BX,Maxcore
Alloc0:	Mov	In_Ptr,AX		;Seg addr for input buffer
	Cmp	BX,MinCore		;Enough	just to	run?
	Jb	Alloc1
	Sub	BX,32			;Size less stack and PSP
Alloc2:	Sar	BX,1			;Paras for each	buffer
	Add	AX,BX
	Mov	Out_Ptr,AX		;Seg addr for output buffer

	Mov	AX,BX
	Mov	CL,4
	Shl	AX,CL			;Convert to bytes
	Mov	BufLen,AX
	Mov	Olen,AX
	Cmp	AX,Minpara		;Have enough?
	Jb	Alloc0			; nope,	bye

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

Alloc1:	Mov	DX,Offset Msg4a		;Not enough memory
	Jmp	Error

Alloc	Endp

Tabs	Endp

Rec	Db	0			;Current record

PgmEnd	Equ	$+MaxRec

PgmSize	Equ	(PgmEnd-Cseg+256)/16	;Cseg and stack	length
Maxcore	Equ	4096-PgmSize		;Max I/O buffer	size, paras
Minpara	Equ	32

Cseg	Ends
	End	Tabs
