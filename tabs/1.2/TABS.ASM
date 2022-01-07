Title	TABS - Align ASCII File
	Page	82,132
	Comment | Version 1.2, April 27, 1984

TABS Command
-----------------

Purpose:   Replace blanks with TAB character(s).

Format:    TABS  d:input.ext  d:output.ext

Remarks:   Any TAB characters found are first expanded. Thus, if TABS
	appear within quoted strings - out of context - they will
	be expanded incorrectly.

	In replacing blanks with tabs, quoted strings are ignored.
	The maximum logical record size is 255, see MAXREC equate.
	Defacto tab columns are 9,17,25,...

	V. Buerg, March, 1984. For public domain use.

-----------------					|

Cseg	Segment Public Para 'CODE'
	Assume	CS:Cseg,DS:Cseg,ES:Nothing

Tabs	Proc	Far
	Push	DS			;DOS convention
	Sub	AX,AX
	Push	AX
	Mov	CS:Stk_Top,SP		;Save stack ptr to insure return
	Mov	AH,30h
	Int	21h			;Verify DOS 2.0 or later
	Mov	DX,Offset Sorry
	Cmp	AL,2
	Jb	Error

	Call	GetFile 		;Get file names

	Call	OpenIn			;Open input

	Call	OpenOut 		;Open output

	Call	Inform			;Display "cooking" message

	Call	GenTab			;Generate tabs

	Call	Flush			;Empty the output buffer

	Mov	DX,Offset EofMsg	;Say END-OF-FILE
Error:	Mov	SP,Stk_Top		;Insure proper return
	Mov	AH,9			;Print any message
	Int	21h

	Call	Close			;Close files

	Ret				;Return to DOS
	Page

Buflen	Equ	16*1024 		;I/O buffer size
Maxrec	Equ	255			;Longest logical record

S_Quote Equ	34			;Single quote
D_Quote Equ	39			;Double quote
Tab	Equ	9
Lf	Equ	10
Cr	Equ	13
Eof	Equ	1Ah

Rec	Db	Maxrec Dup (0)		;Current record
Rlen	Dw	0			;Current record length
Sw	Db	0			;Number of blanks skipped
Qsw	Db	0			;Quote switch
Stk_Top Dw	0			;SP at entry

MsgIn	Db	Cr,Lf,'Enter INPUT file name>  $'
Msg1	Db	Cr,Lf,'Input failed to open>'
InKey	Db	32,32			;Keyboard buffer
Input	Db	64 Dup (0),0,'$'        ;Drive:path\name.ext
IHandle Dw	0			;Input file handle
Ilen	Dw	0			;Input block length
Iptr	Dw	0			;Offset to next char

MsgOut	Db	Cr,Lf,'Enter OUTPUT file name> $'
Msg2	Db	Cr,Lf,'Output failed to open>'
OutKey	Db	32,32
Output	Db	64 Dup (0),0,'$'
OHandle Dw	0			;Output file handle
Olen	Dw	0			;Output block size
Optr	Dw	0			;Offset to next char

Sorry	Db	Cr,Lf,'Sorry, PC DOS Version 2 required',Cr,Lf,'$'
Msg3	Db	Cr,Lf,'I/O error reading',Cr,Lf,'$'
Msg4	Db	Cr,Lf,'I/O error writing',Cr,Lf,'$'
Cooking Db	Cr,Lf,'TABBING:  $'
Mark	Db	' => $'
EofMsg	Db	Cr,Lf,'End of File',Cr,Lf,'$'
NewLine Db	CR,LF,'-$'

Code2	Db	'File not found $'
Code3	Db	'Path not found $'
Code4	Db	'Too many files $'
Code5	Db	'Access denied  $'
	Page

	;	Replace blanks with tabs

GenTab	Proc	Near
Loop:	Call	GetRec			;Get a record
	Mov	CX,Rlen 		; its length
	Sub	BX,BX			;Output column
	Mov	Sw,0			;No blanks yet
	Mov	Qsw,0			;No quotes yet
	Or	CX,CX			;Any data in record?
	Jnz	Set1
	Jmp	Null			; no, just CR-LF

Set1:	Mov	SI,Offset Rec		;Look for blanks and
Wloop:	Lodsb				; replace strings of blanks
	Inc	BX			; with tab characters
	Cmp	AL,D_Quote		;Don't count blanks
	Jne	Chk1			; within single or double
	Xor	Qsw,2			; quoted strings
	Jmp	Chk2

Chk1:	Cmp	AL,S_Quote		;Insert TABs for any
	Jne	Chk3			; blanks skipped before
	Xor	Qsw,1			; a quote
Chk2:	Cmp	Sw,0			;Must re-insert
	Je	Check			; any blanks skipped
	Jmp	Insert			; if not enough for a TAB

Chk3:	Cmp	AL,' '                  ;Tis a blank?
;	Jmp	Check			;for DETAB
	Jne	Check			; no, see if eof
	Test	Qsw,3			;Within quotes?
	Jnz	Check
	Inc	Sw
	Test	BL,07h			;Ready for a tab?
	Jnz	Tloop			; no, keep going
	Mov	AL,Tab			; yes, send one
	Jmp	Copy

Check:	Cmp	AL,Eof			;End of file?
	Je	Done			; yes, all done
;	Jmp	Copy			;for DETAB
	Test	Qsw,3			;When a non-blank is
	Jnz	Copy			; encountered, insert a TAB
	Cmp	Sw,0			; if there were blanks
	Je	Copy			; before it
	Mov	DX,BX
	Dec	DL
	Test	DL,07h			;If the non-blank is not
	Jnz	Insert			; in a TAB column, then
	Push	AX			; keeps all the blanks
	Mov	AL,Tab
	Call	PutChar
	Pop	AX
	Jmp	Copy

Insert: Push	AX			;Insert any blanks that
	Mov	DL,Sw			; didn't line up on
Blanks: Cmp	DL,1			; a TAB column
	Jb	None
	Mov	AL,' '
	Call	PutChar
	Dec	DL			;Decr insert count
	Jmp	Blanks			; and continue

None:	Pop	AX			;Get char back
Copy:	Call	PutChar 		; and write it
	Mov	Sw,0			;Ind not blank
Tloop:	Loop	Wloop
Null:	Mov	AL,Cr			;Append CR
	Call	PutChar
	Mov	AL,Lf			; and LF
	Call	PutChar
	Jmp	Loop
Done:	Ret
GenTab	Endp
	Page

	;	Build a logical record

GetRec	Proc	Near
	Push	DI
	Sub	DI,DI			;Target record offset
	Mov	Rlen,0			; and length
	Mov	Qsw,0			;Quote indicator

Get1:	Call	GetChar 		;Build up a logical record
	Cmp	AL,Cr			; by looking for a CR or LF
	Je	Get1			; as end-of-record
	Cmp	AL,Lf
	Je	Get7
	Cmp	AL,S_Quote		;Don't expand tabs
	Jne	Get2			; found within a
	Xor	Qsw,1			; quoted string
Get2:	Cmp	AL,D_Quote
	Jne	Get3
	Xor	Qsw,2
Get3:	Cmp	AL,Tab			;Is it TAB?
	Jne	Get5			; no, pass it
	Test	Qsw,3			;Within quotes?
	Jnz	Get5			; yes, pass it
Get4:	Mov	Rec[DI],' '             ;Expand embedded tabs
	Inc	DI			; with blanks
	Test	DI,0007h
	Jz	Get1
	Jmp	Get4

Get5:	Mov	Rec[DI],AL		;Build the record by
	Inc	DI			; copying each character
	Cmp	DI,Maxrec		; or TABs expanded to blanks
	Jae	Get6
	Cmp	AL,Eof			;Is it EOF?
	Je	Get6			; yes, all done
	Jmp	Get1			; no, continue
Get6:	Mov	Rlen,DI 		;Final record length
	Pop	DI
	Ret

Get7:	Cmp	Rec-1[DI],' '           ;Strip trailing blanks
	Jne	Get6
	Dec	DI
	Jz	Get6
	Jmp	Get7

GetRec	Endp
	Page
	;	Extract one char from record

GetChar Proc	Near			;Read char into AL
	Push	CX
	Push	SI
Read1:	Cmp	Ilen,0			;Any in buffer?
	Je	Read			; no, read next block
	Mov	SI,Iptr 		; yes, get offset in buf
	Push	DS
	Mov	AX,Seg InBuf		;Copy a char from the
	Mov	DS,AX			; input (segment) buffer
	Lodsb
	Pop	DS
	Mov	Iptr,SI 		;Offset for next one
	Dec	Ilen			;Decr buffer size left
	Jmp	Read4			; and return with AL

Read:	Mov	BX,IHandle		;Read a block of data
	Mov	CX,BufLen		; into Input (segment) buffer
	Sub	DX,DX
	Push	DS
	Mov	AX,Seg InBuf
	Mov	DS,AX
	Mov	AH,3Fh
	Int	21h
	Pop	DS
	Mov	Iptr,0			;Reset buffer ptr
	Mov	Ilen,AX 		; and length
	Jc	Read2
	Or	AX,AX			;Anything read?
	Jnz	Read1			; yes, pick it up
	Mov	AL,Eof			; no, return EOF
	Jmp	Read4

Read2:	Mov	DX,Offset Msg3		;Say I/O ERROR
	Jmp	Error

Read4:	Pop	SI
	Pop	CX
	Ret
GetChar Endp
	Page

	;	Block output records

PutChar Proc	Near			;Write from AL
	Push	AX
	Push	BP
	Push	BX
	Push	CX
	Push	DI
	Push	DX
	Mov	DI,Optr 		;Offset in buffer
	Mov	DX,Seg OutBuf
	Push	ES			;Get buffer segment
	Mov	ES,DX
	Stosb				;Place into buffer
	Pop	ES
	Inc	Olen			;Incr the length
	Mov	Optr,DI 		; and buffer ptr
	Cmp	Olen,Buflen		;Full block?
	Jb	Write2			; no, return
	Mov	CX,Buflen		; yes,write it
	Jmp	Write3

Flush:	Push	AX			;Write data left over
	Push	BP			; in output buffer
	Push	BX
	Push	CX
	Push	DI
	Push	DX
	Mov	CX,Olen 		;Any left in output?
	Or	CX,CX
	Jz	Write2

Write3: Mov	BX,OHandle		;Get file handle
	Mov	BP,CX			;Save size requested
	Sub	DX,DX
	Push	DS			;Set up DS:DX
	Mov	AX,Seg OutBuf		; in buffer segment
	Mov	DS,AX
	Mov	AH,40h			;Write the block
	Int	21h
	Pop	DS
	Mov	Optr,0			;Reset buffer ptr
	Mov	Olen,0			; and size used
	Jc	Writer			;Write OK?
	Cmp	BP,AX			;Wrote all data?
	Je	Write2			; yes, good
Writer: Mov	DX,Offset Msg4		; no, say I/O error
	Jmp	Error

Write2: Pop	DX
	Pop	DI
	Pop	CX
	Pop	BX
	Pop	BP
	Pop	AX
	Ret
PutChar Endp
	Page

	;	Open input file

OpenIn	Proc	Near
	Mov	DX,Offset Input
	Mov	AL,0			;For input
	Mov	AH,3Dh			;Open a file
	Int	21h
	Jnc	Openi
	Mov	DX,Offset Msg1
	Jmp	OpenErr

Openi:	Mov	IHandle,AX
	Ret
OpenIn	Endp

	;	Open output file

OpenOut Proc	Near
	Mov	DX,Offset Output
	Sub	CX,CX			;Normal file attribute
	Mov	AH,3Ch			;Create a file
	Int	21h
	Jnc	Openo
	Mov	DX,Offset Msg2
	Jmp	OpenErr

Openo:	Mov	OHandle,AX
	Ret
OpenOut Endp

	;	Determine why OPEN failed

OpenErr:Cmp	AL,2			;AL has reason code
	Jb	Opene
	Cmp	AL,5
	Ja	Opene
	Sub	BX,BX			;Get offset to reason
	Mov	BL,AL			; text for open failure
	Mov	CL,4
	Shl	BX,CL
	Mov	AH,9			;Say OPEN FAILED
	Int	21h
	Mov	DX,Offset NewLine
	Mov	AH,9
	Int	21h
	Lea	DX,Code2-32[BX]
Opene:	Jmp	Error

	;	Close input/output

Close	Proc	Near			;Close files
	Mov	BX,IHandle		; input
	Mov	AH,3Eh
	Int	21h
	Mov	BX,OHandle		; output
	Mov	AH,3Eh
	Int	21h
	Ret
Close	Endp
	Page

	;	Get file names from command line

GetFile Proc	Near			;Get file name(s)
	Push	CS			;DS points to PSB
	Pop	ES			;Now ES points to data
	Mov	SI,80h			;Point to command line
	Sub	BP,BP			;Indicates first or second name
	Sub	CH,CH			;The PSP may contain one or two
	Or	CL,Byte Ptr DS:[SI]	; filenames separated by blanks
	Jz	GetF5
	Lea	DI,ES:Input
	Inc	SI

GetF1:	Lodsb				;Copy command line to file names
	Cmp	AL,' '                  ; by skipping leading blanks
	Jne	GetF2			; until a CR is found
	Or	BP,BP			; or until the length is zero
	Jz	GetF4			;If a second blank is found,
	Mov	AX,2400h		; append zero and dollar sign
	Stosw
	Lea	DI,ES:Output		; and it starts the second file name
	Jmp	GetF4

GetF2:	Cmp	AL,Cr			;Is it CR, end of line?
	Je	GetF5			; yes, end of command
	Stosb				; no, save in name
	Mov	BP,DI			; and indicate data copied
GetF4:	Loop	GetF1

GetF5:	Mov	AX,2400h		;Append zero and dollar sign
	Stosw
	Mov	AX,CS			;When done, set up
	Mov	DS,AX			; segment registers

GetF7:	Cmp	Input,0 		;Any input name?
	Jne	GetF8			; yes, try output name
	Mov	DI,Offset MsgIn 	; no, ask for one
	Mov	SI,Offset InKey
	Call	AskName 		;Get the input file name

GetF8:	Cmp	Output,0		;Any output name?
	Jne	GetF9			; yes, that was easy
	Mov	DI,Offset MsgOut	; no, ask for it
	Mov	SI,Offset OutKey
	Call	AskName 		;Get the output name

GetF9:	Cmp	Word Ptr Output+1,003Ah ;If just a drive is given
	Jne	GetFend 		; for the output,
	Mov	CX,64			; use the input filename
	Mov	DI,Offset Output+2
	Mov	SI,Offset Input
	Cmp	Input+1,':'             ;If drive was given for
	Jne	GetF10			; input, must skip over it
	Dec	CL
	Dec	CL			;Adjust pointers passed drive
	Dec	SI
	Dec	SI
GetF10: Rep	Movsb

GetFend:Ret
GetFile Endp
	Page

	;	Ask for file name(s)

AskName Proc	Near			;Ask for input file name
	Push	DI			;Ptr to prompt msg
	Push	SI			;Ptr to reply buffer
	Mov	Byte Ptr [SI],64	;Reply length
Ask1:	Mov	DX,DI
	Mov	AH,9			;Print the prompt msg
	Int	21h
	Mov	DX,SI			;Read console reply
	Mov	AH,10
	Int	21h
	Sub	BX,BX			;If a reply is given,
	Add	BL,1[SI]		; append a zero as the
	Jz	Ask1			; ASCIIZ name stopper
	Mov	Word Ptr 2[SI][BX],2400h
	Mov	Word Ptr 0[SI],'  '     ;Clear error message part
	Pop	SI
	Pop	DI
	Ret
AskName Endp

	;	Display "cooking" message

Inform	Proc	Near
	Mov	AH,9
	Mov	DX,Offset Cooking
	Int	21h
	Mov	AH,9
	Mov	DX,Offset Input
	Int	21h
	Mov	AH,9
	Mov	DX,Offset Mark
	Int	21h
	Mov	AH,9
	Mov	DX,Offset Output
	Int	21h
	Ret
Inform	Endp

Tabs	Endp


Cseg	Ends

Stk	Segment Byte Stack 'STACK'
	Db	128 Dup (?)
Stk	Ends

InBuf	Segment Public Byte 'DATA'
	Db	Buflen Dup (?)
InBuf	Ends

OutBuf	Segment Public Byte 'DATA'
	Db	Buflen Dup (?)
OutBuf	Ends

	End	Tabs
				;	Clock_cntr.Yr < 179
		mov	AX,BX			;AL = yy
		or	AL,AL			;Same as 'cmp AL,0'
