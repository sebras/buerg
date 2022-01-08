	Page	80,132
	Title	Set Oki	Printer	Modes

; This program sends control characters	to an OkiData Microline	92
; printer connected as LPT1.
;
; The user is presented	with a menu of 20 items. Any number of
; control functions may	be performed.
;
; DOS 2.00 with	ANSI.SYS is required.

Cseg	Segment	Para Public 'CODE'
	Org	100h

Set_Oki	Proc	Far
	Assume	CS:Cseg,DS:Cseg,ES:Cseg

Set:	Push	DS
	Xor	AX,AX			;Set return code
	Push	AX

Start:	Mov	DX,Offset Titles	;Start-up message
	Mov	AH,9
	Int	21h

Prompt:	Mov	AH,8			;Get char in AL, no echo
	Int	21h			; call DOS to do it
	Cmp	AL,0			;Extended code?
	Jne	ChkEsc
	Jmp	Short Ext		      ;Yes, invalid
ChkEsc:	Cmp	AL,27			; or ESCape?
	Jne	ChkLtr
	Jmp	Short Done		      ;Yes, close up

ChkLtr:	Mov	What,AL
	Cmp	AL,65			;Is it a letter?
	Jl	Number			; no, assume number
	And	AL,0DFh			;Make upper case
	Mov	What,AL
	Sub	AL,'A'			;Get offset
	Add	AL,10
	Jmp	Short Letter

Number:	Cmp	AL,'9'			;Valid number?
	Ja	Error			; nope
	Sub	AL,'0'			;To binary value
	Js	Error			;if less than zero
Letter:	Mov	SI,AX			;Save binary code
	Cmp	AL,17			;Exceeded menu list?
	Ja	Error			;Yes, oops
	Add	AL,AL			;Times 2 for indexing
	Mov	BL,AL			;Copy offset
	Sub	BH,BH			;Clear hi-byte
	Mov	CX,Word	Ptr Cmds[BX]

	Mov	AX,SI			;Get code back
	Mul	Text_Size
	Mov	DI,AX			; as index to attribute
	Mov	Text+2[DI],'1'		; and hi-lite chosen text
	Mov	Text+Text_Ln-1[DI],'$'	; add print stopper
	Mov	DX,Offset InCase
	Mov	AH,9			;In case printer is off
	Int	21h

Send:	Mov	DL,CL
	Mov	AH,5			;Print first hex code
	Int	21H

	Mov	DL,CH
	Mov	AH,5			; and second code
	Int	21H

	Mov	CX,Offset Answer
HiLite:	Mov	DX,Offset Word Ptr Text
	Add	DX,DI			;Hi-lite selected option
	Mov	AH,9
	Int	21h

	Mov	DX,CX			;Appropriate message
	Mov	AH,9			;Confirm selection
	Int	21H
	Mov	DX,Offset Cursor
	Mov	AH,9			;Reset cursor
	Int	21h
	Jmp	Short Prompt		      ;Get another selection

Done:	Mov	AH,9
	Mov	DX,Offset End_Msg	;All Set
	Int	21h
	Ret				;Return	to DOS

Ext:	Mov	AH,8			;Get extended char
	Int	21h
Error:	Mov	AH,9
	Mov	DX,Offset Err_Msg	;Invalid entry
	Int	21h
	Jmp	Prompt

Set_Oki	Endp
	Page
;
;		C O N S	T A N T	S

Titles	Db	27,'[2J',27,'[=2h',27,'[4m',27,'[1;5H'
Version	Db	' Set Okidata Printer - Ver 1.1'
	Db	' (c) 1984 Vernon D. Buerg '

;	Each entry must	be the same size and in	number sequence

Text	Db	27,'[0m',27,'[3;5H0 = Six (6) lpi       ';2754
Text_ln	Equ	$ - Text
	Db	27,'[0m',27,'[4;5H1 = Pica 10 cpi       ';3000
	Db	27,'[0m',27,'[5;5H2 = Elite 12 cpi      ';2800
	Db	27,'[0m',27,'[6;5H3 = Condensed 17 cpi  ';2900
	Db	27,'[0m',27,'[7;5H4 = Data quality      ';2748
	Db	27,'[0m',27,'[8;5H5 = Emphasized Print  ';2784
	Db	27,'[0m',27,'[9;5H6 = Enhanced print    ';2772
	Db	27,'[0m',27,'[10;5H7 = Underlined       ';2767
	Db	27,'[0m',27,'[11;5H8 = Form feed        ';1200
	Db	27,'[0m',27,'[3;41H9 = Eight (8) lpi    ';2756
	Db	27,'[0m',27,'[4;41HA = Double Pica 5    ';3031
	Db	27,'[0m',27,'[5;41HB = Double Elite 6   ';2831
	Db	27,'[0m',27,'[6;41HC = Double Condensed ';2931
	Db	27,'[0m',27,'[7;41HD = Correspondence   ';2749
	Db	27,'[0m',27,'[8;41HE = Stop Emphasized  ';2773
	Db	27,'[0m',27,'[9;41HF = Stop Enhanced    ';2773
	Db	27,'[0m',27,'[10;41HG = Stop Underlined ';2768
	Db	27,'[0m',27,'[11;41HH = Line feed       ';1310

	Db	27,'[16;18H(ESCape to quit)'
	Db	27,'[0m',27,'[14;18HEnter selection => ',27,'[K$'

Answer	Db	27,'[0m',27,'[15;18H'
What	Db	0,' has been set$'

Err_Msg	Db	07,27,'[1m',27,'[15;18HInvalid entry',27,'[K'
Cursor	Db	27,'[0m',27,'[14;37H',27,'[K $'
InCase	Db	27,'[0m',27,'[20;1H',27,'[K$'

End_Msg	Db	27,'[19;20H',27,'[1m ALL SET',27,'[0m$'

Text_Size Db	Text_Ln

Cmds	Db	27,54 ;0 6lpi	Two byte DECIMAL codes
	Db	30,00 ;1 pica	Refer to User's Manual
	Db	28,00 ;2 elite
	Db	29,00 ;3 condensed
	Db	27,48 ;4 data quality
	Db	27,84 ;5 emphasized
	Db	27,72 ;6 enhanced
	Db	27,67 ;7 underlined
	Db	12,00 ;8 form feed
	Db	27,56 ;9 8 lpi
	Db	30,31 ;A dbl-pica
	Db	28,31 ;B dbl-elite
	Db	29,31 ;C dbl-condensed
	Db	27,49 ;D corres. quality
	Db	27,73 ;E stop emphasized
	Db	27,73 ;F stop enhanced
	Db	27,68 ;G stop underlined
	Db	13,10 ;H line feed
Cseg	Ends
	End	Set
