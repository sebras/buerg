	TITLE	Set_Oki	Printer	Modes
	PAGE	80,132

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
	Xor	AX,AX		;Set return code
	Push	AX
	Push	CS		;Set Data Seg
	Pop	DS
	Jmp	Start		;Damn assembler
	Page

;		C O N S	T A N T	S

Titles	Db	27,'[2J',27,'[=2h',27,'[0m'
Version	Db	'Set OKIDATA Printer - Version 2.0'
	Db	27,'[1;41H (c) 1984 Vernon D. Buerg'
;	   Each	entry must be the same sizes and in number sequence
Text	Db	27,'[0m',27,'[3;1H0 = Six (6) lpi		';2754
Text_ln	Equ	This Byte - Text
	Db	27,'[0m',27,'[4;1H1 = Pica 10 cpi		';3000
	Db	27,'[0m',27,'[5;1H2 = Elite 12 cpi		';2800
	Db	27,'[0m',27,'[6;1H3 = Condensed	17 cpi		';2900
	Db	27,'[0m',27,'[7;1H4 = Data processing quality	';2748
	Db	27,'[0m',27,'[8;1H5 = Emphasized Print		';2784
	Db	27,'[0m',27,'[9;1H6 = Enhanced print		';2772
	Db	27,'[0m',27,'[10;1H7 = Underlined		';2767
	Db	27,'[0m',27,'[11;1H8 = Form feed		';1200
	Db	27,'[0m',27,'[12;1H9 = Line feed		';1310
	Db	27,'[0m',27,'[3;41HA = Eight (8) lpi		';2756
	Db	27,'[0m',27,'[4;41HB = Double Pica, 5 cpi	';3031
	Db	27,'[0m',27,'[5;41HC = Double Elite, 6 cpi	';2831
	Db	27,'[0m',27,'[6;41HD = Double Condensed, 8.5cpi	';2931
	Db	27,'[0m',27,'[7;41HE = Correspondence quality	';2749
	Db	27,'[0m',27,'[8;41HF = Stop Emphasized print	';2773
	Db	27,'[0m',27,'[9;41HG = Stop Enhanced print	';2773
	Db	27,'[0m',27,'[10;41HH =	Stop Underlining	';2768
	Db	27,'[0m',27,'[11;41HI =	ITALIC characters	';dlcg
	Db	27,'[0m',27,'[12;41HJ =	SCRIPT characters	';dlcg

Msg	Db	27,'[17;18HESCape to exit'
	Db	27,'[14;18HEnter selection => ',27,'[K$'

Answer	Db	27,'[0m',27,'[15;18H'
What	Db	0,' has	been processed$'

S_Title	Db	27,'[0m',27,'[15;18HLoading SCRIPT character set.$'
I_Title	Db	27,'[0m',27,'[15;18HLoading ITALIC character set.$'
S_Msg	Db	27,'[0m',27,'[15;18HSCRIPT characters now loaded.$'
I_Msg	Db	27,'[0m',27,'[15;18HITALIC characters now loaded.$'

Err_Msg	Db	07,27,'[1m',27,'[15;18HInvalid entry',27,'[K'
Cursor	Db	27,'[0m',27,'[14;37H',27,'[K $'
InCase	Db	27,'[0m',27,'[20;1H',27,'[K$'

End_Msg	Db	27,'[19;20H',27,'[1m ALL SET',27,'[0m$'

Text_Size Db	Text_ln
Count	Dw	0

Cmds	Db	27,54 ;0 6lpi	Two byte DECIMAL codes
	Db	30,00 ;1 pica	Refer to User's	Manual
	Db	28,00 ;2 elite
	Db	29,00 ;3 condensed
	Db	27,48 ;4 data quality
	Db	27,84 ;5 emphasized
	Db	27,72 ;6 enhanced
	Db	27,67 ;7 underlined
	Db	12,00 ;8 form feed
	Db	13,10 ;9 line feed
	Db	27,56 ;A 8 lpi
	Db	30,31 ;B dbl-pica
	Db	28,31 ;C dbl-elite
	Db	29,31 ;D dbl-condensed
	Db	27,49 ;E corres. quality
	Db	27,73 ;F stop emphasized
	Db	27,73 ;G stop enhanced
	Db	27,68 ;H stop underlined
	Db	00,00 ;I Italic
	Db	00,00 ;J Script
	Page


;	    S C	R I P T	  Characters


Script	Equ	This Byte
	DB	'A0',48,104,84,66,8,33,21,9,7,2,0	 ;Numbers
	DB	'A1',0,64,64,64,96,80,10,6,2,1,0
	DB	'A2',64,64,96,64,82,65,73,1,5,3,0
	DB	'A3',0,32,64,64,72,65,45,17,3,1,1
	DB	'A4',0,16,24,20,82,48,16,24,20,2,1
	DB	'A5',32,64,64,68,70,69,41,17,1,1,1
	DB	'A6',0,96,80,72,76,74,40,17,1,1,2
	DB	'A7',0,96,0,17,1,9,1,5,1,3,1
	DB	'A8',0,0,32,80,68,74,72,41,17,5,2
	DB	'A9',32,64,68,74,8,41,25,9,5,3,0
;
	DB	'AA',0,60,66,1,64,1,64,57,70,2,65	 ;Upper	case
	DB	'AB',0,112,12,67,8,65,8,70,48,64,64
	DB	'AC',0,28,34,0,65,0,65,0,65,2,64
	DB	'AD',0,112,12,67,0,65,0,65,32,94,64
	DB	'AE',0,0,54,0,73,0,73,0,65,2,64
	DB	'AF',0,1,0,66,40,18,8,5,10,1,0
	DB	'AG',0,0,14,80,1,80,33,16,9,2,0
	DB	'AH',0,98,24,7,8,0,8,32,88,7,64
	DB	'AI',0,0,0,0,102,9,64,63,0,0,0
	DB	'AJ',0,0,34,80,1,64,63,0,1,0,1
	DB	'AK',0,64,32,24,7,8,4,16,34,1,64
	DB	'AL',0,32,80,0,80,47,16,33,66,0,64
	DB	'AM',64,62,1,1,0,6,0,1,1,62,64
	DB	'AN',1,0,126,0,1,0,1,0,62,0,64
	DB	'AO',0,28,34,0,65,0,65,0,34,92,64
	DB	'AP',0,66,48,15,0,9,0,9,0,6,0
	DB	'AQ',32,82,0,81,0,49,0,25,38,0,64
	DB	'AR',64,50,12,3,8,1,8,17,40,6,64
	DB	'AS',32,0,16,32,72,3,68,1,74,0,48
	DB	'AT',50,65,16,65,0,65,62,1,0,1,0
	DB	'AU',48,12,67,0,64,0,48,12,67,0,64
	DB	'AV',4,2,31,32,64,0,32,16,40,7,64
	DB	'AW',63,64,64,0,48,0,64,64,63,0,64
	DB	'AX',64,1,32,18,12,0,12,18,32,1,64
	DB	'AY',0,7,32,72,0,72,0,56,71,0,64
	DB	'AZ',0,2,64,33,80,9,68,1,66,1,64
;
	DB	'Aa',64,64,56,32,68,0,68,0,56,4,64	 ;Lower	case
	DB	'Ab',64,0,32,0,22,41,69,66,48,16,64
	DB	'Ac',64,64,48,8,68,0,68,0,68,8,64
	DB	'Ad',64,64,56,64,4,64,4,64,63,0,64
	DB	'Ae',64,64,48,8,100,0,84,0,68,8,64
	DB	'Af',32,0,16,15,112,13,2,8,0,0,0
	DB	'Dg',0,0,6,96,9,96,25,0,22,0,16
	DB	'Ah',64,33,30,0,0,4,0,4,56,0,64
	DB	'Ai',64,0,32,0,29,32,0,64,64,0,64
	DB	'Dj',16,0,8,96,20,66,61,0,16,0,16
	DB	'Ak',64,32,16,15,24,4,16,4,40,0,64
	DB	'Al',64,0,38,9,16,9,38,0,64,0,64
	DB	'Am',64,56,4,0,4,24,4,0,4,56,64
	DB	'An',64,32,16,108,0,0,4,0,4,56,64
	DB	'Ao',64,56,0,68,0,68,0,60,0,4,4
	DB	'Dp',16,64,56,4,18,1,16,1,8,6,16
	DB	'Dq',16,0,14,0,17,0,81,32,94,0,80
	DB	'Ar',64,32,16,8,116,8,0,4,0,4,8
	DB	'As',64,0,32,0,48,64,8,64,12,80,32
	DB	'At',64,0,32,16,15,48,68,0,68,0,64
	DB	'Au',64,0,60,0,64,0,64,0,124,0,64
	DB	'Av',68,40,16,32,64,0,32,16,72,4,64
	DB	'Aw',64,60,64,0,64,48,64,0,64,60,64
	DB	'Ax',64,4,32,8,16,0,40,0,68,0,64
	DB	'Dy',16,0,15,0,16,64,16,96,63,0,16
	DB	'Dz',16,8,4,18,0,89,0,85,32,19,0
;
	DB	'A',33,0,0,0,64,0,28,24,14,10,7,0	;exclamation
	DB	'A',34,4,6,1,2,1,4,6,1,2,1,0		;dbl-quote
	DB	'A',35,16,32,20,8,20,34,20,8,20,2,4	;pound
	DB	'A',36,0,0,80,32,100,42,50,3,6,1,0	;dollar
	DB	'A',37,32,0,18,1,10,33,20,32,18,0,1	;percent
	DB	'A',38,0,32,64,80,64,68,74,72,53,17,107	;ampersand
	DB	'A',39,0,0,8,0,4,2,1,2,1,0,0		;right-quote
	DB	'A',40,0,0,56,68,0,2,0,1,0,0,0		;left-paren
	DB	'A',41,0,0,0,64,0,32,16,9,6,0,0		;right-paren
	DB	'A',42,32,8,0,58,16,28,4,46,0,8,2	;asterisk
	DB	'A',43,0,0,8,40,24,8,12,10,8,0,0	;plus
	DB	'D',44,0,32,16,8,16,8,0,0,0,0,0		;comma
	DB	'A',45,0,0,8,8,8,8,8,8,8,0,0		;minus
	DB	'A',46,0,0,64,32,64,32,0,0,0,0,0	;period
	DB	'A',47,64,32,0,16,0,8,0,4,0,2,1		;slash
	DB	'A',58,0,64,32,64,40,4,8,4,0,0,0	;colon
	DB	'D',59,64,32,0,48,0,20,2,4,2,0,0	;semi-colon
	DB	'A',60,0,0,0,8,16,36,64,2,0,1,0		;less-than
	DB	'A',61,0,32,40,40,40,40,40,40,8,0,0	;equals
	DB	'A',62,64,0,32,1,18,4,8,0,0,0,0		;greater-than
	DB	'A',63,0,0,0,64,2,17,9,1,5,3,0		;question
	DB	'A',64,28,32,74,20,17,117,73,69,33,18,12 ;at
	DB	'A',91,64,96,80,72,68,2,1,1,1,1,1	;left-bracket
	DB	'A',92,0,0,0,1,2,4,8,16,32,64,0		;int-divide
	DB	'A',93,64,64,64,64,64,33,17,9,5,3,1	;right-bracket
	DB	'A',94,0,0,4,0,2,0,1,2,4,0,0		;caret
	DB	'D',95,64,64,64,64,64,64,64,64,64,64,64	;under-score
	DB	'A',96,0,0,0,0,0,2,1,6,9,0,0		;left-quote
	DB	'A',123,0,8,64,104,80,68,2,1,1,1,1	;left-brace
	DB	'A',124,64,32,80,32,20,2,5,2,1,0,0	;concat
	DB	'A',125,64,64,64,64,32,16,1,13,3,9,0	;right-brace
	DB	'A',126,0,4,2,1,0,7,0,4,2,1,0		;tilde
	DB	'A',127,127,127,127,127,127,127,127,127,127,127,127 ;del

SCount	Dw	(This Byte - Script) / 13
	Page


;	    I T	A L I C	  Characters


Italics	Equ	This Byte
	DB	'A0',48,104,84,66,8,33,21,9,7,2,0	;Numbers
	DB	'A1',0,64,64,64,96,80,10,6,2,1,0
	DB	'A2',64,64,96,64,82,65,73,1,5,3,0
	DB	'A3',0,32,64,64,72,65,45,17,3,1,1
	DB	'A4',0,16,24,20,82,48,16,24,20,2,1
	DB	'A5',32,64,64,68,70,69,41,17,1,1,1
	DB	'A6',0,96,80,72,76,74,40,17,1,1,2
	DB	'A7',0,96,0,17,1,9,1,5,1,3,1
	DB	'A8',0,0,32,80,68,74,72,41,17,5,2
	DB	'A9',32,64,68,74,8,41,25,9,5,3,0
;
	DB	'AA',96,16,8,4,10,64,41,17,9,6,0	;Upper case
	DB	'AB',0,64,32,80,8,76,10,73,9,65,54
	DB	'AC',32,80,72,68,66,64,65,33,1,1,2
	DB	'AD',64,96,16,72,4,66,1,33,17,9,6
	DB	'AE',64,96,80,72,76,74,73,9,1,1,1
	DB	'AF',64,32,16,8,12,10,9,9,1,1,1
	DB	'AG',32,80,72,68,66,80,49,17,17,17,2
	DB	'AH',64,32,16,8,68,42,17,8,4,2,1
	DB	'AI',64,64,64,96,80,8,5,3,1,1,1
	DB	'AJ',112,0,64,32,17,8,5,2,1,0,1
	DB	'AK',64,32,16,8,4,10,113,4,0,2,1
	DB	'AL',64,96,80,72,68,66,65,64,0,0,0
	DB	'AM',96,16,8,4,2,15,64,36,18,8,7
	DB	'AN',96,16,8,4,2,95,32,16,8,4,3
	DB	'AO',112,72,68,66,64,1,33,17,9,7,0
	DB	'AP',64,32,16,8,12,10,9,9,9,9,7
	DB	'AQ',56,68,66,64,81,1,33,17,78,0,0
	DB	'AR',64,32,16,8,4,10,17,104,9,5,2
	DB	'AS',48,0,64,0,64,6,40,17,0,1,2
	DB	'AT',64,32,17,9,5,3,1,1,1,1,1
	DB	'AU',32,80,72,68,2,33,16,8,4,2,1
	DB	'AV',0,112,72,36,2,17,0,8,4,2,1
	DB	'AW',112,8,36,18,33,64,48,8,4,2,1
	DB	'AX',64,32,16,0,9,2,4,24,98,0,1
	DB	'AY',0,64,33,18,12,0,4,0,2,0,1
	DB	'AZ',64,96,64,80,65,73,69,1,3,1,1
;
	DB	'Aa',0,48,72,0,68,0,4,100,24,72,4	;Lower case
	DB	'Ab',64,96,16,72,4,66,5,32,20,8,0
	DB	'Ac',32,80,72,64,68,68,4,36,8,0,0
	DB	'Ad',112,8,68,0,68,32,20,8,4,2,1
	DB	'Ae',32,80,88,80,84,84,20,20,12,0,0
	DB	'Af',64,32,16,8,12,10,8,9,1,1,2
	DB	'Dg',0,72,20,66,16,33,16,9,5,2,1
	DB	'Ah',64,32,16,8,4,2,69,32,20,8,0
	DB	'Ai',0,0,64,32,16,8,4,0,1,0,0
	DB	'Dj',64,0,64,0,32,16,8,5,2,1,0
	DB	'Ak',64,32,16,8,28,34,73,8,4,0,0
	DB	'Al',64,32,16,8,4,2,1,0,0,0,0
	DB	'Am',64,32,16,12,4,24,0,72,32,28,4
	DB	'An',64,32,16,8,4,0,68,36,20,8,0
	DB	'Ao',32,80,8,64,4,32,20,8,0,0,0
	DB	'Dp',64,32,16,24,20,18,17,1,9,5,2
	DB	'Dq',0,8,20,82,112,81,9,37,3,1,0
	DB	'Ar',64,32,16,8,4,0,4,4,4,8,0
	DB	'As',0,0,32,64,64,64,72,52,4,4,8
	DB	'At',0,0,32,16,72,4,66,5,32,4,0
	DB	'Au',32,80,72,68,0,32,16,8,4,0,0
	DB	'Av',64,96,80,8,36,0,16,0,8,0,4
	DB	'Aw',32,80,8,36,48,64,0,32,16,8,4
	DB	'Ax',0,0,64,0,32,20,8,16,40,68,0
	DB	'Dy',0,64,72,84,18,33,16,8,4,2,1
	DB	'Az',0,0,64,64,96,68,84,68,12,4,4
;
	DB	'A',33,0,0,0,64,0,28,24,14,10,7,0	;exclamation
	DB	'A',34,0,0,0,0,0,2,1,0,2,1,0		;double-quote
	DB	'A',35,16,32,20,8,20,34,20,8,20,2,4	;pound
	DB	'A',36,0,0,80,32,100,42,50,3,6,1,0	;dollar
	DB	'A',37,32,0,18,1,10,33,20,32,18,0,1	;percent
	DB	'A',38,0,32,64,80,64,68,74,72,53,17,107	;ampersand
	DB	'A',39,0,8,0,4,2,1,2,1,0,0,0		;quote
	DB	'A',40,0,0,56,68,0,2,0,1,0,0,0		;left-paren
	DB	'A',41,0,0,0,64,0,32,16,9,6,0,0		;right-paren
	DB	'A',42,32,8,0,58,16,28,4,46,0,8,2	;asterisk
	DB	'A',43,0,0,8,40,24,8,12,10,8,0,0	;plus
	DB	'D',44,0,32,16,8,16,8,0,0,0,0,0		;comma
	DB	'A',45,0,0,8,8,8,8,8,8,8,0,0		;dash
	DB	'A',46,0,0,64,32,64,32,0,0,0,0,0	;period
	DB	'A',47,64,32,0,16,0,8,0,4,0,2,1		;slash
	DB	'A',58,0,64,32,64,40,4,8,4,0,0,0	;colon
	DB	'D',59,64,32,0,48,0,20,2,4,2,0,0	;semi-colon
	DB	'A',60,0,0,0,8,16,36,64,2,0,1,0		;less-than
	DB	'A',61,0,32,40,40,40,40,40,40,8,0,0	;equals
	DB	'A',62,64,0,32,1,18,4,8,0,0,0,0		;greater-than
	DB	'A',63,0,0,0,64,2,17,9,1,5,3,0		;question
	DB	'A',64,28,32,74,20,17,117,73,69,33,18,12 ;at
	DB	'A',91,64,96,80,72,68,2,1,1,1,1,1	;left-bracket?
	DB	'A',92,0,0,0,1,2,4,8,16,32,64,0		;back-slash
	DB	'A',93,64,64,64,64,64,33,17,9,5,3,1	;right-bracket
	DB	'A',94,0,0,4,0,2,0,1,2,4,0,0		;caret
	DB	'D',95,64,64,64,64,64,64,64,64,64,64,64	;under-score
	DB	'A',96,0,0,0,0,0,2,1,6,9,0,0		;left-quote
	DB	'A',123,0,8,64,104,80,68,2,1,1,1,1	;left-brace
	DB	'A',124,64,32,80,32,20,2,5,2,1,0,0	;concat
	DB	'A',125,64,64,64,64,32,16,1,13,3,9,0	;right-brace
	DB	'A',126,0,4,2,1,0,7,0,4,2,1,0		;tilde
	DB	'A',127,127,127,127,127,127,127,127,127,127,127,127 ;del

Icount	Dw	(This Byte - Italics) /	13
	Page

Start:	Mov	DX,Offset Titles      ;Start-up	message
	Mov	AH,9
	Int	21h

Prompt:	Mov	AH,8		;Get char in AL, no echo
	Int	21h		; call DOS to do it
	Cmp	AL,0		;Extended code?
	Jne	ChkEsc
	Jmp	Ext		;Yes, invalid
ChkEsc:	Cmp	AL,27		; or ESCape?
	Jne	ChkLtr
	Jmp	Done		;Yes, close up

ChkLtr:	Mov	What,AL
	Cmp	AL,65		;Is it a letter?
	Jl	Number		; no, assume number
	And	AL,0DFh		;Make upper case
	Mov	What,AL
	Sub	AL,65		;Get offset
	Add	AL,10
	Jmp	Letter

Number:	Cmp	AL,57		;Valid number?
	Ja	Error		; nope
	Sub	AL,48		;To binary value
	Js	Error		;if less than zero
Letter:	Mov	SI,AX		;Save binary code
	Cmp	AL,19		;Exceeded menu list?
	Ja	Error		;Yes, oops
	Add	AL,AL		;Times 2 for indexing
	Mov	BL,AL		;Copy offset
	Sub	BH,BH		;Clear hi-byte
	Mov	CX,Word	Ptr Cmds[BX]

	Mov	AX,SI		;Get code back
	Mul	Text_Size
	Mov	BX,AX		; as index to attribute
	Mov	Text+2[BX],'1'	; and hi-lite chosen text
	Mov	Text+39[BX],'$'	; add print stopper
	Mov	DX,Offset InCase
	Mov	AH,9		;In case printer is off
	Int	21h

	Cmp	What,'I'	;Want italics?
	Jne	ChkS
	Jmp	Load_I		;Yes, invoke DLCG

ChkS:	Cmp	What,'J'	;Want Script?
	Jne	Send
	Jmp	Load_S		;Yes, invoke DLCG

Send:	Mov	DL,CL
	Mov	AH,5		;Print char in DL
	Int	21H

	Mov	DL,CH
	Mov	AH,5		;Print char in DL
	Int	21H

	Mov	CX,Offset Answer
HiLite:	Mov	DX,Offset Word Ptr Text
	Add	DX,BX		;Hi-lite selected option
	Mov	AH,9
	Int	21h

	Mov	DX,CX		;Appropriate message
	Mov	AH,9		;Confirm selection
	Int	21H
	Mov	DX,Offset Cursor
	Mov	AH,9		;Reset cursor
	Int	21h
	Jmp	Prompt		;Get another selection

Done:	Mov	AH,9
	Mov	DX,Offset End_Msg	;All Set
	Int	21h
	Ret		;Return	to DOS

Ext:	Mov	AH,8		;Get extended char
	Int	21h
Error:	Mov	AH,9
	Mov	DX,Offset Err_Msg	;Invalid entry
	Int	21h
	Jmp	Prompt

Load_I:	Mov	CX,ICount		;Number	of Italic chars
	Lea	DI,Italics		;Addr of table
	Mov	DX,Offset I_Title	;Addr of title
	Call	Dlcg			;Load character	generator
	Mov	CX,Offset I_Msg
	Jmp	HiLite

Load_S:	Mov	CX,SCount		;Number	of Script chars
	Lea	DI,Script		;Addr of table
	Mov	DX,Offset S_Title	;Addr of title
	Call	Dlcg			;Load character	generator
	Mov	CX,Offset S_Msg
	Jmp	HiLite
	Page
; Subroutine for Downline Loadable Character Generator


Dlcg	Proc	Near
	Push	AX		;Save registers
	Push	BX
	Push	CX		;Number	of entries
	Push	DI		;Addr of table
	Push	DX		;Offset	to title

	Mov	Count,CX	;Number	of characters
	Mov	AH,9		;Indicate loading DLCG
	Int	21h

	Xor	BX,BX		;Index into table
Next1:	Mov	CX,13		;For 'A' or 'D', letter, and 11	rows
	Mov	DL,27		;First an ESCape
	Mov	AH,5
	Int	21h
	Mov	DL,37		;Then DLCG command
	Mov	AH,5
	Int	21h

Rows:	Mov	DL,[DI][BX]	;Get a character
	Mov	AH,5		;Print char in DL
	Int	21H
	Inc	BX		;Next row
	Loop	Rows
	Dec	Count
	Jz	Loaded
	Jmp	Next1

Loaded:	Mov	DL,27		;Ending	ESCape
	Mov	AH,5
	Int	21h
	Mov	DL,'2'		;Set DLCG char set
	Mov	AH,5
	Int	21h

	Pop	DX		;Restore registers
	Pop	DI
	Pop	CX
	Pop	BX
	Pop	AX
	Ret			;Return	to caller
Dlcg	Endp

Set_Oki	Endp

Cseg	Ends
	End	Set
