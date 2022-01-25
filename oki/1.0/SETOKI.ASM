        TITLE   SET_OKI PRINTER MODES
        PAGE    80,132

; THIS PROGRAM SENDS CONTROL CHARACTERS TO AN OKIDATA MICROLINE 92
; PRINTER CONNECTED AS LPT1.
;
; THE USER IS PRESENTED WITH A MENU OF 16 ITEMS. ANY NUMBER OF
; CONTROL FUNCTIONS MAY BE PERFORMED.
;
; DOS 2.00 WITH ANSI.SYS IS REQUIRED.

CSEG    SEGMENT PARA PUBLIC 'CODE'
        ORG     100H

SET_OKI PROC    FAR
        ASSUME  CS:CSEG,DS:CSEG,ES:NOTHING
SET:    PUSH    DS
        XOR     AX,AX   ;SET RETURN CODE
        PUSH    AX
        PUSH    CS      ;SET DATA SEG
        POP     DS

        MOV     DX,OFFSET TITLES      ;START-UP MESSAGE
        MOV     AH,9
        INT     21H

PROMPT: MOV     AH,8  pe"w*:hr AAL NNO ECHO
        INT     21H     ; CALL DOS TO DO IT
        CMP     AL,0    ;EXTENDED CODE?
        JE      ERROR   ;YES, INVALID
        CMP     AL,27   ; OR ESCAPE?
        JE      DONE

        MOV     WHAT,AL
        CMP     AL,97   ;IS IT LOWER CASE
        JL      UPPER   ; NO, SEE IF LETTER
        SUB     AL,97   ;FORM OFFSET
        ADD     AL,10   ; ADJUST FOR LETTER CODE
        JMP     LETTER

UPPER:  CMP     AL,65   ;IS IT A LETTER?
        JL      NUMBER  ; NO, ASSUME NUMBER
        SUB     AL,65   ;GET OFFSET
        ADD     AL,10
        JMP     LETTER

NUMBER: CMP     AL,57   ;VALID NUMBER?
        JA      ERROR   ; NOPE
        SUB     AL,48   ;TO BINARY VALUE
        JS      ERROR   ;IF LESS THAN ZERO
LETTER: MOV     SI,AX   ;SAVE BINARY CODE
        CMP     AL,15   ;EXCEEDED MENU LIST?
        JA      ERROR   ;YES, OOPS
        ADD     AL,AL   ;TIMES 2 FOR INDEXING
        MOV     BL,AL   ;COPY OFFSET
        SUB     BH,BH   ;CLEAR HI-BYTE
        MOV     CX,WORD PTR CMDS[BX]

        MOV     AX,SI   ;GET CODE BACK
        MUL     TEXT_SIZE
        MOV     BX,AX   ; AS INDEX TO ATTRIBUTE
        MOV     TEXT+2[BX],'1'  ; AND HI-LITE CHOSEN TEXT
        MOV     TEXT+39[BX],'$' ; AND PRINT STOPPER

        MOV     DL,CL
        MOV     AH,5    ;PRINT CHAR IN DL
        INT     21H

        MOV     DL,CH
        MOV     AH,5    ;PRINT CHAR IN DL
        INT     21H

        MOV     DX,OFFSET WORD PTR TEXT
        ADD     DX,BX   ;HI-LITE SELECTED OPTION
        MOV     AH,9
        INT     21H
        MOV     DX,OFFSET ANSWER
        MOV     AH,9    ;CONFIRM SELECTION
        INT     21H
        JMP     PROMPT  ;GET ANOTHER SELECTION

ERROR:  MOV     AH,9
        MOV     DX,OFFSET ERR_MSG       ;INVALID ENTRY
        INT     21H
        JMP     PROMPT

DONE:   MOV     AH,9
        MOV     DX,OFFSET END_MSG       ;ALL SET
        INT     21H
        RET             ;RETURN TO DOS
        PAGE
TEXT_SIZE DB    40      ;LENGTH OF SELECTION ITEMS
TITLES  DB      27,'[2J',27,'[=2H',27,'[0M'
VERSION DB      'SET OKIDATA(R) PRINTER - VER. 1.0'
        DB      27,'[1;41H (C) 1984 VERNON D. BUERG'
;        EACH ENTRY MUST BE 40 BYTES AND IN NUMBER SEQUENCE
TEXT    DB      27,'[0M',27,'[3;1H0 = SIX (6) LPI               ';2754
        DB      27,'[0M',27,'[4;1H1 = PICA 10 CPI               ';3000
        DB      27,'[0M',27,'[5;1H2 = ELITE 12 CPI              ';2800
        DB      27,'[0M',27,'[6;1H3 = CONDENSED 17 CPI          ';2900
        DB      27,'[0M',27,'[7;1H4 = CORRESPONDENCE QUALITY    ';2749
        DB      27,'[0M',27,'[8;1H5 = EMPHASIZED PRINT          ';2784
        DB      27,'[0M',27,'[9;1H6 = STOP ENHANCED/EMPHASIZE   ';2773
        DB      27,'[0M',27,'[10;1H7 = UNDERLINED               ';2767
        DB      27,'[0M',27,'[3;41H8 = EIGHT (8) LPI            ';2756
        DB      27,'[0M',27,'[4;41H9 = DOUBLE PICA, 5 CPI       ';3031
        DB      27,'[0M',27,'[5;41HA = DOUBLE ELITE, 6 CPI      ';2831
        DB      27,'[0M',27,'[6;41HB = DOUBLE CONDENSED, 8.5CPI ';2931
        DB      27,'[0M',27,'[7;41HC = DATA PROCESSING QUALITY  ';2748
        DB      27,'[0M',27,'[8;41HD = ENHANCED PRINT           ';2772
        DB      27,'[0M',27,'[9;41HE = FORM FEED                ';1200
        DB      27,'[0M',27,'[10;41HF = STOP UNDERLINING        ';2768

MSG     DB      27,'[14;18HENTER SELECTION =>     '
        DB      27,'[17;18HESCAPE TO EXIT'
        DB      27,'[14;37H$'

ANSWER  DB      27,'[0M',27,'[15;18H'
WHAT    DB      0,' HAS BEEN PROCESSED',27,'[14;37H $'

ERR_MSG DB      07,27,'[1M',27,'[15;18HINVALID ENTRY           '
        DB      27,'[0M',27,'[14;37H $'

END_MSG DB      27,'[19;20H',27,'[1M ALL SET',27,'[0M$'

CMDS    DB      27,54 ;0        TWO BYTE DECIMAL CODES
        DB      30,00 ;1        REFER TO USER'S MANUAL
        DB      28,00 ;2
        DB      29,00 ;3
        DB      27,49 ;4
        DB      27,84 ;5
        DB      27,73 ;6
        DB      27,67 ;7
        DB      27,56 ;8
        DB      30,31 ;9
        DB      28,31 ;A
        DB      29,31 ;B
        DB      27,48 ;C
        DB      27,72 ;D
        DB      12,00 ;E
        DB      27,68 ;F

SET_OKI ENDP
CSEG    ENDS
        END     SET
