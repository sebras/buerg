	 PAGE	 60,132
	 TITLE	 LIST --- Replace TYPE and MORE commands
;==============================================================================
; Name:     LIST, display contents of an ASCII file.
; Syntax:
;	    LIST  <[d:][path]filename[.ext]>
; Input:
;	    An ASCII file of any size may be listed, however only the
;	    first 80 bytes of each record is displayed.
;
;	    After the 'More?' prompt, enter a CR to continue, or
;	    any other character to terminate.
; Output:
;	    Logical records (ending in LF and/or CR) are placed into
;	    the screen buffer.
; Notes:
;	    Written for the IBM PC by Vernon Buerg, November 1983,
;	    and is supplied for public domain use.
;
; Revised:  Robert S. Russell, Bootstrap Creations, Walnut Creek, Calif.
;	    December 3, 1983 to allow enough space in buffer for filename
;	    so that a path may also be specified.  Also removed a bug which
;	    caused the system to lock if a carriage return is entered in
;	    response to the filename prompt.
;
;==============================================================================
;
STACK	 SEGMENT PARA STACK 'STACK'
	 DB	 128 DUP (0)
STACK	 ENDS
;
DATA	 SEGMENT PUBLIC PARA 'DATA'
ASKFILE  DB	 13,10,'Enter [d:][path]filename[.ext]:$'             ;RSR
CLEAR	 DB	 27,'[2J$'
PROMPT	 DB	 27,'[25;1H','More?$'
EOFMSG	 DB	 27,'[25;1HEnd-of-file$'
CODE2	 DB	 13,10,'File not found$'                              ;RSR
CODE4	 DB	 13,10,'Too many open files$'                         ;RSR
KEYIN	 DB	 0	      ;keyboard buffer size
KEYOUT	 DB	 0	      ;keyboard length read
FILENAME DB	 45 DUP (0)   ;drive:\path\filename.ext 	      ;RSR
HANDLE	 DW	 0	      ;file handle from open
COL	 DW	 1	      ;current display column
ROW	 DW	 2	      ;current display row
INDEX	 DW	 0	      ;offset in buffer to record
;
OPENMSG  DB	 13,10,'Open code: '                                  ;RSR
OPENCODE DW	 '00'
	 DB	 '  $'
RECLEN	 DW	 0	      ;length of current record
RECADDR  DW	 0	      ;addr of i/o buffer
;
SWITCH1  DB	 0
EOR	 EQU	 1	      ;end-of-record
SWITCH2  DB	 0
NODATA	 EQU	 2	      ;null record
NUMLF	 DB	 0	      ;line feed count
NUMCR	 DB	 0	      ;C/R count
WORK	 DB	 256 DUP (?)  ;current logical record
DATA	 ENDS
;
ZBUFFER  SEGMENT PARA PUBLIC 'BUFFER'
RECORDS  DB	 65535 DUP (?)
ZBUFFER  ENDS
;
BIOS	 SEGMENT AT 40H       ;set up labels to determine
	 ORG	 10H	      ;color or monochrome card
EQFLAG	 LABEL	 WORD
	 ORG	 4AH	      ;40 or 80 column display
NCLMS	 LABEL	 WORD
	 ORG	 63H
A6845	 LABEL	 WORD	      ;points to video card ports
BIOS	 ENDS
;
	 PAGE
CSEG	 SEGMENT PARA PUBLIC 'CODE'
	 ASSUME  CS:CSEG,DS:DATA,SS:STACK,ES:ZBUFFER
LIST	 PROC	 FAR
	 PUSH	 DS	      ;save for linkage
	 XOR	 AX,AX	      ;clear for return
	 PUSH	 AX	      ;put in stack
;
	 MOV	 AX,DATA      ;Addr of work areas
	 MOV	 DS,AX	      ;Set data segment reg
;
	 PUSH	 DS	      ;Save DS
	 XOR	 CX,CX	      ;clear hi-byte
	 MOV	 CL,BYTE PTR ES:[80H]  ;Length of command parm
	 DEC	 CL	      ;For ending CR
	 CMP	 CL,0	      ;Any parm string?
	 JLE	 GETNAME      ;No, ask for it
;
	 MOV	 SI,82H       ;Offset to command parm string
	 MOV	 DI,OFFSET FILENAME
	 MOV	 AX,DS	      ;Swap DS/ES
	 MOV	 BX,ES
	 MOV	 DS,BX	      ;Copy command string
	 MOV	 ES,AX
	 REP	 MOVSB
	 POP	 DS	      ;Restore DS
	 JMP	 OPEN
	 PAGE
;  No filename supplied with command
;
GETNAME: POP	 DS
RETRYNAME:								;RSR
	 MOV	 DX,OFFSET ASKFILE    ;Prompt for file name
	 MOV	 AH,9
	 INT	 21H
	 MOV	 AH,0AH       ;Buffered kybd input DOS req
	 MOV	 DX,OFFSET KEYIN
	 MOV	 KEYIN,44     ;Size of buffer				;RSR
	 INT	 21H
;
	 XOR	 BX,BX
	 MOV	 BL,KEYOUT    ;Number of chars read
	 CMP	 BL,0
	 JE	 RETRYNAME						;RSR
	 MOV	 FILENAME[BX],0 ;overlay CR
	 PAGE
;
OPEN:	 MOV	 DX,OFFSET FILENAME	 ;file to open
	 MOV	 AX,0	      ;for read only				;RSR
	 MOV	 AH,3DH       ;open a file
	 INT	 21H
	 MOV	 HANDLE,AX    ;save file handle
;
	 JNC	 INIT	      ;if OPEN okay
	 MOV	 DX,OFFSET CODE2
	 CMP	 AL,2	      ;is it 'file not found'?
	 JE	 ERROR
	 MOV	 DX,OFFSET CODE4					;RSR
	 CMP	 AL,4	      ;is it 'too many open files'?             ;RSR
	 JE	 ERROR
;
	 AAM
	 XCHG	 AL,AH
	 OR	 OPENCODE,AX
	 MOV	 DX,OFFSET OPENMSG
ERROR:	 MOV	 AH,9
	 INT	 21H	      ;say OPEN FAILED
	 RET
	 PAGE
;
; Initialize buffer to EOF stoppers
;
INIT:	 MOV	 BX,ZBUFFER   ;addr of I/O area
	 MOV	 RECADDR,BX   ;save it
	 MOV	 DX,OFFSET CLEAR
	 MOV	 AH,9
	 INT	 21H	      ;to clear screen
;
READAGN: MOV	 CX,65535     ;number of bytes to clear
	 MOV	 ES,RECADDR
;
STOPPER: MOV	 DI,CX
	 MOV	 ES:BYTE PTR[DI],1AH	;fill with stoppers
	 LOOP	 STOPPER
	 PAGE
;
; Read a block	(64K)
;
	 MOV	 BX,HANDLE	 ;get file handle from open
	 MOV	 DX,RECADDR	 ;offset to record buffer
	 PUSH	 DS
	 MOV	 DS,DX		 ;set data segment ptr
	 SUB	 DX,DX		 ; with zero offset
	 MOV	 CX,65534	 ;number of bytes to read
	 MOV	 AH,3FH 	 ;read from a file
	 INT	 21H
;
	 POP	 DS
;	 MOV	 BX,AX		 ;Save length read
	 MOV	 SWITCH1,0	 ;reset EOR flag
	 MOV	 INDEX,0	 ;offset into buffer
	 CMP	 AX,0		 ;Any bytes read?
	 JNE	 READ		 ;Yes, list the buffer
	 JMP	 CLOSE		 ;No, all done
;
; Set next row and column for next display line
;
READ:	 MOV	 CX,RECLEN	 ;set column and row
	 INC	 CX		 ; for next record
	 MOV	 AX,ROW
	 DEC	 AX
	 CMP	 NUMLF,0	 ;record ended in LF?
	 JE	 SET		 ;no, have col/row
	 INC	 AX		 ;yes, row stays where it is
	 MOV	 CX,1		 ; and in column 1
;
SET:	 MOV	 ROW,AX 	 ;set row
	 MOV	 COL,CX 	 ;set column
;
; Extract next logical record from display
;
GETNEXT: CALL	 SCAN_BUF	 ;Scan for logical record
	 MOV	 CX,RECLEN	 ;Record size
	 SUB	 CL,NUMLF	 ;for LF
	 SUB	 CL,NUMCR	 ;for CR
	 MOV	 RECLEN,CX
	 CMP	 CX,0		 ;blank line?
	 JE	 GETROW 	 ;yes, increment row only
;
	 LEA	 SI,WORK	 ;addr of record
	 MOV	 AX,ROW 	 ;destination row
	 CALL	 PRINT		 ;put into screen buffer
;
GETROW:  MOV	 AX,ROW 	 ;get row again
	 INC	 AX		 ;bump to next row
	 MOV	 ROW,AX 	 ;save row number
	 CMP	 AL,25		 ;exceeded screen?
	 JNE	 TESTEOR	 ;no, read next record
;
	 MOV	 DX,OFFSET PROMPT
	 MOV	 AH,9
	 INT	 21h		 ;say 'More?'
;
; Wait for keyboard input
;
	 MOV	 AH,12		 ;clear console
	 MOV	 AL,7		 ;and get a char
	 INT	 21H		 ;pause for enter
	 CMP	 AL,0DH 	 ;want to quit?
	 JNE	 CLOSE		 ;yes, clean up
;
	 MOV	 ROW,2		 ;no, reset to first row
	 MOV	 AX,ROW
;
	 MOV	 DX,OFFSET CLEAR
	 MOV	 AH,9
	 INT	 21H		 ;to clear screen
;
	 LEA	 SI,WORK	 ;addr of record
	 MOV	 AX,1		 ;put last line on top
	 MOV	 CX,RECLEN
	 CALL	 PRINT		 ;put into screen buffer
;
TESTEOR: TEST	 SWITCH1,EOR	 ;end-of-records?
	 JZ	 READ
	 JMP	 READAGN	 ;yes, read next block
;
CLOSE:	 MOV	 BX,HANDLE	 ;file handle from open
	 MOV	 AH,3EH 	 ;close a file handle
	 INT	 21H
;
	 MOV	 DX,OFFSET EOFMSG
	 MOV	 AH,9
	 INT	 21H		 ;to say done
;
	 RET
	 PAGE
SCAN_BUF PROC	 NEAR
;
; Function: Scan the buffer for special characters and copy wanted
;	 data to field WORK. A logical record ends in an LF and/or CR.
;
; Input: ZBUFFER (RECORDS) contains a block of data from the file
;	 INDEX is the current offset to a logical record
; Output:
;	 WORK contains a logical record
;	 NUMLF contains number of line feeds (ignored)
;	 NUMCR contains number of carriage returns (ignored)
;	 RECLEN contains length of logical record
; Notes: Tabs are replaced by blanks;
;	 lines beginning with hex-F are ignored
;
	 PUSH	 ES
	 PUSH	 CX
	 PUSH	 SI
	 PUSH	 DI
	 TEST	 SWITCH1,EOR
	 JZ	 SCAN1
	 JMP	 SCAN_END
;
SCAN1:	 XOR	 CX,CX
	 XOR	 DI,DI
	 AND	 SWITCH2,0FFH-NODATA
	 MOV	 NUMLF,0	 ;reset LF indicator
	 MOV	 NUMCR,0	 ;zero CR counter
	 MOV	 AX,ZBUFFER
	 MOV	 ES,AX		 ;set addr of I/O buffer segment
;
SCAN2:	 MOV	 SI,INDEX
	 MOV	 AL,RECORDS[SI]  ;Get a byte
	 CMP	 AL,1AH 	 ;End of buffer?
	 JNE	 SCAN3
	 MOV	 RECLEN,CX
	 OR	 SWITCH1,EOR	 ;Indicate end-of-records
	 JMP	 SCAN_END
;
SCAN3:	 CMP	 AL,9H		 ;Is it TAB?
	 JNE	 SCAN4
	 MOV	 AL,' '          ;Yes, replace with blank
;
SCAN4:	 MOV	 WORK[DI],AL	 ;Store character
	 INC	 DI		 ;Increment pointer
	 INC	 CX		 ;Increment counter
	 INC	 INDEX		 ;Increment counter
;
	 CMP	 AL,0DH 	 ;Is it a CR?
	 JNE	 SCAN5
	 INC	 NUMCR		 ;Yes, increment counter
SCAN5:	 CMP	 AL,' '
	 JE	 SCAN7
	 CMP	 AL,0AH 	 ;Is it line feed?
	 JNE	 SCAN6
	 INC	 NUMLF
	 JMP	 SCAN8
SCAN6:	 OR	 SWITCH2,NODATA  ;Non-space found
;
SCAN7:	 CMP	 CX,255 	 ;Record too big?
	 JE	 SCAN8		 ;Chop record at 255 bytes
	 JMP	 SCAN2
;
SCAN8:	 MOV	 RECLEN,CX
	 CMP	 WORK,0FH	 ;If record begins with "sun"
	 JNE	 SCAN9		 ; symbol, skip it
	 JMP	 SCAN1
;
SCAN9:	 TEST	 SWITCH2,NODATA  ;If nothing but spaces found,
	 JNZ	 SCAN_END	 ; read another record
	 JMP	 SCAN1
;
SCAN_END:
	 POP	 DI
	 POP	 SI
	 POP	 CX
	 POP	 ES
	 RET
;
SCAN_BUF ENDP
;
	 PAGE
	 ASSUME  CS:CSEG,DS:DATA,ES:NOTHING
PRINT	 PROC	 NEAR
	 PUSH	 ES
	 PUSH	 DI
	 PUSH	 DX
	 PUSH	 SI
;
	 MOV	 DI,COL 	 ;set column
	 DEC	 DI		 ;adjust for zero offset
	 DEC	 AX		 ;adjust row too
	 CMP	 CL,0		 ;null string?
	 JE	 EXIT		 ;if so,do nothing, Else,
;
	 MOV	 BX,BIOS	 ;get ready to determine card type
	 MOV	 ES,BX		 ;and number of columns
	 MUL	 ES:NCLMS	 ;AX = column * words per line
	 ADD	 DI,AX		 ;DI = words from start of screen
	 SHL	 DI,1		 ;adjust for attribute bytes
;
	 MOV	 DX,ES:A6845	 ;point to 6845 base port
	 ADD	 DX,6		 ;point to status port
;
;CX has the count of characters to write,
;SI points to the string data,
;DI points to a screen position
;
	 MOV	 AX,0B800H	 ;default to color card
	 MOV	 BX,ES:EQFLAG
	 AND	 BX,30H
	 CMP	 BX,30H 	 ;is it monochrome?
	 JNE	 CARDOK 	 ;no, go
	 MOV	 AX,0B000H	 ;yes, set for monochrome
CARDOK:  MOV	 ES,AX		 ;points ES to video
;
;  DS:SI => first character of string
;  ES:DI => screen memory to display it
;  CX	 => number of characters to display
;  DX	 => status port of video card
;
;-------- Wait for horzontal retrace
TESTLO:  IN	 AL,DX		 ;get status
	 TEST	 AL,1		 ;is it low?
	 JNZ	 TESTLO 	 ;no, keep checking
	 CLI			 ;turn off interrupts
TESTHI:  IN	 AL,DX		 ;get status
	 TEST	 AL,1		 ;is it high?
	 JZ	 TESTHI 	 ;no, keep checking
;-------- Okay to write to screen now (no 'hash')
	 MOVSB			 ;[DS:DI]->[ES:DI],DI++,SI++,CX--
	 INC	 DI		 ;skip the attribute byte
	 LOOP	 TESTLO 	 ;do till end of string
	 STI			 ;turn interrupts back on
;
EXIT:	 POP	 SI
	 POP	 DX
	 POP	 DI
	 POP	 ES
	 RET
;
PRINT	 ENDP
;
LIST	 ENDP
CSEG	 ENDS
;
	 END	 LIST
