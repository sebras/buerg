Page82,132
TitleTABS - Align ASCII File

Comment| Version 1.9, June 5, 1985

TABS Command
-----------------

Purpose:   Replace blanks with TAB character(s); or expand TABs.

Format [d:[input.ext]] [d:[output.ext]] [/D]

RemarkIf TABS
appear they will
not be expanded.

The /D file,

The masee MAXREC equate.
Defact9,17,25,...

WrittIBM PC using DOS 2.
For public domain use.

Notes1.6 includes a correction for the use of wildcards
to nainput file if only
a drivewas supplied for the output file name.

Version1.7 fixes a problem regarding the EOF character. It
now considers the EOF as the end of a file and will no longer
copy dathat point. Also, if wildcards are used, all
matching files are processed.

Version1.8 cleans up the messages displayed.

Version 1.9 requires the ouput file on a different drive,
or in a different path.
-|

CSePublic Para 'CODE'
AssumeCS:Cseg,DS:Cseg,ES:CSeg
Org100h

Far
;Save sto insure return

Ca;Check for DOS 2

C;Get maximum I/O buffers

Cal;Get file names

Again:
Ca;Open input

Cal; and output

Ca;Display "cooking" message

Ca;Generate tabs

C;Empty the output buffer

C;Close files

;Get next matching file
OrAL,AL
JzAgain
;All done
JmpShort Exit

ESproper return
Ca;Print any message

MovAL,to 1
AH,4Ch
Int21to DOS
Page
;
work areas

0;I/O buffer size
M51sector
M255;Longest logical record

S_3quote
D_3quote
TabEqu9
LFEqu10
CREqu13
EOFEqu1Ah
St255

Rec;Current record
SwDbof blanks skipped
QswDb0;Quote switch
;Non-zero for detab function
S0;SP at entry

Msg1DbCR,LF,'Input failed to open, '
Inp;Drive:path\name.ext
I0;Input file handle
IlenDw0;Input block length
IptrDchar
0;Seg offset

Msg2DbCR,LF,'Output failed to open, '
76 Dup (0),0,CR,LF,Stopper
Ofile handle
OlenDw0;Bytes in output buffer
OptrDchar
O0;Seg offset

8 Dup (' ')
FOffs;Addr of file name part
Offse;Spot for output file name
DTADb48;DOS data transfer area
Page
;
;Messages

V'TABS - Version 1.9 - V.Buerg',CR,LF,CR,LF
Db'Usage:  TABS  infile  outfile  [/D]',CR,LF
Db' o  infile and outfile may include drive and path names',CR,LF
Db' o  use ending /D to expand tabs to spaces.',CR,LF
Db' o  June 5, 1985; public domain.',Stopper
SorryDbCR,LF,'Wrong PC DOS Version',Stopper
Msg3fDbCR,LF,'Read error',Stopper
Msg40DbCR,LF,'Write error or Disk full.',Stopper
Msg4aDbCR,LF,'Not enough memory',Stopper
Msg4eDbCR,LF,'No matching file(s) found',Stopper
I'DE-'
C'TABS:',9,Stopper
MarkDb9,'-> ',Stopper
NCR,LF,Stopper

Code2Db'File not found ',Stopper
Code3Db'Path not found ',Stopper
Code4Db'Too many files ',Stopper
Code5Db'Access denied  ',Stopper
Page
;
blanks with tabs

GeNear
LGetRec;Get a record, length in CX
;Outputcolumn
;No blanks yet
M;No quotes yet
OrCX,CX;Any data in record?
JzNull; no, just CR-LF

SI,Of;Look for blanks and
Wlo; replace strings of blanks
IncBX; with tab characters
CmpAL;Don't count blanks
JneChkor double
; quoted strings
JmpChk2

ATABs for any
JneChk3; blanks skipped before
; a quote
Sw,0;Must re-insert
JeCheck; any blanks skipped
for a TAB

Detab,record as-is
; if de-tabbing
C;Tis a blank?
; no, see if eof
quotes?
JnzCheck
IncSw
Te;Ready for a tab?
; no, keep going
M; yes, send one
JmpCopy

CAL,EOfile?
JeDone; yes, all done
CmpDetab,0
JneCopy
non-blank is
JnzCopTAB
CmpSw,blanks
JeCopy; before it
MovDX,BX
DecDL
Tnon-blank is not
J; in a TAB column, then
Pushblanks
MovAL,Tab
CallPutChar
PopAX
; and write it
MovSw,0;Ind not blank
TlWloop
AL,CCR
CallPutChar
; and LF
CallPutChar
JmpLoop

InsAany blanks that
; didn't line up on
BlDL,column
JbNone
MovAL,' '
CallPutChar
DecDL;Decr insert count
J; and continue
AX;Get char back
JmpCopy

Done:Ret
GenTabEndp
Page
;
logicalrecord with TABs expanded

GeNear
;Targetrecord offset
;Quote indicator

;Build up a logical record
; by looking for a CR or LF
JeGet1; as end-of-record
CmpAL,LF
JeGet7
CmpAL;Don't expand tabs
JneGetwithin a
; quoted string
AL,D_Quote
JneGet3
XorQsw,2
AL,Tab;Is it TAB?
JneGet5; no, pass it
quotes?
JnzGet5; yes, pass it as-is
Reembedded tabs
IncDI; with blanks
TestDI,0007h
JzGet1
JmpGet4

Re;Build the record by
IncDI; copying each character
CmpD; or TABs expanded to blanks
JaeGet6
C;Is it EOF?
JeGet6; yes, all done
JmpGet1; no, continue
CX,DI;Final record length
Ret

Rec-1;Omit trailing blanks
JneGet6
DecDI
JzGet6
JmpGet7

GetRecEndp
Page
;
one char from record

GetNeaAL
RIlebuffer?
JsReablock
Mo; yes, get offset in buf
Lodsb
Mfor next one
Ret

RCX
MovBblock of data
MovC; into Input (segment) buffer
MovDX,In_Ptr
MovIptr,DX
MovAH,3Fh
Int21h
PopCX
Mo; and length
JcRead3
OrAX,AX;Anything read?
; yes, pick it up
M; no, return EOF
Ret

;Say I/O ERROR
JmpError
GetCharEndp
Page
;
;Block output records

PutNear;Write from AL
PushCX
Min buffer
Stosb
Mo;New buffer ptr
IncOlen
MovCX,Buflen
Cm;Full block?
J; yes, write it
WrCX
Ret

FlCX;Write data left over
Mo;Any left in output?
OrCX,CX
JnzWrite3
JmpWrite1

WriAX
PushBP
PushBX
PushDX
MovBX;Get file handle
;Save size requested
MovDX,Out_Ptr
MovOptr,DX
M;Write the block
Int21h
;Write OK?
;Wrote all data?
MovOlen,BP
; yes, good
W; no, say I/O error
JmpError

WrDX
PopBX
PopBP
PopAX
PopCX
Ret
PutCharEndp
Page

;Open input file

OpNear
MovDX,Offset Input
Mov;For input
Int21h
JncOpeni
MovDX,Offset Msg1
JmpOpenErr

OIHandle,AX
Ret
OpenInEndp

;Open output file

OpeNear
MovDX,Offset Output
;Normalfile attribute
a file
Int21h
JncOpeno
M;Oops, can't open output
JmpOpenErr

OOHandle,AX
Ret
OpenOutEndp

;Determine why OPEN failed

OpeAL,reason code
JbOpene
CmpAL,5
JaOpene
;Get offset to reason
; text failure
MovCL,4
ShlBX,CL
Ca;Say OPEN FAILED
MovDX,Offset NewLine
CallPrintS
LeaDX,Code2-32[BX]
OError

;Close input/output

CNear;Close files
MovBX; output
MovAH,3Eh
Int21h

MovBX; input
MovAH,3Eh
Int21h
Ret
CloseEndp
Page
;
;Get file names from command line

GetNear;Get file name(s)
M;Point to command line
;The PSP may contain one or two
OPtr; filenames separated by blanks
JnzGetF0
GeD;None, display usage message
JmpError

;Targetis infile for
Incoperand

Get;Copy command line to file names
C; by skipping leading blanks
a CR isfound
LoopeGetF1
Jblank

GeAL,CR;Is it CR, end of line?
JeGetFname
C;Or option string?
JeGetF1c
blank?
JeGetF2
Stosb
Lodsb
LoopGetF1a
JmpGetF5

GeA;Terminate fname operand
Stosw
Lodsb;Get option letter
option for detabbing
JeGetF1d
CmpAL,'d'
JneGetF3
GeDetab,Stopper
GetF3:
JmpGetF6

GA;Terminate fname operand
Stosw
LeaDI,fname
GetF2a:Lodsb
C;Skip intervening blanks
JneGetF2b
LoopeGetF2a
J;If no operand

GeAL,CR;Is it CR, end of line?
JeGetF5; yes, end of name
C;Or option string?
; yes, copy it
C;Or ending blank?
JeGetF2c
Stosb;Copy second operand
MovNewPtr,DI
GetF2c:Lodsb
LoopGetF2b

sign
Stosw

GetF6:
;Any input name?
; yes, try output name
J; no, display usage

GetF8:
;Find first matching file
Ge;Any output name?
; yes, further check name
CmpInp;Make sure don't over-write
JeGetFo; the input file
JmpGetUse

;If just a drive is given
; for the output
MovDI;Skip over drive
MovNewptr,DI
JmpSho; and copy as outfile name

GWord P;Drive and path?
JeGetFs; yes, append infile name
CmpBypath?
Jn; no, outfile is a filename

Gpath delimiter
MovAL,'\'
Stosb
MovNewPtr,DI
GCX,7filename
Movthe outfile spec
MovSI,FilePtr
RepMovsb
GetFend:Ret
GetFileEndp
Page
;
;Find first matching file, just cuz I'm lazy

Near;Find first matching file
;Set data xfer area
MovAH,1Ah
Int21h
Mo;Input path\filename.ext
;Searchfor first normal file
MovAH,4Eh
Int21h
JncFind1
;Say NOMATCHING FILE
JmpError

AL,Afor return
; if none found
MovDI,Offset Input
CmpByt;If drive was supplied
; leaveit in file name
AddDI,2
FB;If path was supplied
J; try to leave it in Input name
MovSI,Offset Input+75
Std
MovCX,76
Find3:Lodsb
C;Find the last separator
JeFinspec
LoopFind3
MovSI,DI

FDI,SI
AddDI,2
FiFi;Save addr of filename part
FCX,13;Copy found name to Input name
MovDI,FilePtr
Cld
Mpath name
Find7:Lodsb
Stosb
CmpAL,0;Don't want crud in message
LoopneFind7
FAL,Stopper
Stosb
;Set good return code
Ret

AH,4Fh;Get next matching file
Int21h
OrAL,AL; any more?
J; no, just return

;Re-initialize
MovSw,0
M;Reset buffer counts
MovIlen,0
MovAX;Reset buffer ptrs
MovOptr,AX
MovAX,In_Ptr
MovIptr,AX
Mov;Was output name supplied?
CmpAX,Newptr
Jne     Next1
Mov;Reset output file name
Next1:
MovCX,8;Clear message prefix
MovSI,Offset Spaces
MovDI,Offset InformD
RepMovsb
MovCooking,CR
MovCooking+1,LF

MovD;Copy input name as output name
MovCX,13
MovSI,Offset DTA+30
Next7:Lodsb
Stosb
CmpAL,0;Don't want crud in message
LoopneNext7
MovAL,Stopper
Stosb
; yes, name
Nexted:Ret
FindEndp

Page
;
"cooking" message

InNear
MovDX,Offset Cooking
CmpDetab,0
JeInform1
MovDX,Offset InformD
InfoPrintS
MovDX,Offset Input
CallPrintS
MovDX,Offset Mark
CallPrintS
MovDX,Offset Output
CallPrintS
Ret
InformEndp

ChNear
MovAH,30h
Int2or later
CmpAL,2
JaeChk9
MovDX,Offset Sorry
JmpError
Chk9:Ret
ChkVerEndp

PrNear;Print string like Int 21h (9)
PushBX;DX points to string
PushSI
MovSI,DX
PS1:Lodsb
Cmpa hex FF
JePSsign
CmpAL,zeros
JePS1
MovDL,AL
MovAH,2;Display to standard device
Int21h
JmpPS1

PS9:PopSI
PopBX
Ret
PrintSEndp

Page
;
;Allocate up to 32K per buffer by modifying memory
program.
more complicated than using data segments
buffersof allowing
;for variable buffer sizes depending upon the amount
also allows DS and ES to remain
Besides, the COM version is under 2K bytes.

ANear;Get I/O buffers
MovCX;Program size in paragraphs
MoPaddress
;My starting seg address
;Paragrthis COM program
; less code size
;Next addr

CmpBX;Can only use 64k
JbeAlloc0
MovBX,Maxcore
AlI;Seg addr for input buffer
Cmprun?
JbAlloc1
;Size less stack and PSP
AlBX,buffer
AddAX,BX
MovOu;Seg addr for output buffer

MovAX,BX
MovCL,4
;Convert to bytes
MovBufLen,AX
CmpAX;Have enough?
; nope,bye

;Convert ptrs to offsets
MovAX,In_Ptr
SubAX,DX
ShlAX,CL
MovIn_Ptr,AX
MovIptr,AX

MovAX,Out_Ptr
SubAX,DX
ShlAX,CL
MovOut_Ptr,AX
MovOptr,AX
Ret

A;Not enough memory
JmpError

AllocEndp

TabsEndp

;Cseg alength
Ma(36size
Mi32

CsegEnds
EndTabs
