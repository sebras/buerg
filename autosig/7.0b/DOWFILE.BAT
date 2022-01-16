@ECHO OFF
:: Based on original Dowfile by Doug Williams [70511,51]
:: v2.0 Modified by Dave Konkel [72241,1603] to add multi-forum capabilities
:: v3.0 Further modified by Dave Konkel to allow
::  1) running autopasses after downloading terminates
::  2) use of "/A" (Append) switch to generate scripts longer than possible
::        with a single 127 character dowfile command. 
IF "%1"=="" GOTO EXPLAIN
IF "%1"=="?" GOTO EXPLAIN
IF "%1"=="/A" GOTO APPEND
IF "%1"=="/a" GOTO APPEND
IF "%1"=="/AS" GOTO APPEND
IF "%1"=="/as" GOTO APPEND
ECHO LOGON '%1' > dowfile.scr
:START
ECHO SENDLINE 'Lib %2' >> DOWFILE.SCR
ECHO MATCH '!' >> DOWFILE.SCR
:CONT
ECHO DOW %3 >> DOWFILE.SCR
:CONT2
ECHO MATCH '!' >> DOWFILE.SCR
IF "%4"=="/AP1" GOTO AP1
IF "%4"=="/ap1" GOTO AP1
IF "%4"=="/AP2" GOTO AP2
IF "%4"=="/ap2" GOTO AP2
IF "%4"=="" GOTO END
IF "%4"=="%2" GOTO SAMELIB
SHIFT
SHIFT
IF "%2"=="F" GOTO NEXTF
IF "%2"=="f" GOTO NEXTF
IF "%2"=="G" GOTO NEXTG
IF "%2"=="g" GOTO NEXTG
ECHO DOW %3 LIB:%2 >> DOWFILE.SCR
GOTO CONT2
:SAMELIB
SHIFT
SHIFT
GOTO CONT
:APPEND
TYPE DOWFILE.SCR | FIND /V "LOGOFF" > DOWFILE.TMP
DEL DOWFILE.SCR
REN DOWFILE.TMP DOWFILE.SCR
IF "%1"=="/as" GOTO START
IF "%1"=="/AS" GOTO START
SHIFT
ECHO LOGON '%1' >> DOWFILE.SCR
GOTO START
:AP1
ECHO EXIT 1 >> DOWFILE.SCR
GOTO STOP
:AP2
ECHO EXIT 2 >> DOWFILE.SCR
GOTO STOP  
:END
ECHO LOGOFF >> DOWFILE.SCR
GOTO STOP
:NEXTF
SHIFT
SHIFT
ECHO LOGON '%1' >> dowfile.scr
GOTO START
:NEXTG
SHIFT
SHIFT
ECHO SENDLINE 'GO %1' >> DOWFILE.SCR
ECHO MATCH 'Forum !' >> DOWFILE.SCR
GOTO START
:EXPLAIN
ECHO  +*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*+
ECHO  + The syntax is: DOWFILE [/A] forum1 lib#1 file1 [lib #2 file2]...      +
ECHO  +  [F forumname2 lib#1 file#1 lib#2 file#2 ... etc]                     +
ECHO  +  [G forumname3 lib#1 file#1 lib#2 file#2 ... etc]... [/AP1] [/AP2]    +
ECHO  + This creates a script that will download file1 from forum #1 lib#1,   +
ECHO  +  file2 from Lib#2 (specify the Lib# even if file2 is also in Lib#1),  +
ECHO  +  then go to forum#2, download file #1 from Lib #1, etc...             +
ECHO  + The optional /AP1 or /AP2 switch after the last filename tells ATO to +
ECHO  +  run Autopass 1 or 2 after the last DL; otherwise you're logged off.  +
ECHO  + To generate a script that will DL more files than can be specified by +
ECHO  +  a single DOS command line (which has a 127 character limit), you can +
ECHO  +  run DOWFILE more than once, as long as an optional /A (append) switch+
ECHO  +  precedes forumname 1 on all but the first instance of DOWFILE needed +
ECHO  +  to generate a given Script.  Note that forum1 or 2 must be in your   +
ECHO  +  Autosig.dfn file; a Forumname after a G switch need only be a valid  +
ECHO  +  CIS Goword (and may include a Service Prefix, e.g. "ZNT:")           +
ECHO  +                                                                       +
ECHO  +   To run the script file, at the command line enter AUTOSIG /XDOWFILE +
ECHO  +_______________________________________________________________________+
ECHO  + (DOWFILE.BAT creates a script file, dowfile.scr, that is overwritten  +
ECHO  + each time DOWFILE.BAT is used (without a /A switch).  Make sure that  +
ECHO  + dowfile.scr is on your path or in the same directory as Autosig.      +
ECHO  +=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*=*DAK*72241,1603=*=*=*=*=*=*=*=+
:stop
