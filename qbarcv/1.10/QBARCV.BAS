'$page $subtitle:'QBARCV example - LA command'
'
' input:
'   - set FILE$ to the LA argument, the name of an ARC file
'   - include completely qualified drive and path names unless
'     a FILEPATH utility is in use
' output:
'   - the file TEMPARC.DIR is created by the QBARCV subroutine,
'     it contains either a verbose directory listing, or an
'     error message
'   - the RETCD return code contains:
'          0 = okay,  1 = error,  2 = file not found

list.arc.dir: ' Uses Vern's QBARCV assembler sub. 8-7-86.

if q < 2 _
  then _
    gosub send : _
    a$ = "Enter ARChive file name [.ARC] " : _
    gosub receive : _
    arc$ = b$(1) _
  else _
    arc$ = b$(2)

if arc$ = "" then goto files.menu
 arc$ = fn cap.strip$(arc$)
if instr(arc$,".") = 0 then arc$ = arc$ + ".ARC"
 file$ = arc$
 z$ = arc$
 gosub protection.check
if protected then goto files.menu
 a$ = "Please wait. Extracting " + qu$ + file$ + qu$ + " ..."
 gosub send2
 retcode% = 0

call arcv(file$,retcode%)

if retcode% _
  then
    gosub send
    a$ = "Sorry " + first$ + ", but an error occured while trying to do an ARCV"
    gosub send
    a$ = "on file " + qu$ + file$ + qu$ + ". Please leave " + sys1stnam$ + _
	 " a message about it."
    gosub send
    gosub press.enter
    goto files.menu
end if

file$ = "temparc.dir" ' Again, don't use a PATH!
gosub send.file
gosub send
a$ = "End of directory. "
gosub send1
kill file$
gosub press.enter
goto files.menu

