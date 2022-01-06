' $title:'LARC - Attempt to make the Littlest ARC file' $pagesize:74 $linesize:132
' by Vernon D. Buerg, 2/21/87; 2/25/87 (1.1); 2/26/87 (1.2); 2/28/87 (1.3)
'                     3/01/87 (1.4); 3/15/87 (1.5)
'
' Purpose:
'       - make the smallest ARC files possible
'       - learn how the ADVBAS subroutines work
'       - convert LBR to ARC files
'       - evaluate compression efficiency of ARC utilities
'
' Usage:
'       LARC d:[\path\]filespec  [d:\outpath]  [/A] [/P] [/C] [/L] [/R]
'
'       The input file specification is required and specifies the
'       location of ARC files to be processed. The path name is optional.
'
'       You MUST not have the input dir as the current dir. The current
'       drive (and directory) is used for temporary work space. Each
'       ARC file is extracted to the current directory.
'
'       If the processed ARC file is smaller, the original ARC file
'       is replaced. The file's date and time are preserved.
'
'       If an LBR library file is encountered, it is ARC'ed. A copy
'       of LUE.COM must be available in the DOS path. If you want to
'       just convert LBR files, supply an input filespec of "*.LBR".
'
'       You must have ARCA, PKXARC and PKARC accessible from the DOS path
'       depending on the options /A, /P, and /C supplied.
'
' Options:
'       /A specifies that ARCA should be used.
'       /P specifies that PKARC should be used.
'       /C specifies that ARC should be used.
'       /R specifies that a summary report is produced in the file LARC.RPT.
'       /L indicates that original LBR files be deleted after being converted.
' ==========================================================================
' Definitions

	defint a-z
	dim arc$(1000)                  ' filenames and stats for later
	dim method$(3)                  ' up to three methods used
	dim savings(3)                  ' total bytes saved per method

	version$="LARC Version 1.5"     ' some internal signs
	author$="by Vernon D. Buerg"

	false = 0 : true = not false
	cluster = 512                   ' target disk cluster size

	 ' $dynamic
	dim before!(1000)               ' original file sizes
	dim after!(1000,3)              ' sizes after each method
	dim stamp(1000,6)               ' file mo,dy,yr;hr,min,sec
	 ' $static

	def fneat$(x!)                  ' neaten number displays
	   fneat$ = right$(space$(8)+str$(x!),8)
	end def

	def fn ltrim$(x$)               ' trim leading blanks
	   while left$(x$,1)=" "
	     x$=mid$(x$,2)
	   wend
	   fn ltrim$ = x$
	end def

	def fn rtrim$(x$)               ' trim trailing blanks
	   while right$(x$,1)=" "
	     x$=left$(x$,len(x$)-1)
	   wend
	   fn rtrim$ = x$
	end def

	def fn trim$(x$)                ' trim left and right blanks
	   fn trim$ = fn rtrim$(fn ltrim$(x$))
	end def

	def fn switch (x$)              ' process option switches
	   if instr(parm$,x$) _
	     then fn switch = true : _
		  mid$(parm$,instr(parm$,x$),2)="  " _
	     else fn switch = false
	end def

' $page $subtitle: 'Initialization'
' =============================================================================

initialize:
	on error goto err.traps

	call getdosv(majorv,minorv)     ' check dos version
	 if majorv<3 then print "Incorrect DOS version." : end

	parm$=command$                  ' command parameters and options
	swa = fn switch ("/A")          ' use ARCA
	swp = fn switch ("/P")          ' use PKARC
	swc = fn switch ("/C")          ' use ARC
	swr = fn switch ("/R")          ' produce LARC.RPT
	swl = fn switch ("/L")          ' delete converted LBR files

	if not swa and not swp and not swc _
	  then swa=true                 ' default to just ARCA

	method=0                        ' index to method name
	if swp then method=method+1 : method$(method)="P"
	if swa then method=method+1 : method$(method)="A"
	if swc then method=method+1 : method$(method)="C"

					' get input file d:\path\filename
	if instr(parm$," ") _           ' and output drive:\path
	  then infile$ = fn trim$(left$(parm$,instr(parm$," ")-1)) : _
	       outpath$ = fn trim$(mid$(parm$,instr(parm$," ")+1)) _
	  else infile$ = fn trim$(parm$) : _
	       outpath$ = ""

	if infile$="" then print "Input filespec missing!" : end

	if instr(infile$,".")=0 then infile$=infile$+".ARC"


	in.drive$=" "                   ' get drive letter of original files
	 if mid$(infile$,2,1) = ":" _
	   then in.drive$=left$(infile$,1) : _
		infile$=mid$(infile$,3) _
	   else print "You must supply the input drive letter!" : _
		end

	call drvspace (in.drive$,a,b,c) ' initial free space on source drive
	 before.space! = csng(a)*csng(b)*csng(c)
	 cluster = a * 512              ' target disk cluster size

	inpath$=""                      ' get input drive and path names
	for i=len(infile$) to 1 step -1
	 if mid$(infile$,i,1)="\" _
	   then inpath$=left$(infile$,i) : _
		infile$=mid$(infile$,i+1) _
	   else next

	temp.drive$=" "                 ' make sure different drives\paths
	 call getdrv(temp.drive$)       ' for temp, input, and output

	temp.path$=string$(64,0)        ' temporary d:\path
	 call getsub (temp.path$,tlen)
	 temp.path$="\"+left$(temp.path$,tlen)+"\"
	 temp.file$=temp.drive$+":"+left$(temp.path$,len(temp.path$)-1)

	if (temp.drive$ = in.drive$ and temp.path$=inpath$) _
	     or outpath$ = temp.file$ then
	  print "Input path:  ";in.drive$+":"+inpath$
	  print "Output path: ";outpath$
	  print "Temp path:   ";temp.file$
	  print
	  print "You must use a different d:\path for the original input files,"
	  print "and the output destination drive and path;  other than the"
	  print "current directory used for the temporary work files!"
	  end
	end if

' $page $subtitle: 'Mainline'
' =============================================================================

mainline:
	attr = 0 : retcd=0                      ' get first file name
	arcname$=in.drive$+":"+inpath$+infile$  ' from original filespec

	call findfirstf (arcname$+chr$(0),attr,retcd)
	 if retcd then
	   print "No matching files found for ";arcname$
	   end
	 end if

' Build table of files to process

get.file:                                       ' extract next file name
	infile$=space$(12)
	 call getnamef (infile$,flen)
	 if flen <0 _
	   then print "GETNAMEF logical error." : end _
	   else infile$=left$(infile$,flen)

	numfiles=numfiles+1                     ' save data for report

	 call getdatef(month,day,year)          ' preserve datestamp
	  stamp(numfiles,1)=month
	  stamp(numfiles,2)=day
	  stamp(numfiles,3)=year
	 call gettimef(hour,minute,second)
	  stamp(numfiles,4)=hour
	  stamp(numfiles,5)=minute
	  stamp(numfiles,6)=second

	 call getsizef(lo,hi)                   ' original file size
	  lo!=csng(lo)
	  if lo<0 then lo!=lo!+65536!
	  insize!=lo!+csng(hi)*65536!

	 arc$(numfiles)=infile$
	 before!(numfiles)=insize!
	 for method=1 to 3
	  after!(numfiles,method)=insize!
	 next method

	call findnextf (retcd)                  ' next file to process
	if retcd=0 then goto get.file


' $page $subtitle:'Invoke ARC processors for each archive file'
' ----------------------------------------------------------------

process:
100     for filenum=1 to numfiles
	 infile$=arc$(filenum)                  ' original file name
	 insize!=before!(filenum)               '  and file size
	 before!=insize!
	 arcname$=in.drive$+":"+inpath$+infile$    ' complete original filespec

	 outfile$=infile$                       ' form target file name
	 if instr(infile$,".LBR") _
	   then mid$(outfile$,instr(infile$,".LBR"),4)=".ARC"


120     method = 0                              ' index for method used to ARC

	if insize!<cluster then                 ' skip small files?
	  for s=1 to 3
	   after!(filenum,s)=insize!
	  next
	  if outpath$ = "" _                    ' unless copying all ARC files
	    then goto next.file
	end if

	replaced=copies                         ' times file has been copied

	if instr(arcname$,".LBR") _             ' extract the file
	  then cmd$="lue "+arcname$ _
	  else cmd$="pkxarc /r "+arcname$
	 cls
	 shell cmd$

	if swp then
	 cmd$="pkarc a "+outfile$+" *.*"        ' comparison to pk
	 cls
	 shell cmd$
	 gosub evaluate
	end if

	if swa then
	cmd$="arca "+outfile$+" *.*"            ' and to arca
	 cls
	 shell cmd$
	 gosub evaluate
	end if

	if swc then                             ' and to SEA ARC
	 cmd$="arc -a "+outfile$+" *.*"
	 cls
	 shell cmd$
	 gosub evaluate
	end if

	kill "*.*"                              ' rid extracted files

	if swl and instr(arcname$,".LBR") and replaced<>copies _
	  then kill arcname$            ' delete original LBR file

	if outpath$<>"" and replaced=copies _   ' did not copy it yet?
	  then shell "copy "+arcname$+" "+outpath$

next.file:
	next filenum

' $page $subtitle: 'Display file statistics'
' =============================================================================

report:
200     if swr _
	  then rptname$="larc.rpt" _
	  else rptname$="scrn:"

	open rptname$ for output as #1
	gosub heading

	for i=1 to numfiles
	 if swr=0 and csrlin>22 then gosub newpage
	 print #1,arc$(i);tab(15); fneat$(before!(i));
	 for s=1 to method
	  after=int( (after!(i,s)+cluster-1)/cluster)
	  before=int( (before!(i)+cluster-1)/cluster)
	  savings = after-before
	  savings(s)=savings(s)+savings
	  print #1,fneat$(after!(i,s)); fneat$(csng(savings)*cluster);
	 next s
	 print #1,
	next

	if swr=0 and csrlin>12 then gosub newpage
	 print #1,copies;"file(s) replaced";    ' Sum of savings by method
	 print #1,tab(30);" ";
	for s=1 to method
	 print #1,fneat$(csng(savings(s))*cluster);"        ";
	next
	print #1,

	call drvspace (in.drive$,a,b,c)         ' get disk space saving
	 after.space! = csng(a)*csng(b)*csng(c)

	 print #1,
	 print #1," Free disk space: "
	 print #1,"           before ";
	 print #1,using "##,###,###";before.space!
	 print #1,"           after  ";
	 print #1,using "##,###,###";after.space!
	 print #1,"           saved  ";after.space! - before.space!;"bytes"

	close #1                                ' all done
	beep                                    ' wake em up

	if swr then
	 open rptname$ for input as #1          ' display the report
	 while not eof (1)                      '  in addition to writing it to
	  line input #1,a$                      '   the file to LARC.RPT
	  print a$
	 wend
	 close #1
	end if

	end

newpage:
	line input "Press ENTER to continue:";a$
heading:
	cls                                     ' pretty fancy, eh?
	print #1,version$;" - Processing ";command$
	 print #1,
	 print #1,"Filename";tab(15);"  before";
	 for s=1 to method
	  print #1,"  after";method$(s);"    diff";
	 next
	print #1,
	locate ,1
	return

' $page $subtitle: 'Evaluate results of re-ARCing the files'
' ---------------------------------------------------------

evaluate:
	method = method + 1
300     open outfile$ for input as #2           ' get new file size
	 outsize!=lof(2)
	 close #2

310     after!(filenum,method)=outsize!

	'after=int( (outsize!+cluster-1)/cluster) ' compute clusters saved
	'before=int( (before!+cluster-1)/cluster)
	savings! = outsize! - before!             ' bytes (was clusters) saved

400     if savings! <0 or (outpath$<>"" and method=1) then

	 call setftd(outfile$+chr$(0),stamp(filenum,1),stamp(filenum,2), _
		     stamp(filenum,3),stamp(filenum,4),stamp(filenum,5), _
		     stamp(filenum,6) )         ' preserve date stamp

	 if outpath$="" _               ' overlay original or to another subdir
	   then cmd$= "copy "+outfile$+" "+in.drive$+":"+inpath$+outfile$ _
	   else cmd$= "copy "+outfile$+" "+outpath$

	 shell cmd$

	 before!=outsize!               ' new original file size
	 copies=copies+1
	end if

410     kill outfile$                   ' rid the temporary ARC file
copy.done:
	return

copy.failed:
	return next.file                ' file not found, not created, etc.


err.traps:
	if erl=100 then print arcname$;" not found"
	if erl=410 then resume copy.done        ' short file only copied
	if erl=300 then resume copy.failed      ' no ARC created
	print "Error";err;"at line";erl
	end
