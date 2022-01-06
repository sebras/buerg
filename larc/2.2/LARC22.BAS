' $title:'LARC - Attempt to make the Littlest ARC file' $pagesize:74 $linesize:132
' by Vernon D. Buerg, 2/21/87; 2/25/87 (1.1); 2/26/87 (1.2); 2/28/87 (1.3)
'                     3/01/87 (1.4); 3/15/87 (1.5); 4/14/87 (1.6)
'                     11/02/88 (1.8), 02/10/89 (1.9), 2/24/89 (2.1)
'                     3/08/89 (2.2)
'
' Purposes:
'       - make the smallest ARC files possible
'       - learn how the ADVBAS subroutines work
'       - convert LBR to ARC files
'       - evaluate compression efficiency of ARC utilities
'       - convert ARC to ZIP files
'
'     If the processed ARC file is smaller, the original ARC file
'     is replaced. The file's date and time are preserved.
'
'     If an LBR library file is encountered, it is ARC'ed. A copy
'     of LUE.COM must be available in the DOS path. If you want to
'     just convert LBR files, supply an input filespec of "*.LBR".

info.panel:
data " LARC Version 2.2 by Vernon D. Buerg"
data "
data " Usage:
data "       LARC d:[\path\]filespec  [d:\outpath]  [/A] [/P] [/C] [/L] [/R] [/Z]
data "
data "       The input file specification is required and specifies the
data "       location of ARC files to be processed. The path name is optional.
data "
data "       You MUST not have the input dir as the current dir. The current
data "       drive (and directory) is used for temporary work space. Each
data "       ARC file is extracted to the current directory.
data "
data "       You must have ARCA, PKXUNPAK and any other associated programs
data "       available from the DOS path depending on the options used.
data "
data " Options:
data "       /A specifies that ARCA should be used.
data "       /C specifies that QARC should be used.
data "       /G specifies that PAK (GSARC) should be used.
data "       /K specifies that PKARC should be used.
data "       /P specifies that PKPAK should be used.
data "       /Z specifies that PKZIP should be used
data "
data "       /L indicates that original LBR files be deleted after being converted.
data "       /R specifies that a summary report is produced in the file LARC.RPT.
data "9"

' $page $subtitle:'--- Definitions'
' ==========================================================================

	defint a-z
	maxfiles = 512
	maxmethods = 6

	dim arc$(maxfiles)		' filenames and stats for later
	dim method$(maxmethods)         ' up to four methods used
	dim savings(maxmethods)         ' total bytes saved per method
	dim create$(maxmethods,2)       ' command line for create programs
	dim sw(maxmethods)              ' indicates method is in use

	false = 0 : true = not false
	cluster = 512                   ' target disk cluster size

extract.list:
	data    ".ARC","pkunpak /r "
	data    ".LBR","lue "
	data    ".PAK","pak E /WA "
	data    ".ZIP","pkunzip -o "
	data    "9",""

create.list:
	data    "A","arca "
	data    "C","qarc -a "
	data    "G","pak A "
	data    "K","pkarc -a "
	data    "P","pkpak -a "
	data    "Z","pkzip -a -ea4 -eb4 "
	data    "",""

' $dynamic

	dim before!(maxfiles)		' original file sizes
	dim after!(maxfiles,maxmethods) ' sizes after each method
	dim stamp(maxfiles,6)           ' file mo,dy,yr;hr,min,sec

' $static

	def fneat$(x!)			' neaten number displays
	   fneat$ = right$(space$(7)+str$(x!),7)
	end def

	def fn ltrim$(x$)		' trim leading blanks
	   while left$(x$,1)=" "
	     x$=mid$(x$,2)
	   wend
	   fn ltrim$ = x$
	end def

	def fn rtrim$(x$)		' trim trailing blanks
	   while right$(x$,1)=" "
	     x$=left$(x$,len(x$)-1)
	   wend
	   fn rtrim$ = x$
	end def

	def fn trim$(x$)		' trim left and right blanks
	   fn trim$ = fn rtrim$(fn ltrim$(x$))
	end def

	def fn switch (x$)		' process option switches
	   if instr(parm$,x$) _
	     then fn switch = true : _
		  mid$(parm$,instr(parm$,x$),2)="  " _
	     else fn switch = false
	end def

' $page $subtitle: 'Initialization'
' =============================================================================

initialize:
1000    on error goto err.traps
	restore info.panel
	read version$

build.cmds:                             ' build table of codes/commands
1100    restore create.list : cmds=0
	do
	 read a$,c$
	 if a$<>"" then
	   cmds=cmds+1
	   create$(cmds,1)=a$
	   create$(cmds,2)=c$
	 end if
	loop while a$<>""

1200    call getdosv(majorv,minorv)     ' check dos version
	 if majorv<3 then print "Incorrect DOS version." : end

	parm$=command$                  ' command parameters and options
	for i=1 to cmds
	 a$=create$(i,1) : p$="/"+a$    ' option letter
	 sw(i) = fn switch (p$)
	 if sw(i) then
	   methods=methods+1 : method$(methods)=a$
	   if a$="L" then swl=true      ' special for conversions
	   if a$="Z" then swz=true
	 end if
	next

	swr = fn switch ("/R")          ' produce LARC.RPT
	swl = fn switch ("/L")          ' delete converted LBR files

	if methods=0 then               ' default to just ARCA
	  sw(1) = true
	  methods=1
	  method$(1)="A"
	end if

' get input file d:\path\filename and output drive:\path

	if instr(parm$," ") _
	  then infile$ = fn trim$(left$(parm$,instr(parm$," ")-1)) : _
	       outpath$ = fn trim$(mid$(parm$,instr(parm$," ")+1)) _
	  else infile$ = fn trim$(parm$) : _
	       outpath$ = ""

	if infile$="" then
	  restore info.panel
	  while a$<>"9"
	   print a$
	   read a$
	  wend
	  end
	end if

	if instr(infile$,".")=0 then infile$=infile$+".ARC"

	in.drive$=" "                   ' get drive letter of original files
	 if mid$(infile$,2,1) = ":" _
	   then in.drive$=left$(infile$,1) : _
		infile$=mid$(infile$,3) _
	   else print "You must supply the input drive letter!" : _
		end

	call drvspace (in.drive$,a,b,c) ' initial free space on source drive
	 before.space! = csng(a)*csng(b)*csng(c)
	 cluster = a * 512		' target disk cluster size

	inpath$=""                      ' get input drive and path names
	for i=len(infile$) to 1 step -1
	 if mid$(infile$,i,1)="\" _
	   then inpath$=left$(infile$,i) : _
		infile$=mid$(infile$,i+1): _
		exit for
	next

	temp.drive$=" "                 ' make sure different drives\paths
	 call getdrv(temp.drive$)	' for temp, input, and output

	temp.path$=string$(64,0)	' temporary d:\path
	 call getsub (temp.path$,tlen)
	 temp.path$="\"+left$(temp.path$,tlen)+"\"
	 temp.file$=temp.drive$+":"+left$(temp.path$,len(temp.path$)-1)

	call findfirstf ("*.*"+chr$(0),0,retcd)   ' insure temp is empty

	if (temp.drive$ = in.drive$ and temp.path$=inpath$) _
	     or outpath$ = temp.file$ _
	     or retcd = 0 _
	       then
	  print "Input path:  ";in.drive$+":"+inpath$
	  print "Output path: ";outpath$
	  print "Temp path:   ";temp.file$
	  print
	  print "You must use a different d:\path for the original input files,"
	  print "and the output destination drive and path;  other than the"
	  print "current directory used for the temporary work files!"
	  print "The temporary directory must be empty."
	  end
	end if

' $page $subtitle: 'Mainline'
' =============================================================================

mainline:
2000    attr = 0 : retcd=0                      ' get first file name
	arcname$=in.drive$+":"+inpath$+infile$  ' from original filespec

	call findfirstf (arcname$+chr$(0),attr,retcd)
	 if retcd then
	   print "No matching files found for ";arcname$
	   end
	 end if

' Build table of files to process

get.file:					' extract next file name
	infile$=space$(12)
	 call getnamef (infile$,flen)
	 if flen <0 _
	   then print "GETNAMEF logical error." : end _
	   else infile$=left$(infile$,flen)

	 if numfiles < maxfiles _		' save data for report
	   then numfiles=numfiles+1

	 call getdatef(month,day,year)		' preserve datestamp
	  stamp(numfiles,1)=month
	  stamp(numfiles,2)=day
	  stamp(numfiles,3)=year
	 call gettimef(hour,minute,second)
	  stamp(numfiles,4)=hour
	  stamp(numfiles,5)=minute
	  stamp(numfiles,6)=second

	 call getsizef(lo,hi)			' original file size
	  lo!=csng(lo)
	  if lo<0 then lo!=lo!+65536!
	  insize!=lo!+csng(hi)*65536!

	 arc$(numfiles)=infile$
	 before!(numfiles)=insize!
	 for method=1 to methods
	  after!(numfiles,method)=insize!
	 next method

	call findnextf (retcd)			' next file to process
	if retcd=0 then goto get.file

' $page $subtitle:'Invoke ARC processors for each archive file'
' ----------------------------------------------------------------

process:
100	for filenum=1 to numfiles
	 infile$=arc$(filenum)                  ' original file name
	 insize!=before!(filenum)		'  and file size
	 before!=insize!
	 arcname$=in.drive$+":"+inpath$+infile$    ' complete original filespec

	 outfile$=infile$			' form target file name
	 if instr(infile$,".LBR") _
	   then mid$(outfile$,instr(infile$,".LBR"),4)=".ARC"


120	method = 0				' index for method used to ARC
	if insize!<cluster then 		' skip small files?
	  for s=1 to methods
	   after!(filenum,s)=insize!
	  next
	  if outpath$ = "" _                    ' unless copying all ARC files
	    then print "Skipping small file: ";arcname$ : goto next.file
	end if

130     replaced=copies                         ' times file has been copied
	restore extract.list                    ' determine extractor name
	do
	 read a$,c$
	 if instr(arcname$,a$) then cmd$=c$+arcname$ : exit do
	loop while a$<>"9"

	cls : color 15,0 : print cmd$ : color 7,0
	shell cmd$

' create new archive file

	for m=1 to cmds                         ' Use each program
	 if sw(m) then
	  a$=create$(m,1)                        ' method letter
	  select case a$
	   case "G" : mid$(outfile$,instr(outfile$,"."),4)=".PAK"
	   case "Z" : mid$(outfile$,instr(outfile$,"."),4)=".ZIP"
	   case else :mid$(outfile$,instr(outfile$,"."),4)=".ARC"
	  end select
	  cmd$=create$(m,2)+outfile$+" *.*"      ' command line
	  cls : color 15,0 : print cmd$ : color 7,0
	  shell cmd$
	  gosub evaluate
	 end if
	next m

	if okay then kill "*.*"         ' rid extracted files

	if outpath$<>"" and _           ' insure new file is copied
	 (replaced=copies) _
	  then color 15,0 : shell "copy "+infile$+" "+outpath$ : color 7,0

	if replaced<>copies _		' delete original LBR/ZIP file
	  and ( (swl and instr(infile$,".LBR")) _
	   or   (swz and instr(infile$,".ARC")) ) _
	  then kill arcname$

next.file:
	next filenum

' $page $subtitle: 'Display file statistics'
' =============================================================================

report:
200	if swr _
	  then rptname$="larc.rpt" _
	  else rptname$="scrn:"
	   open rptname$ for output as #1

	beep					' wake em up

	if okay =0 then                         ' something broke
	  print  'locate 23,1
	  print "Aborted due to Error (";err;"at";erl;") or ESC keyin!"
	  print
	  gosub newpage
	  else gosub heading
	end if

	for i=1 to numfiles
	 if swr=0 and csrlin>22 then gosub newpage
	 print #1,arc$(i);tab(13); fneat$(before!(i));
	 for s=1 to methods
	  after=int( (after!(i,s)+cluster-1)/cluster)
	  before=int( (before!(i)+cluster-1)/cluster)
	  savings = after-before
	  savings(s)=savings(s)+savings
	  print #1,fneat$(after!(i,s));" ";fneat$(csng(savings)*cluster);
	 next s
	 print #1,
	next

	if swr=0 and csrlin>12 then gosub newpage
	 print #1,copies;"file(s) replaced";    ' Sum of savings by method
	 print #1,tab(27);" ";
	for s=1 to methods
	 print #1,fneat$(csng(savings(s))*cluster);"        ";
	next
	print #1,

	call drvspace (in.drive$,a,b,c) 	' get disk space saving
	 after.space! = csng(a)*csng(b)*csng(c)

	 print #1,
	 print #1," Free disk space: "
	 print #1,"           before ";
	 print #1,using "##,###,###";before.space!
	 print #1,"           after  ";
	 print #1,using "##,###,###";after.space!
	 print #1,"           saved  ";after.space! - before.space!;"bytes"

	close #1				' all done


	if swr then
	 open rptname$ for input as #1		' display the report
	 while not eof (1)			'  in addition to writing it to
	  line input #1,a$			'   the file to LARC.RPT
	  print a$
	 wend
	 close #1
	end if

	end

newpage:
	line input "Press ENTER to continue:";a$
heading:
	cls					' pretty fancy, eh?
	print #1,version$;" - Processing ";command$
	 print #1,
	 print #1,"Filename";tab(14);"before";
	 for s=1 to methods
	  print #1,"  after  ";method$(s);"-diff";
	 next
	print #1,
	locate ,1
	return

' $page $subtitle: 'Evaluate results of re-ARCing the files'
' ---------------------------------------------------------

evaluate:
	okay = 0				' indicates success or not
	if inkey$ = chr$(27) then return report ' aborted by ESCape key
	okay = 1
	method = method + 1

300	open outfile$ for input as #2		' get new file size
	 outsize!=lof(2)
	 close #2

310	after!(filenum,method)=outsize!

	'after=int( (outsize!+cluster-1)/cluster) ' compute clusters saved
	'before=int( (before!+cluster-1)/cluster)
	savings! = outsize! - before!		  ' bytes (was clusters) saved

400     if savings! <0 or outpath$<>"" or swz or swl then

	 call setftd(outfile$+chr$(0),stamp(filenum,1),stamp(filenum,2), _
		     stamp(filenum,3),stamp(filenum,4),stamp(filenum,5), _
		     stamp(filenum,6) ) 	' preserve date stamp

	 if outpath$="" _               ' overlay original or to another subdir
	   then cmd$= "copy "+outfile$+" "+in.drive$+":"+inpath$+outfile$ _
	   else cmd$= "copy "+outfile$+" "+outpath$

	 color 15,0 : print cmd$ : color 7,0
	 shell cmd$
	 before!=outsize!		' new original file size
	 copies=copies+1
	end if

410     kill outfile$                   ' rid the temporary ARC file
copy.done:
	return

copy.failed:
	okay = 0
	return report 'next.file                ' file not found, not created, etc.

err.traps:
	if erl=100 then print arcname$;" not found"
	if erl=410 then resume copy.done	' short file only copied
	if erl=300 then
	  print "Copy failed! Not enough disk space." : beep
	  resume copy.failed      ' no ARC created
	end if
	print "Error";err;"at line";erl
	end
