' $Title:' -DELINARC-  Delete duplicate files already in ARC files' $Pagesize:74 $Linesize:132
'
'  QB delinarc/e/o/c:0;
'  LINK delinarc+qbarcv,,NUL,advbas;
'
'  Syntax:
'               delinarc [filespec] [/o]
'
100     defint a-z
        const maxfiles=512
        const true=-1, false=0

        const version$="DELINARC v1.1 - 10/10/88 - V.Buerg"

        dim fl.names$(maxfiles)        ' non-ARC files in current directory
        dim fl.date!(maxfiles)         ' file dates
        dim fl.time(maxfiles)          ' file times
        dim fl.size!(maxfiles)         ' file sizes

        on error goto error.traps

	i=instr(command$,"/O") : if i then sw.o=true ' get option switches
	i=instr(command$,"/N") : if i then sw.n=true
        cmd$=command$
        if instr(cmd$," ") then cmd$=left$(cmd$,instr(cmd$," ")-1)
        if instr(cmd$,"/") then cmd$=left$(cmd$,instr(cmd$,"/")-1)


' --- Build list of non-ARC files in directory

200     fspec$="*.*"                    ' filespec for ARCs
        if cmd$<>"" then fspec$=cmd$
        attr=0 : retcd=0
        call findfirstf (fspec$+chr$(0),attr,retcd) ' first matching file
        if retcd then
          print
          print "No files found!"
          end
        end if

get.file:
300     infile$=space$(12)              ' get first matching file
        call getnamef (infile$,flen)
        fl$=left$(infile$,flen)
        if f<maxfiles and instr(fl$,".ARC")=0 then
         f=f+1
         fl.names$(f)=fl$
         call getdatef (month,day,year)
	  fl.date!(f)=csng(year-1900)*10000!+csng(month)*100!+csng(day)
         call gettimef (hour,minute,second)
          fl.time(f)=hour*100+minute
         call getsizef (lo,hi)
          lo!=csng(lo)
          if lo<0 then lo!=lo!+65536!
          fl.size!(f)=lo!+csng(hi)*65536!
        end if

get.next.file:
400     call findnextf (retcd)          ' get next matching file
        if retcd=0 then goto get.file

        if f=0 then
          print
          print "No ";fspec$;" files found!"
          end
        end if

' ---  Get list of files within ARC files

run.arcv:
500     print
	print version$
        print
	print "Usage:  DELINARC [d:\path\filespec] [/O] [/N]
        print
        print "Where d:\path\filespec refers to subdir containing non-ARC"
        print "files that may be in ARC files in the current directory."
	print "The default is *.*."
	print "Specify /O to delete older files."
	print "Specify /N to delete files of the same name."

        print
        print "Stand-by. Getting ARC contents ..."

        shell "ARCV * >temparcv.tmp"

        i=0
getspec:
        j=i : i=instr(i+1,fspec$,"\")
        if i then goto getspec else fspec$=left$(fspec$,j)

510     open "temparcv.tmp" for input as #1
        open "delinarc.bat" for output as #2

        while not eof(1)
         line input #1,a$

         if a$=space$(len(a$)) then goto another
         if left$(a$,5)="Name " then goto another

         if left$(a$,9)="Archive: " then        ' new ARC file
           arcname$=mid$(a$,11)
           print "Checking: ";arcname$
           goto another
         end if

         if left$(a$,12)="============" then    ' directory begins
           while not eof (1)
            line input #1,a$
            if left$(a$,6)="*total" then goto another
            arc.name$=left$(a$,12)
            if instr(arc.name$," ") then arc.name$=left$(arc.name$,instr(arc.name$," ")-1)

            arc.size!=val(mid$(a$,15,8))

            day=val(mid$(a$,51,2))
            month=(instr("JanFanMarAprMayJunJulAugSepOctNovDec",mid$(a$,54,3)) +2 ) /3
            year=val(mid$(a$,58,2))
            arc.date!=csng(year)*10000!+csng(month)*100!+csng(day)

            hour=val(mid$(a$,62,2))
            minute=val(mid$(a$,65,2))
            arc.time=hour*100+minute

            for n=1 to f
             if arc.name$=fl.names$(n) then
	       if ( arc.date!=fl.date!(n) and (arc.time=fl.time(n) ) _
		or (sw.o and arc.time>fl.time(n)) )_
		or sw.n _
		or (sw.o and fl.date!(n)<arc.date!) then

                 print #2,"ERASE ";fspec$;arc.name$
		 print " ";fspec$;arc.name$;tab(17);"File: ";str$(fl.date!(n));arc.time/100;" / ARC:";arc.date!;fl.time(n)/100
                 nd=nd+1
		 exit for

               end if
             end if
            next
           wend
         end if
another:
        wend
        close #1
800     kill "temparcv.tmp"
810     print #2,"DEL DELINARC.BAT"
        close #2
        if nd=0 then
          kill "delinarc.bat"
         else
          print
          print "File DELINARC.BAT has been created in the current directory."
        end if
820     print : print nd;"duplicate files to be deleted."
        end

' --- Error recovery

error.traps:
900     if erl=510 then
          print
          print "No ARC files found!"
          beep
          end
        end if
        if erl=800 then resume 810
        if erl=810 then resume 820
        on error goto 0
        end
