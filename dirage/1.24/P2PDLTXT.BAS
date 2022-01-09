rem $title:'P2PDLTXT - Convert CALLERS to DOWNLOAD.TXT file'

	defint a-z
	const true=-1, false=0

100	print "P2PDLTXT - Convert PCBoard CALLERS to PCBoard DL.TXT - V1.0, 8/09/88, V.Buerg"
	print

	on error goto errors

200	cmd$=command$
210	if cmd$="" then
	  print "Usage:"
	  print "       P2PDLTXT [caller file name]  [/A] [/L]"
	  print "Where:"
	  print "       use /A to append DOWNLOAD.TXT entries to ";dltxt$
	  print "       use /L to display download entries"
	  print
	  end
	 end if

220	j=instr(cmd$,"/")                       ' any switches?
	if j then
	  i=instr(cmd$,"/A")                    ' append option?
	  if i then sw.append=true
	  if instr(cmd$,"/L") then sw.list=true
	  cmd$=left$(cmd$,j-1)
	end if

	dltxt$="DOWNLOAD.TXT"                   ' default file names
	callers$="CALLERS"

230	if cmd$<>"" then                        ' get command line file names
	  i=instr(cmd$," ")
	  if i then
	    callers$=left$(cmd$,i-1)
	    dltxt$=mid$(cmd$,i+1)
	   else
	    callers$=cmd$
	  end if
	end if

300     open callers$ for input as #1
	fsz!=lof(1)

310	if sw.append then
	  open dltxt$ for append as #2
	 else
	  open dltxt$ for output as #2
	end if

	if sw.list=false then print : print "Converting '";callers$;"' to '";dltxt$;"'. (Press ESCape to abort)"

400	while not eof (1)			' read CALLERS file
	 line input #1,r$
	 if inkey$=chr$(27) then end
	 rsz!=loc(1) : pc=cint(rsz!*12800!/fsz!)
	 if pc <> oldpc then locate ,30 : print pc;"%"; : oldpc=pc

	 if left$(r$,6)=space$(6) then          ' detail record
	   t$=mid$(r$,7,3)
	   if t$="(D)" or t$="(U)" then
	     filenm$=mid$(r$,11,12)
	     i=instr(filenm$," ")
	     if i then filenm$=left$(filenm$,i-1)
	     i=instr(r$," using ")
	     if i then prot$=mid$(r$,i+7,1) else prot$="?"
	     i=instr(r$,"T/E=")
	     if i then errors$=str$(val(mid$(r$,i+4))) else errors$=" 0"
	     i=instr(r$,"CPS=")
	     if i then cps$=str$(val(mid$(r$,i+4))) else cps$=" 0"
	     timedl$=timeon$
	     if sw.list then print "         ";timedl$;" ";filenm$;" ";prot$
	     print #2,t$;",";userid$;",";dateon$;",";timeon$;",";filenm$;",";prot$;",";str$(val(errors$));" ,";str$(val(cps$))
	     if t$="(D)" then d=d+1 else if t$="(U)" then u=u+1
	     goto more
	   end if
	 else                                   ' logon record
	  if instr(22,r$,"Off Normally")=0 _
	   and mid$(r$,3,1)="-" and mid$(r$,6,1)="-" and mid$(r$,10,1)="(" _
	   and mid$(r$,13,1)=":" and mid$(r$,16,1)=")" then
	    if mid$(r$,18,1)="(" then userid$=mid$(r$,22) else userid$=mid$(r$,18)
	    i=instr(userid$," (")
	    if i then userid$=left$(userid$,i-1)
	    dateon$=left$(r$,8)
	    timeon$=mid$(r$,11,5)
	    if sw.list then print dateon$;" ";timeon$;" ";left$(userid$+space$(30),32)
	    goto more
	   end if
	 end if

more:
450	wend
460	close #1,#2
	print
	print d;"downloads."
	print u;"uploads."
	end

errors:
500	print r$
	on error goto 0
	end

