' $title:'Sort DOWNLOAD.TXT - Extract (U) records, delete dupes'
defint a-z
print "SORT DOWNLOAD.TXT - 8/08/88 - V.Buerg" : Print : print "Reading:";

open command$ for input as #1
open "dl.new" for output as #2
' (D)|(U),user-name,mm-dd-yyyy,hh:mm,filename,p[,n,n,n]
while not eof(1)
 line input #1,a$
 b$=left$(a$,4)
 select case b$
  case "(D),"
   i1=instr(a$,",")       ' position of name
   i2=instr(i1+1,a$,",")  ' position of date
   i3=instr(i2+1,a$,",")  ' position of time
   i4=instr(i3+1,a$,",")  ' position of filename
   flnm$=mid$(a$,i4+1,12)
   i=instr(flnm$,",") : if i then flnm$=left$(flnm$,i-1)
   i=instr(flnm$,".") : if i then flnm$=left$(flnm$,i-1)+mid$(flnm$,i+1)
   flnm$=left$(flnm$+space$(11),11)
   n=n+1
   x$=chr$(val(mid$(a$,i2+1,2))+128)+chr$(val(mid$(a$,i2+4,2))+128) _     ' date
       + chr$(val(mid$(a$,i3+1,2))+128) + chr$(val(mid$(a$,i+4,2))+128) _ ' time
       + flnm$ + a$                                    ' filename
   print #2,x$
   if (n mod 25)=0 then locate ,10 : print n;
  case "(U)," : u=u+1
  case else : o=o+1
 end select
wend
close
print
print u;"uploads."
print n;"downloads."
print o;"unknown."

print : print "Sorting ..."
shell "sortf dl.new dltxt.new /+1,15"

open "dltxt.new" for input as #1
open "dl.new" for output as #2
locate 20 : print : print "Copying ..."
n=0 : b$=""
while not eof(1)
 line input #1,a$
 if a$<>b$ then b$=a$ : print #2,mid$(a$,16) : n=n+1
wend
close
print
print n;"unique records."
end

