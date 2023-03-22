' $Title:'AUTOSIG - Browse DL catalog offline' $Pagesize:74 $Linesize:132

' Name:
'       BROWSEDL, version 1, 12/24/87
'
' Function:
'       Create an ATO script file to download files selected
'       from a forum DL catalog file listing.
'
' Syntax:
'       BRO [forum.dl]
'
'       where "forum" is the exact forum name, 1 to 7 characters
'             "dl" is a number from 0 to 17
'       if omitted, the user is prompted for the forum name, etc.
'
' Input:
'       The DL catalog file is created by capturing the output of
'       a CAT /DES command while online.
'
' Output:
'       A file called "DL.SCR" is created if any entries are M)arked.
'       The user may then invoke ATO with the following:
'               ATO /XDL
'       to automatically log on and download those files.
'
' Compile:
'       QB BRO/E;
'       LINK BRO+ATOWEB;


        Defint A-Z
        Dim ITEMS$(500,7)               ' Files available in a forum/DL
         Const ITEM.MARK=0
         Const ITEM.PPN=1
         Const ITEM.FILE=2
         Const ITEM.DATE=3
         Const ITEM.SIZE=4
         Const ITEM.COUNT=5
         Const ITEM.KEYS=6
         Const ITEM.DESCR=7

        Dim INFO$(3)                    ' File name, forum name, DL number
         Const INFO.FILE=1
         Const INFO.FORUM=2
         Const INFO.DL=3

        Const VERSION$="5.53"

        Const ROW.FILE=6, ROW.FORUM=7, ROW.DL=8
        Const ROW.ITEM=6

100     On Error Goto Browse.Errors
        Key Off

        Def SEG=0 : MONO=(Peek(&H410) And &H30)=48 : Def SEG
        If MONO _
          Then ZF1=7 : ZB1=0 : ZF3=0 : ZB3=7 : ZA.HI=112 : ZA1=7 _
          Else ZF1=7 : ZB1=1 : ZF3=14 : ZB3=1 : ZA.HI=113 : ZA1=23

        Gosub Color1                    ' Usual colors

200     T$=Command$                     ' Stuff on command line?
        If T$<>"" Then                  ' Must be "forum.dl"
          I=Instr(T$,".")               ' Any ext?
          If I Then
            INFO$(INFO.FILE)=T$
            INFO$(INFO.FORUM)=Left$(T$,I-1)
            INFO$(INFO.DL)=Mid$(Str$(Val(Mid$(T$,I+1))),2)
          End If
        End If


Browse.Init:
900     Cls: Restore Browse.Panel1      ' Display main menu
        For R=1 To 10
         Read T$
         Locate R,1
         Print T$;
        Next

Browse.Menu:
1000    For I=1 To Ubound(INFO$)        ' Clear input fields
         INFO$(I)=Left$(INFO$(I)+Space$(20),20)
        Next

        WERS=6 : WERE=8 : WECS=31 : WECE=50
        Call ATOwe (WERS,WERE,WECS,WECE,ZA.HI,WECH,INFO$())
        If WERS<1 Then End              ' PgDn to panic exit

Browse.Check:
1100    For J=1 To 3                    ' Delete trailing blanks
         For I=Len(INFO$(J)) To 1 Step -1
          If Mid$(INFO$(J),I,1)<>" " Then
            INFO$(J)=Left$(INFO$(J),I)
            Exit For
          End If
         Next I
        Next J

        Locate ROW.FORUM,52             ' Check forum name
        If Len(INFO$(2))>7 Then
          Print "<= Invalid forum name"
          Gosub Beeper
          Goto Browse.Menu
        End If
        Print Space$(26);               ' Clear error message field

        Locate ROW.DL,52
        If Val(INFO$(3))=0 And INFO$(3)<>"0" Then
          Print "<= Invalid DL number"
          Gosub Beeper
          Goto Browse.Menu
        End If
        Print Space$(26);

Browse.Open:
1200    Open INFO$(1) For Input As #1

        Locate ROW.DL+4,27
         Gosub Color3
         Print "Loading ";INFO$(1);" ...";
         Gosub Color1

Browse.Load:
1300    While NOT Eof(1)
         Line Input #1,T$
         If Left$(T$,2)="[7" And Instr(T$,"]") Then
          Browse.Pick:
           NUMFILE=NUMFILE+1
           ITEMS$(NUMFILE,ITEM.PPN)=T$                  ' Uploader ppn
1310       Line Input #1,T$
           ITEMS$(NUMFILE,ITEM.FILE)=Mid$(T$,1,19)      ' File name
           ITEMS$(NUMFILE,ITEM.DATE)=Mid$(T$,27,9)      ' Upload date
           ITEMS$(NUMFILE,ITEM.SIZE)=Mid$(T$,37,7)      ' File size
           ITEMS$(NUMFILE,ITEM.COUNT)=Mid$(T$,56)       ' dl count
1320       Line Input #1,T$
            If T$="" Then Line Input #1,T$
           ITEMS$(NUMFILE,ITEM.KEYS)=T$                 ' Keywords
1330       Line Input #1,T$
            If T$="" Then Line Input #1,T$
           While T$ <> ""
            ITEMS$(NUMFILE,ITEM.DESCR)=ITEMS$(NUMFILE,ITEM.DESCR)+T$+" þ"
1340        Line Input #1,T$
            If Left$(T$,2)="[7" Then Goto Browse.Pick
           Wend
         End If
        Wend

' $Page $Subtitle:'--- Display file descriptions'

Browse.Show:
1400    Close #1

        J=1                                     ' Display each file
Browse.Next:
1500     Restore Browse.Panel1 : Cls             ' Clear display
         For R=1 To 5
          Read T$
          Locate R,1
          Print T$;
         Next

        If J<1 Then J=1                         ' Check position
        If J>NUMFILE Then J=NUMFILE

         Locate ROW.ITEM,1              ' Show file stuff
          Print ITEMS$(J,ITEM.PPN)
          Print ITEMS$(J,ITEM.FILE);Tab(27);ITEMS$(J,ITEM.DATE);
           Print Tab(37);ITEMS$(J,ITEM.SIZE);Tab(56);ITEMS$(J,ITEM.COUNT)
           Print

          A$=ITEMS$(J,ITEM.KEYS)        ' Show keywords
          Gosub Browse.Found

          T$=ITEMS$(J,ITEM.DESCR)       ' Show description lines
          While T$<>""
           I=Instr(T$,"þ")              ' end of line marker
           A$=Left$(T$,I-1)             ' next line of descr
           Gosub Browse.Found
           T$=Mid$(T$,I+1)
          Wend
          Goto Browse.Prompt

Browse.Found:
1600    F=Instr(A$,F$)               ' location of found text
        If F$="" Or F=0 Then
          Print A$                   ' normal display
         Else
          Print Left$(A$,F-1);       ' highlight found text
          Gosub Color3
          Print Mid$(A$,F,Len(F$));
          Gosub Color1
          Print Mid$(A$,F+Len(F$))
        End If
        Return

' $Page

Browse.Prompt:
1610     Locate 23,1,0                          ' Get action response
          Print "U)p D)own M)ark O)mit Q)uit F)ind A)gain. Enter for next. Action?";
          A$="" : Locate ,,1
          While A$=""
           A$=Inkey$
          Wend

Browse.Action:
1700      If Len(A$)=1 Then                     ' See if letter or cursor key
            If A$=Chr$(13) Then A$="D"  ' Enter
            If A$=Chr$(27) Then A$="Q"  ' ESCape
            If A$>"Z" Then A$=Chr$(Asc(A$)-32)
           Else
            K=Asc(Right$(A$,1))

            Select Case K
             Case 72,73 : A$="U"                   ' Up
             Case 80,81 : A$="D"                   ' Down
             Case 71 :    A$="T"                   ' Home, top
             Case 79 :    A$="B"                   ' End, bottom
             Case Else :  A$="?"                   ' Unknown
            End Select
          End If

            Select Case A$                         ' What to do
             Case "Q" : Goto Browse.Select              ' Q)uit
             Case "U" : J=J-1                           ' U)p
                        If J<1 Then J=1 : Gosub Beeper
                        Goto Browse.Next

             Case "D" : J=J+1                           ' D)own
                        If J>NUMFILE Then Gosub Beeper : J=NUMFILE
                        Goto Browse.Next

             Case "M" : ITEMS$(J,ITEM.MARK)="M"         ' M)ark for downloading
                        MARKED=MARKED+1

             Case "O" :                                 ' O)mit from downloading
                        If ITEMS$(J,ITEM.MARK)="M" Then
                         ITEMS$(J,ITEM.MARK)="O"
                         MARKED=MARKED-1
                        End If

             Case "T" : J=1                             ' T)op
                        Goto Browse.Next
             Case "B" : J=NUMFILE                       ' B)ottom
                        Goto Browse.Next

             Case "A" :                                 ' A)gain next occurance
                        If F$<>"" Then J=J+1 : Goto Browse.Find
                        Gosub Beeper

             Case "F" :                                 ' F)ind
                        Locate 23,1 : Print Space$(79);
                        Locate 23,1 : Print "Find what? ";
                        Line Input F$

                        If F$<>"" Then
                         U$=F$                          ' Upper case for keys
                         For L=1 To Len(U$)
                          If Mid$(U$,L,1)>"Z" Then Mid$(U$,L,1)=Chr$(Asc(Mid$(U$,L,1))-32)
                         Next

                Browse.Find:
                         For K=J To NUMFILE             ' Search keys and descr
                          If Instr(ITEMS$(K,ITEM.DESCR),F$) Or _
                             Instr(ITEMS$(K,ITEM.KEYS),U$) _
                           Then
                            J=K
                            Goto Browse.Next
                          End If
                         Next K
                         Gosub Beeper                   ' Not found
                          'Locate 22,1
                          'Print " Text not found!";
                          Goto Browse.Next
                        End If

             Case Else : Gosub Beeper
            End Select

        J=J+1
        If J>NUMFILE Then J=NUMFILE : Gosub Beeper:  Goto Browse.Prompt
        Goto Browse.Next

' $Page $Subtitle:'--- Common subroutines'

Beeper:                                         ' Make some racket
        Sound 420,.22
        Sound 820,.22
        Return

Color1:                                         ' Normal colors
        ZA=ZA1 : Color ZF1,ZB1 : Return

Color3:                                         ' Bright colors
        ZA=ZA.HI : Color ZF3,ZB3 : Return


' $Page $Subtitle:'--- Errors and exits'

Browse.Errors:
9000    If ERL=1200 Then                        ' Invalid catalog file name
          Locate ROW.FILE,52
          Print "Unable to find that file!";
          Gosub Beeper
          Resume Browse.Menu
        End If

        If ERL>=1300 And ERL<1400 Then Resume Browse.Show

        On Error Goto 0                         ' Display error info

Browse.Select:
        If MARKED Then
            Locate 24,1 : Print "Creating ";
            Gosub Color3 : Print "DL.SCR";
            Gosub Color1 : Print
           Open "DL.SCR" For Append AS #2
           Print #2,"Logon ";INFO$(2)
           Print #2,"Sendline DL";INFO$(3)
           Print #2,"Match !"

         For I=1 To NUMFILE                      ' See if any marked
          If ITEMS$(I,ITEM.MARK)="M" Then
           T$=ITEMS$(I,ITEM.FILE)
           If Instr(T$,"/") Then T$=Left$(T$,Instr(T$,"/"))
           Print #2,"Dow ";T$
          End If
         Next

        Print #2,"Exit Z"
        Close #2

Browse.Done:
        End If

        End

Browse.Panel1:
        Data "                             A U T O S I G"
        Data "                          ออออออออออออออออออออ"
        Data "                          Browse Forum Catalog"
        Data ""
        Data ""
             '....,....1....,....2....,....3....,....4....,....5....,....6....,
        Data "                   File name:"
        Data "                  Forum name:"
        Data "                   DL number:"
        Data ""
        Data "                (Press ESCape when ready, PgDn to abort)"

