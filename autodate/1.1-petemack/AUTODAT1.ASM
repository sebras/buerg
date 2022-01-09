         page    63,132
         title   AUTODATE --- Display and reset Date and Time
;=====================================================================
; Name:     AUTODATE, automatic date routine.
; Function: Set the date and time from user or file input.
; Input:    1) after re-boot, the date and time are read
;              from "AUTODATE.DAT",
;           2) otherwise, DOS functions return current date and time.
; Output:   1) the date and time are set via DOS function calls,
;           2) the date and time are saved in file "AUTODATE.DAT".
; Notes:
;           Written for the IBM PC by Vernon Buerg, October 1983,
;           and is supplied for public domain use.
;
; Rev   11-01-84
;                Revised console routine to remove ansi mode dependency.
;               Changed to buffered input to permit editing. (pete mack).
;=====================================================================
;
;
cseg     segment PARA public 'CODE'
         assume  cs:cseg,ds:cseg,es:cseg
         org     100h
autodate PROC    FAR
         push    ds                      ;save for linkage
         xor     ax,ax                   ;clear for return
         push    ax                      ;put in stack
;
         mov     dx,offset filename      ;file to open
         call    open                    ;open for input/output
;
         call    getdate
;
; If the current date is 01-01-1980, power was turned off
;
         mov     si,offset ipldate       ;date if new boot
         mov     di,offset month         ;the current date
         cmps    ds:byte ptr[si],es:[di]
         jne     print1                  ;no, display date/time
;
         mov     cx,12                   ;length for date record
         lea     bx,month                ;buffer address
         call    read                    ;get a record
;
         mov     cx,10                   ;length for time record
         lea     bx,hour                 ;buffer address
         call    read                    ;get a record
;
         jmp     print2                  ;now prompt
;
print1:
         call    gettime                 ;current time if not read
print2:
         mov     dx,offset pr_date       ;prompt for DATE
         lea     bx,month                ;where to reply
         call    console                 ;read the DATE
;
         call    setdate                 ;set the date
;
         mov     dx,offset pr_time       ;prompt for TIME
         lea     bx,hour                 ;overlay with reply
         call    console                 ;read the TIME
;
         call    settime                 ;set the time
         page
;============================;
; Re-write Date/Time Records ;
;============================;
         mov     byte ptr end_date,13    ;for end of record
         mov     byte ptr end_date[1],10
         mov     byte ptr end_time,13    ;for end of record
         mov     byte ptr end_time[1],10
;
         mov     cx,0                    ;new file offset of zero
         mov     dx,cx
         mov     al,0                    ;to use CX:DX offset
         mov     bx,handle               ;supply file handle
         mov     ah,42h                  ;to move file pointer
         int     21h
         mov     cx,12                   ;length of date record
         lea     bx,month                ;addr of data
         call    write                   ;re-write date record
;
         mov     cx,10                   ;length of time record
         lea     bx,hour                 ;addr of time
         call    write                   ;re-write time data
;
         mov     bx,handle               ;file handle
         call    close                   ;all done
         RET
         page
         subttl  Get current date
;===================;
; GET CURRENT DATE  ;
;===================;
getdate  proc    near
         push    ax
         push    cx
         push    dx
         mov     ah,2Ah ;DOS DATE function
         int     21h    ;issue request
;
         mov     ax,cx ;get year(19xx)
         sub     ax,1900
         aam
         xchg    al,ah
         or      year,ax
         mov     al,dh ;get month
         aam
         xchg    al,ah
         or      month,ax
         mov     al,dl ;get day
         aam
         xchg    al,ah
         or      day,ax
         pop     dx
         pop     cx
         pop     ax
         ret
getdate  endp
         page
         subttl  Display current time
;==================;
; GET CURRENT TIME ;
;==================;
gettime  proc    near
         push    ax
         push    cx
         push    dx
         mov     ah,2ch ;DOS time function
         int     21h    ;issue request
;
         mov     al,ch ;get hours
         aam
         xchg    al,ah
         or      hour,ax
         mov     al,cl ;get minutes
         aam
         xchg    al,ah
         or      minute,ax
         mov     al,dh ;get seconds
         aam
         xchg    al,ah
         or      second,ax
;
         pop     dx
         pop     CX
         pop     ax
         ret
gettime  endp
         page
         subttl  SETTIME - set time from user input
;===========================;
;        SETTIME            ;
;===========================;
settime  proc    near
         push    ax
         push    bx
         push    cx
         push    dx
;
settimer:
         sub     cx,cx                   ;clear AF flag
         mov     ax,word ptr hour        ;get ASCII hours
         aaa                             ;adjust AL to ASCII
         xchg    al,ah                   ;switch to other byte
         aaa                             ;adjust other byte
         aad                             ;convert to binary
         add     ch,al                   ;copy hours
         mov     ax,word ptr minute      ;get ASCII minutes
         aaa                             ;adjust AL to ASCII
         xchg    al,ah                   ;switch to other byte
         aaa                             ;adjust other byte
         aad                             ;convert to binary
         add     cl,al                   ;copy minutes
         mov     ax,word ptr second      ;get ASCII seconds
         aaa                             ;adjust AL to ASCII
         xchg    al,ah                   ;switch to other byte
         aaa                             ;adjust other byte
         aad                             ;convert to binary
         sub     dx,dx                   ;no hundreths
         mov     dh,al
;
         mov     ah,2dh                  ;set time
         int     21h
;
         cmp     al,0                    ;set okay?
         je      timeset                 ;yes, all done
;
timebad:
         mov     ah,9                    ;no, print message
         mov     dx,offset timemsg
         int     21h
         mov     dx,offset pr_time       ;prompt for TIME
         lea     bx,hour                 ;overlay with reply
         call    console                 ;read the TIME
         jmp     settimer                ;try again
;
timeset:
         pop     dx
         pop     cx
         pop     bx
         pop     ax
         ret
settime  endp
         page
         subttl  SETDATE - set DATE from user input
;==========================;
;        SETDATE           ;
;==========================;
setdate  proc    near
         push    ax
         push    bx
         push    cx
         push    dx
;
setdates:
         cmp     byte ptr month[2],'-'  ;proper delimiter?
         jne     datebad                ;no, prompt again
         cmp     byte ptr day[2],'-'
         jne     datebad
;
         sub     dx,dx                  ;clears AF for AAA
         mov     ax,word ptr month      ;get ASCII month
         aaa                            ;adjust AL to ASCII
         xchg    al,ah                  ;switch to other byte
         aaa                            ;adjust other byte
         aad                            ;convert to binary
         add     dh,al                  ;put month in dh,clear AF
         mov     ax,word ptr day        ;get ASCII day
         aaa
         xchg    al,ah
         aaa
         aad
         add     dl,al                  ;put day in DL,clear AF
         mov     ax,word ptr year       ;get ASCII year
         aaa
         xchg    al,ah
         aaa
         aad
         mov     cl,al                  ;put year in CL
         add     cx,1900                ;still this century
;
         mov     ah,2bh                 ;set date function
         int     21h
;
         cmp     al,0                   ;set okay?
         je      dateset                ;yes, all done
datebad:
         mov     ah,9                   ;no, print message
         mov     dx,offset datemsg
         int     21h
;
         mov     dx,offset pr_date       ;prompt for DATE
         lea     bx,month                ;where to reply
         call    console                 ;read the DATE
;
         jmp     setdates                ;and try it again
;
dateset:
         pop     dx
         pop     cx
         pop     bx
         pop     ax
         ret
setdate  endp
         page
         subttl  CONSOLE - Read console input
;=====================================;
;        CONSOLE                      ;
; INPUT:  DX, offset to prompt        ;
;         BX, LEA of reply            ;
; OUTPUT: field at BX has text        ;
; NOTES:  no editing performed        ;
;=====================================;
console  proc    near
         push    ax
         push    cx
         push    dx
;
         mov     ah,9            ;print function
         int     21h             ;prompt for response
cons1:
        lea        dx,ibuf       ;point input buffer
        mov        ah,0ah        ;console string input call
        int        21h
        lea        si,ibuf1      ;point to first character.
cons1a:
        mov        al,[si]       ;get a character
        inc        si
cons2:
         cmp     al,13      ;is it ENTER?
         je      consend    ;yes, all over
         mov     [bx],al    ;copy inputted character
         inc     bx         ;increment target offset
         jmp     cons1a      ;and get next character
;
consend:
        pop        dx
         pop     cx
         pop     ax
         ret
console  endp
         page
         subttl  OPEN - Open file given filename
;===================================;
;        OPEN                       ;
; input:  DX has offset to filename ;
; output: BX has handle             ;
;         field HANDLE has handle   ;
;===================================;
open     proc    near
         push    ax
         push    cx
;
         mov     ax,2            ;for read/write
         mov     ah,3dh          ;open a file
         int     21h
         mov     handle,ax       ;save file handle
;
         jnc     openend
         aam
         xchg    al,ah
         or      opencode,ax
         mov     dx,offset openmsg
         mov     ah,9
         int     21h
;
openend:
         pop     cx
         pop     ax
         ret
open     endp
         page
         subttl  CLOSE - Close file given handle from open
;=======================;
;        CLOSE          ;
; input:  BX has handle ;
;=======================;
close    proc    near
         push    ax
         mov     ah,3eh          ;close a file handle
         int     21h
         pop     ax
         ret
close    endp
         page
         subttl  READ - Read disk record
;================================;
;        READ                    ;
; input:  CX has length          ;
;         BX has addr rec        ;
;         HANDLE has file handle ;
;================================;
read     proc    near
         push    ax
         push    dx
         mov     recaddr,bx      ;save record address
         mov     numbytes,cx     ;length to clear
readclr: mov     bx,0            ;clear to zero
         inc     bx              ;increment to next byte
         loop    readclr         ;for entire record
;
         mov     bx,handle       ;get file handle from open
         mov     dx,recaddr      ;offset to record buffer
         mov     cx,numbytes     ;number of bytes to read
;
         mov     ah,3fh          ;read from a file
         int     21h
;
readend:
         pop     dx
         pop     ax
         ret
read     endp
         page
         subttl  WRITE - Read disk record
;================================;
;        WRITE                   ;
; input:  CX has length          ;
;         BX has addr rec        ;
;         HANDLE has file handle ;
;================================;
write    proc    near
         push    ax
         push    dx
         mov     dx,bx           ;set record address
         mov     bx,handle       ;set file handle
;
         mov     ah,40h          ;write to file
         int     21h
;
writend:
         pop     dx
         pop     ax
         ret
write    endp
         page
         subttl  Constants and work areas
pr_date  db      0dh,0ah
         db      'Current date is: '
month    dw      '00'
         db      '-'
day      dw      '00'
         db      '-19'
year     dw      '00'
end_date dw      2020h
         db      '   Enter new date: '
         db      '$'
pr_time  db      0dh,0ah
         db      'Current time is: '
hour     dw      '00'
         db      ':'
minute   dw      '00'
         db      ':'
second   dw      '00'
end_time dw      0
         db      '     Enter new time: '
         db      '$'
;
ibuf     db      15
         db      0
ibuf1    db      15 dup (0)
;
ipldate  db      '01-01-1980'
datemsg  db      0dh,0ah,'Date invalid',7,'$'
timemsg  db      0dh,0ah,'Time invalid',7,'$'
ten      db      10
;
filename db      'a:autodate.dat',0  ;drive:filename.ext
handle   dw      0                   ;file handle from open
;
openmsg  db      'Open code: '
opencode dw      '00'
         db      '  $'
numbytes dw      0                   ;bytes to read
bytes    dw      0                   ;bytes read
recaddr  dw      0                   ;addr of i/o area
rec      db      80 dup(0)           ;file record area
;
autodate ENDP
cseg     ends
         end     autodate

                                                                                                                                                                                                                       