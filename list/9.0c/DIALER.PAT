n list.com
l
; Change ctrl-D dialer to COM2 at base port address 02F8
e 0152 F8 02
; Change the modem initialization command string (30 bytes long)
e 0157 'ATE0M1X3DT,                   '
w
q
