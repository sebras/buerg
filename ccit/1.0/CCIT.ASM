	page	74,132
	title	CRC16  Calculate CRC-16 for data block

;   The logic for this method of calculating the CRC 16 bit polynomial
;   is taken from an article by David Schwaderer in the April 1985
;   issue of PC Tech Journal.

; usage:
;	Call CCIT (X$, HICRC%, LOCRC%)
;
; note: For the CCIT routine, do NOT add a word of zeros to the end of the string.
;	For the CRC-16 routine, append a word of zeros to the data block.
;	Supply '/dcrc16' to create a routine for the CRC-16 polynomial.
;
; author:
;	Vern Buerg, Sep 86, for BBSWES

COMPUTE_CRC	macro	character_reg
	xor	character_reg, dl	; CRC^c & 0x00FF
	mov	bl, character_reg	; move into index register
	xor	bh, bh			; make a full word
	shl	bx, 1			; word index

	mov	dl, dh			; CRC >> 8
	xor	dh, dh			; (CRC >> 8) & 0x00ff

	xor	dx, cs:[di][bx] 	; (CRC>>8) & 0x00ff) ^ crctab[(CRC^c)&0x00ff]
	endm


cseg	segment public para 'codesg'
	assume	cs:cseg

	public	ccit

ccit	proc	far
	push	bp			; save bascom reg
	mov	bp,sp			; get parmlist ptr
	mov	si,word ptr 10[bp]	; get X$ vector
	mov	cx,word ptr [si]	; - string length
	mov	si,word ptr 2[si]	; - string offset

	mov	di,offset cs:crctab	; point to the CRC table
	sub	dx,dx			; initialize crc result

	shr	cx, 1			; even or odd?
	jnc	even_number_of_bytes	; branch if even
					; else take care of the odd byte first
	lodsb				; get next byte

	COMPUTE_CRC	al


	jcxz	Finished_CRC		; branch if no more

even_number_of_bytes:			; walk through the data block
	lodsw				;  2 bytes at a time

	COMPUTE_CRC	al

	COMPUTE_CRC	ah

	loop	Even_number_of_bytes

Finished_CRC:
	sub	ax,ax			; DX has crc value

	mov	di,word ptr 8[bp]	; offset to HICRC
	mov	al,dl
	stosw				; return hi crc byte
	mov	di,word ptr 6[bp]	; offset to LOCRC
	mov	al,dh
	stosw				; return low crc byte

	pop	bp			; recover bascom reg
	ret	6			; clear stack and return

	page

	even
crctab	label	word
	ifndef	crc16
; crc-ccit table = x^16 + x^12 + x^5 + 1
	dw 00000h, 02110h, 04220h, 06330h, 08440h, 0A550h, 0C660h, 0E770h
	dw 00881h, 02991h, 04AA1h, 06BB1h, 08CC1h, 0ADD1h, 0CEE1h, 0EFF1h
	dw 03112h, 01002h, 07332h, 05222h, 0B552h, 09442h, 0F772h, 0D662h
	dw 03993h, 01883h, 07BB3h, 05AA3h, 0BDD3h, 09CC3h, 0FFF3h, 0DEE3h
	dw 06224h, 04334h, 02004h, 00114h, 0E664h, 0C774h, 0A444h, 08554h
	dw 06AA5h, 04BB5h, 02885h, 00995h, 0EEE5h, 0CFF5h, 0ACC5h, 08DD5h
	dw 05336h, 07226h, 01116h, 03006h, 0D776h, 0F666h, 09556h, 0B446h
	dw 05BB7h, 07AA7h, 01997h, 03887h, 0DFF7h, 0FEE7h, 09DD7h, 0BCC7h

	dw 0C448h, 0E558h, 08668h, 0A778h, 04008h, 06118h, 00228h, 02338h
	dw 0CCC9h, 0EDD9h, 08EE9h, 0AFF9h, 04889h, 06999h, 00AA9h, 02BB9h
	dw 0F55Ah, 0D44Ah, 0B77Ah, 0966Ah, 0711Ah, 0500Ah, 0333Ah, 0122Ah
	dw 0FDDBh, 0DCCBh, 0BFFBh, 09EEBh, 0799Bh, 0588Bh, 03BBBh, 01AABh
	dw 0A66Ch, 0877Ch, 0E44Ch, 0C55Ch, 0222Ch, 0033Ch, 0600Ch, 0411Ch
	dw 0AEEDh, 08FFDh, 0ECCDh, 0CDDDh, 02AADh, 00BBDh, 0688Dh, 0499Dh
	dw 0977Eh, 0B66Eh, 0D55Eh, 0F44Eh, 0133Eh, 0322Eh, 0511Eh, 0700Eh
	dw 09FFFh, 0BEEFh, 0DDDFh, 0FCCFh, 01BBFh, 03AAFh, 0599Fh, 0788Fh

	dw 08891h, 0A981h, 0CAB1h, 0EBA1h, 00CD1h, 02DC1h, 04EF1h, 06FE1h
	dw 08010h, 0A100h, 0C230h, 0E320h, 00450h, 02540h, 04670h, 06760h
	dw 0B983h, 09893h, 0FBA3h, 0DAB3h, 03DC3h, 01CD3h, 07FE3h, 05EF3h
	dw 0B102h, 09012h, 0F322h, 0D232h, 03542h, 01452h, 07762h, 05672h
	dw 0EAB5h, 0CBA5h, 0A895h, 08985h, 06EF5h, 04FE5h, 02CD5h, 00DC5h
	dw 0E234h, 0C324h, 0A014h, 08104h, 06674h, 04764h, 02454h, 00544h
	dw 0DBA7h, 0FAB7h, 09987h, 0B897h, 05FE7h, 07EF7h, 01DC7h, 03CD7h
	dw 0D326h, 0F236h, 09106h, 0B016h, 05766h, 07676h, 01546h, 03456h

	dw 04CD9h, 06DC9h, 00EF9h, 02FE9h, 0C899h, 0E989h, 08AB9h, 0ABA9h
	dw 04458h, 06548h, 00678h, 02768h, 0C018h, 0E108h, 08238h, 0A328h
	dw 07DCBh, 05CDBh, 03FEBh, 01EFBh, 0F98Bh, 0D89Bh, 0BBABh, 09ABBh
	dw 0754Ah, 0545Ah, 0376Ah, 0167Ah, 0F10Ah, 0D01Ah, 0B32Ah, 0923Ah
	dw 02EFDh, 00FEDh, 06CDDh, 04DCDh, 0AABDh, 08BADh, 0E89Dh, 0C98Dh
	dw 0267Ch, 0076Ch, 0645Ch, 0454Ch, 0A23Ch, 0832Ch, 0E01Ch, 0C10Ch
	dw 01FEFh, 03EFFh, 05DCFh, 07CDFh, 09BAFh, 0BABFh, 0D98Fh, 0F89Fh
	dw 0176Eh, 0367Eh, 0554Eh, 0745Eh, 0932Eh, 0B23Eh, 0D10Eh, 0F01Eh

	else
; crc-16 table = x^16 + x^15 + x^2 +1
	dw 00000H, 0C0C1H, 0C181H, 00140H, 0C301H, 003C0H, 00280H, 0C241H
	dw 0C601H, 006C0H, 00780H, 0C741H, 00500H, 0C5C1H, 0C481H, 00440H
	dw 0CC01H, 00CC0H, 00D80H, 0CD41H, 00F00H, 0CFC1H, 0CE81H, 00E40H
	dw 00A00H, 0CAC1H, 0CB81H, 00B40H, 0C901H, 009C0H, 00880H, 0C841H
	dw 0D801H, 018C0H, 01980H, 0D941H, 01B00H, 0DBC1H, 0DA81H, 01A40H
	dw 01E00H, 0DEC1H, 0DF81H, 01F40H, 0DD01H, 01DC0H, 01C80H, 0DC41H
	dw 01400H, 0D4C1H, 0D581H, 01540H, 0D701H, 017C0H, 01680H, 0D641H
	dw 0D201H, 012C0H, 01380H, 0D341H, 01100H, 0D1C1H, 0D081H, 01040H
	dw 0F001H, 030C0H, 03180H, 0F141H, 03300H, 0F3C1H, 0F281H, 03240H
	dw 03600H, 0F6C1H, 0F781H, 03740H, 0F501H, 035C0H, 03480H, 0F441H
	dw 03C00H, 0FCC1H, 0FD81H, 03D40H, 0FF01H, 03FC0H, 03E80H, 0FE41H
	dw 0FA01H, 03AC0H, 03B80H, 0FB41H, 03900H, 0F9C1H, 0F881H, 03840H
	dw 02800H, 0E8C1H, 0E981H, 02940H, 0EB01H, 02BC0H, 02A80H, 0EA41H
	dw 0EE01H, 02EC0H, 02F80H, 0EF41H, 02D00H, 0EDC1H, 0EC81H, 02C40H
	dw 0E401H, 024C0H, 02580H, 0E541H, 02700H, 0E7C1H, 0E681H, 02640H
	dw 02200H, 0E2C1H, 0E381H, 02340H, 0E101H, 021C0H, 02080H, 0E041H
	dw 0A001H, 060C0H, 06180H, 0A141H, 06300H, 0A3C1H, 0A281H, 06240H
	dw 06600H, 0A6C1H, 0A781H, 06740H, 0A501H, 065C0H, 06480H, 0A441H
	dw 06C00H, 0ACC1H, 0AD81H, 06D40H, 0AF01H, 06FC0H, 06E80H, 0AE41H
	dw 0AA01H, 06AC0H, 06B80H, 0AB41H, 06900H, 0A9C1H, 0A881H, 06840H
	dw 07800H, 0B8C1H, 0B981H, 07940H, 0BB01H, 07BC0H, 07A80H, 0BA41H
	dw 0BE01H, 07EC0H, 07F80H, 0BF41H, 07D00H, 0BDC1H, 0BC81H, 07C40H
	dw 0B401H, 074C0H, 07580H, 0B541H, 07700H, 0B7C1H, 0B681H, 07640H
	dw 07200H, 0B2C1H, 0B381H, 07340H, 0B101H, 071C0H, 07080H, 0B041H
	dw 05000H, 090C1H, 09181H, 05140H, 09301H, 053C0H, 05280H, 09241H
	dw 09601H, 056C0H, 05780H, 09741H, 05500H, 095C1H, 09481H, 05440H
	dw 09C01H, 05CC0H, 05D80H, 09D41H, 05F00H, 09FC1H, 09E81H, 05E40H
	dw 05A00H, 09AC1H, 09B81H, 05B40H, 09901H, 059C0H, 05880H, 09841H
	dw 08801H, 048C0H, 04980H, 08941H, 04B00H, 08BC1H, 08A81H, 04A40H
	dw 04E00H, 08EC1H, 08F81H, 04F40H, 08D01H, 04DC0H, 04C80H, 08C41H
	dw 04400H, 084C1H, 08581H, 04540H, 08701H, 047C0H, 04680H, 08641H
	dw 08201H, 042C0H, 04380H, 08341H, 04100H, 081C1H, 08081H, 04040H
	endif

ccit	endp
cseg	ends
	end
