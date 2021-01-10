; Loads a 16 bit integer into ax and bx 8 bits at a time.
.code
main:
  mov ah, 171 ; 0xAB
  mov al, 205 ; 0xCD
  mov bh, 18  ; 0x12
  mov bl, 52  ; 0x34

end main
