.DATA
AB DB ABh
CD DB CDh

.CODE
main:
  mov al, AB
  mov ah, CD

END main

; Expect ax: 42
