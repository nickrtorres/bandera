foo proc
  push bp
  mov bp, sp
  mov bx, word ptr [bp + 4]
  pop bp
  ret 2
foo endp

main:
  mov ax, 42
  push ax
  call foo

end main

; Expect: ax := 42
;         bx := 42
