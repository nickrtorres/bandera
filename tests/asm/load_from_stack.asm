foo proc
  mov bx, word ptr [bp + 2]
  ret 2
foo endp

main:
  mov ax, 42
  push ax
  call foo

end main

; Expect: ax := 42
;         bx := 42
