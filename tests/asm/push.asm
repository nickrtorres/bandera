.code
foo proc
  ret 4 ; 2 args
foo endp

main:
  mov ax, 42
  push ax
  mov ax, 100
  push ax
  call foo
  mov ax, 2
  mov bx, 4

end main

; Expect: ax := 2
;         bx := 4
