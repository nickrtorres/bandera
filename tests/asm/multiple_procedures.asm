.code
foo proc
  mov ax, 42
  ret
foo endp

bar proc
  mov ax, 100
  ret
bar endp

main:
  call foo
  mov bx, ax
  call bar

end main
; Expect: ax := 100
;         bx := 42
