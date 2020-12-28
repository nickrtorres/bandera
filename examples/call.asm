foo proc
  mov ax, 42
  ret
foo endp

main:
  call foo
end main

; Expect: ax := 42
