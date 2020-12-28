foo proc
  mov ax, 42
  ret
foo endp

main:
  call foo
  add ax, 100
end main

; Expect: ax := 142
