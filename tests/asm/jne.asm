.code
main:
  mov ax, 0
AnotherAdd:
  add ax, 42
  cmp ax, 84
  jne AnotherAdd
end main

; Expect: ax := 84
