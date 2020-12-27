  mov ax, 0
AnotherAdd:
  add ax, 42
  cmp ax, 84
  jne AnotherAdd

; Expect: ax := 84
