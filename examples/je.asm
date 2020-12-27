  mov ax, 0
AnotherAdd:
  add ax, 42
  cmp ax, 42
  je AnotherAdd

; Expect: ax := 84
