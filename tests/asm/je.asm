main:
  mov ax, 0
AnotherAdd:
  add ax, 42
  cmp ax, 42
  je AnotherAdd
end main

; Expect: ax := 84
