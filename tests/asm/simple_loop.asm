main:
  mov ax, 0
Loop:
  add ax, 1
  cmp ax, 10
  jne Loop
end main

; Expect: ax := 10
