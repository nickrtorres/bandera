  mov ax, 0
Loop:
  add ax, 1
  cmp ax, 10
  jne Loop

; Expect: ax := 10
