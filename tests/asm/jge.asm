.code
main:
  mov ax, 10
loop:
  sub ax, 1
  cmp ax, 5
  jge loop

end main

; Expect: ax := 4

