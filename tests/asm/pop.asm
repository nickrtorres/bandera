main:
  mov ax, 0
  mov bx, 0

  mov ax, 42
  push ax

  add ax, 100

  pop bx

end main

; Expect: ax := 142
;         bx := 42
