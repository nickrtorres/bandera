; Writes "Hello, world!\n" to stdout

.code
WriteChar proc
  push bp
  mov bp, sp
  mov dl, word ptr [bp + 4] ; FIXME should be byte ptr; not word ptr
  mov ah, 02h
  int 21h
  pop bp
  ret 2
WriteChar endp

main:
  mov ax, 72  ; 'H'
  push ax
  call WriteChar

  mov ax, 101 ; 'e'
  push ax
  call WriteChar

  mov ax, 108 ; 'l'
  push ax
  call WriteChar

  mov ax, 108 ; 'l'
  push ax
  call WriteChar

  mov ax, 111 ; 'o'
  push ax
  call WriteChar

  mov ax, 44  ; ','
  push ax
  call WriteChar

  mov ax, 32  ; ' '
  push ax
  call WriteChar

  mov ax, 119 ; 'w'
  push ax
  call WriteChar

  mov ax, 111 ; 'o'
  push ax
  call WriteChar

  mov ax, 114 ; 'r'
  push ax
  call WriteChar

  mov ax, 108 ; 'l'
  push ax
  call WriteChar

  mov ax, 100 ; 'd'
  push ax
  call WriteChar

  mov ax, 33  ; '!'
  push ax
  call WriteChar

  mov ax, 10  ; '\n'
  push ax
  call WriteChar

end main
