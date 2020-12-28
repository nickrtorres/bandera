foo proc
  mov ax, 100
foo endp

bar:
  add ax, 42

end bar

; Expect: ax := 42
