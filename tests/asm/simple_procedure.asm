foo proc
  mov ax, 100
  ret
foo endp

bar:
  add ax, 42

end bar

; Expect: ax := 42
