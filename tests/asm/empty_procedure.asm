.code
foo proc
  ret
foo endp

bar:
  mov ax, 42

end bar

; Expect: ax := 42
