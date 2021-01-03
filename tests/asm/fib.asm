; A pretty straight forward implementation of the following C function in ASM.
;
; int fib(int n) {
;     if (n < 2) return n;
;
;     return fib(n-1) + fib(n-2);
; }
fib proc
  push    bp
  mov     bp, sp
  mov     ax, word ptr [bp + 4]
  cmp     ax, 2
  jge     RecursiveStep
  jmp     Cleanup
RecursiveStep:
  push    bx
  sub     ax, 1
  push    ax
  call    fib
  mov     bx, ax
  mov     ax, word ptr [bp + 4]
  sub     ax, 2
  push    ax
  call    fib
  add     ax, bx
  pop     bx
Cleanup:
  pop     bp
  ret     2
fib endp

main:
  mov ax, 24
  push ax
  call fib
  mov bx, 0

end main

; Expect: ax := 46368
;         bx := 0
