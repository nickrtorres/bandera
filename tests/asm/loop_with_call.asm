.code
increment proc
  add ax, 1
  ret
increment endp

main:
  call increment
  cmp ax, 32000
  jne main

end main
