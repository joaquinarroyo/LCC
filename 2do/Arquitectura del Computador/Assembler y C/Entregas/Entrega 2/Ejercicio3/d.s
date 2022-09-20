.data
a: .long 0xAA

.text
.global main
main:
    movl a, %eax
    shll $23, a
    orl a, %eax
    ret
