.data
a: .long 1
b: .long 1

.text
.global main
main:
    shll $31, a
    shll $15, b
    movl a, %r8d
    orl b, %r8d
    ret