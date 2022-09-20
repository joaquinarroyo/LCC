.data
a: .long -1
b: .long 1

.text
.global main
main:
    movl a, %eax
    shll $8, b
    notl b
    andl b, %eax
    ret