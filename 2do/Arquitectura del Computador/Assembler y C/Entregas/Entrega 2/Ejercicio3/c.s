.data
a: .long 4294967040
b: .long -1

.text
.global main
main:
    movl b, %eax
    andl a, %eax
    ret