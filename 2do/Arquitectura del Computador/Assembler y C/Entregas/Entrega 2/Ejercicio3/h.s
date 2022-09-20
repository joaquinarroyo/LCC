.data
a: .long 0x80000000
b: .long 0

.text
.global main
main:
    movl b, %eax
    subl %eax, a
    addl a, %eax
    ret