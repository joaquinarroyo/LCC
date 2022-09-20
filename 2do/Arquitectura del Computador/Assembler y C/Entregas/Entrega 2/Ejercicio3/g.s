.data
a: .long 0
b: .long 1

.text
.global main
main:
    movl b, %eax
    subl a, %eax
    ret