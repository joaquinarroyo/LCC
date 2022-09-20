.data
x: .string "%d\n"

.text

.global main
main:
    pushq $8
    pushq $0
    popq %rax
    popq %rax
    ret