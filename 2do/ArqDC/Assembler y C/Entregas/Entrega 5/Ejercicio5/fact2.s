.data
n: .quad 5     # factorial a calcular

.text
.global main
main:
    cmpq $1, n
    je terminar1
    movq n, %r8         # r8 = n
    movq %r8, %rbx
fact:
    decq %rbx           # rbx = n-1
    imulq %rbx, %r8     # n . n-1 guardado en %r8
    cmpq $1, %rbx
    je terminar2
    jmp fact
terminar1:
    movq n, %rax
    jmp fin
terminar2:
    movq %r8, %rax  
fin:
    ret

