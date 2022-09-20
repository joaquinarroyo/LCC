.data
fmt: .string "%d" 
entero: .long
n: .long 19

funcs:  .quad f1
        .quad f2
        .quad f3

.text
f1: movl $0, %esi
    movq $fmt, %rdi
    call printf
    jmp fin
f2: movl $1, %esi
    movq $fmt, %rdi
    call printf
    jmp fin
f3: movl $2, %esi
    movq $fmt, %rdi
    call printf
    jmp fin

.global main
main:
    pushq %rbp
    movq %rsp, %rbp
    movq $fmt, %rdi
    movq $entero, %rsi
    xorq %rax, %rax
    call scanf
    xorq %rax, %rax
    movq $funcs, %rbx
    leaq (%rbx, %rsi, 8), %rdx
    
    jmp *%rdx

fin:
    movq %rbp, %rsp
    popq %rbp
    ret