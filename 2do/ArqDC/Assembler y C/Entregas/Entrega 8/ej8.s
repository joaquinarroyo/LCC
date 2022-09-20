.data
.byte 10

.align 16
a: .float 1.0,2.0,3.0,4.0,5.0

.align 16
b: .float 1.0,3.0,2.0,3.2,4.0

len: .quad 5

.text
.global main
main:
    movq $a, %rdi
    movq $b, %rsi
    movq len, %rdx
    movq $0, %r8    # index
    movq $0, %r9    # contador
    cmpq $4, %rdx
    jl caso1

multiplo4:
    incq %r9
    imul $4, %r9, %rcx   # rcx = 4 * r9 
    cmpq %rdx, %rcx
    jl multiplo4
    movq $4, %rax
    subq %rax, %rcx
    movq %r9, %rax
    dec %rax
    xorq %r9, %r9
    cmpq %rdx, %rcx
    jl caso2
    jmp caso3

caso1:
    movss (%rdi, %r8), %xmm0
    movss (%rsi, %r8), %xmm1
    addss %xmm0, %xmm1
    movss %xmm1, (%rdi, %r8)
    addq $4, %r8
    incq %r9
    cmpq len, %r9
    je terminar
    jmp caso1

caso2:
    movaps (%rdi, %r8), %xmm0
    movaps (%rsi, %r8), %xmm1
    addps %xmm0, %xmm1
    movss %xmm1, (%rdi, %r8)
    inc %r9
    addq $16, %r8
    movq len, %rdx
    subq %rcx, %rdx
    cmpq %r9, %rax
    je sumar_restantes1
    jmp caso2

sumar_restantes1:
    xorq %r9, %r9
    movq len, %rax
    subq %rcx, %rax

sumar_restantes2:
    movss (%rdi, %r8), %xmm0
    movss (%rsi, %r8), %xmm1
    addss %xmm0, %xmm1
    movss %xmm1, (%rdi, %r8)
    incq %r9
    addq $4, %r8
    cmpq %rax, %r9
    je terminar
    jmp sumar_restantes2

caso3:
    movaps (%rdi, %r8), %xmm0
    movaps (%rsi, %r8), %xmm1
    addps %xmm0, %xmm1
    movaps %xmm1, (%rdi, %r8)
    inc %r9
    addq $16, %r8
    cmpq %r9, %rax
    je terminar
    jmp caso3
    
terminar:
    xorq %rax, %rax
    ret