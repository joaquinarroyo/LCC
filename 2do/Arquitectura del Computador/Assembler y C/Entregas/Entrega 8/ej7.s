.data
a:  .float 1.0 
    .float 2.0 
    .float 5.0

b:  .float 4.0
    .float 2.0
    .float 3.0

len: .quad 3

.text

.global main
main:
    movq $a, %rdi   # argumento 1
    movq $b, %rsi   # argumento 2
    movq len, %rdx  # argumento 3
    xorq %r8, %r8   # index
    xorq %rcx, %rcx # contador
    cmpq $0, %rdx
    je terminar

sumar:
    movss (%rdi, %r8), %xmm0
    movss (%rsi, %r8), %xmm1
    addss %xmm1, %xmm0
    movss %xmm0, (%rdi, %r8)
    addq $1, %rcx
    cmpq %rcx, %rdx
    je terminar
    addq $1, %r8
    jmp sumar

terminar:
    ret

