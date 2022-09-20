.global main
main:
    movl $-1, %eax
    movl $2, %ecx
    imull %ecx
    movl %edx, %esi
    shl $32, %rsi
    or %rsi, %rax

    xorq %rsi, %rsi
    xorq %rax, %rax
    movw $-1, %ax
    movw $2, %cx
    mulw %cx    
    decl %edx
    or %edx, %eax
    ret