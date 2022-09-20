.data
format1: .asciz "Valor de rax(hexadecimal): %lx\n"
format2: .asciz "Valor de rax permutado(hexadecimal): %lx\n"
valorPerm: .quad 0

.text
.global main
main:
    movq %rax, %r8  # r8 va a guardar el valor original de rax
    rol $32, %rax
    movq %rax, valorPerm    

    push %rbx   
    movq $format1, %rdi  
    movq %r8, %rsi  
    xorq %rax, %rax          
    call printf
    movq $format2, %rdi  
    movq valorPerm, %rsi
    xorq %rax, %rax          
    call printf
    pop %rbx

    ret        
