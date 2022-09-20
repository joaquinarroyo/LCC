.data
format: .asciz "%x\n"
i:  .quad 0xDEADBEEF

.text
.global main
main:
    push %rbx   
    movq $format, %rdi     # formato de impresion
    movq $format, %rsi     1# valor a imprimir       
    xorq %rax, %rax          
    call printf
    pop %rbx
    ret

