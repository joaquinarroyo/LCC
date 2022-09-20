.data
s: .asciz "%d\n"
i: .long 89

.text
.global main
main:
    push %rbx        
    movq $format, %rdi     # formato de impresion
    movq i, %rsi           # valor a imprimir 
    movw $0, %ax        
    call printf
    pop %rbx
    ret

