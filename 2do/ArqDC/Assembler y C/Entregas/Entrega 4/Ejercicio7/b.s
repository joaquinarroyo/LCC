.data
format1: .asciz "Cantidad de bits en 1: %ld\n"
format2: .asciz "Valor de rax(hexadecimal): %lx\n"
cantidadDeBits: .byte

.text
.global main
main:
    xorq %r8, %r8       # cantidad de bits en 1
    xorq %rsi, %rsi     # contador de rotaciones hacia izquierda

rotar:
    cmpq $64, %rsi
    je terminar
    inc %rsi
    rol $1, %rax
    jc bit_en_1
    jmp rotar

bit_en_1:
    inc %r8
    jmp rotar

terminar:
    movq %r8, cantidadDeBits  # se guarda la cantidad de bits en 1
    push %rbx
    movq $format2, %rdi  
    movq %rax, %rsi           # valor original de rax
    xorq %rax, %rax          
    call printf
    movq $format1, %rdi  
    movq cantidadDeBits, %rsi # cantidad de bits en 1
    xorq %rax, %rax          
    call printf
    pop %rbx

    ret
