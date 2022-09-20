.data
cadenalarga: .asciz "123456"
cadenacorta: .asciz "1234"
longcadenacorta: .long 4

.text
.global main
main:
    movq $cadenalarga, %rdi
    movq $cadenacorta, %rsi
    movl $0, %r8d                      # contador de iteraciones
    movl $0, %eax                      # contador de igualdades
    movl longcadenacorta, %edx         # longitud cadena corta

.global compara
compara:
    inc %r8d
    cmpsb           
    je aumentar
    jmp desigual

aumentar:
    inc %eax
    cmpl %edx, %eax 
    je igual   
    jmp compara

igual:
    movq $1, %rax
    jmp terminar

desigual:
    xorq %rax, %rax

terminar:
    ret
