.data
cadena: .asciz "123456"
caracter: .asciz "2"

.text
.global main
main:
    movq $cadena, %rdi
    movb caracter, %al
    movb $0, %r8b       # contador de iteraciones

.global busca
busca:
    inc %r8b
    scasb
    je encontro
    cmpb $6, %r8b
    je no_encontro
    jmp busca
encontro:
    movq (%rdi), %rax
    jmp terminar
no_encontro:
    movq $-1, %rax
terminar:
    ret