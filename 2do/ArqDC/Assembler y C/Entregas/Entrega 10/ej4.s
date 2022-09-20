.section .rodata
i:  .word 10
j:  .word 5

.text
.arm
.global main
main:
    LDR r0, =i   // r0 = i
    LDR r1, =j   // r1 = j
    MOV r2, #0   // r2 = res
    CMP r1, #1   // Condicion1, CMP cambia las banderas.

cuerpo_while:
    ANDHS r3, r1, #1        // Si se cumple condicion 1, se ejecutan las sgtes dos instrucciones.
    CMPHS r3, #1            // Condicion 2, CMP cambia las banderas.
    ADDEQ r2, r0            // Si se cumple condicion 2, se ejecutan las sgtes dos instrucciones.
    SUBEQ r1, #1            
    MOVNE r0, r0, LSL #1    // Si no se cumple condicion 2, se ejecutan las sgtes dos instrucciones.
    MOVNE r1, r1, LSR #1
    CMP r1, #1              // Condicion1 de nuevo, CMP cambia las banderas.
    BHS cuerpo_while        // Si se cumple se vuelve al principio del while, si no, termina.
    
terminar:
    ADD r0, r0, r2
    BX lr

    

