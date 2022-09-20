.data
a:  .float 2
b:  .float 3
c:  .float 4
d:  .float 5
e:  .float 6
f:  .float 7
x:  .float 
y:  .float

cero: .float 0.0

.text
.global main
main:
    movss a, %xmm0  # argumentos
    movss b, %xmm1
    movss c, %xmm2
    movss d, %xmm3
    movss e, %xmm4
    movss f, %xmm5
    movq $x, %rdi
    movq $y, %rsi 
calcular:
    movss %xmm3, %xmm6  # xmm6 = d
    movss %xmm4, %xmm7  # xmm7 = e
    mulss %xmm0, %xmm4  # xmm4 = a * e
    mulss %xmm1, %xmm3  # xmm3 = b * d
    subss %xmm4, %xmm3  # determinante = a * e - b * d
    comiss cero, %xmm3
    je sin_solucion
    movss %xmm4, %xmm3  # xmm3 = f
    mulss %xmm2, %xmm7  # xmm7 = c * e
    mulss %xmm1, %xmm5  # xmm5 = b * f
    subss %xmm7, %xmm5  # xmm5 = c * e - b * f
    movq %xmm5, %rdi   # x = xmm5
    mulss %xmm1, %xmm3  # xmm3 = a * f
    mulss %xmm2, %xmm6  # xmm6 = c * d
    subss %xmm5, %xmm6  # xmm6 = a * f - c * d
    movq %xmm6, %rsi   # y = xmm6
    movq $0, %rax
    jmp terminar
sin_solucion:
    movq $-1, %rax
    jmp terminar
terminar:
    ret