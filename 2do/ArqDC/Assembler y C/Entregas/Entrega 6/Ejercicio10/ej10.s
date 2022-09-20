# Idea de setjmp:
# Guardar el estado del programa actual en la pila para que luego se pueda acceder a el.
# Se guarda las direcciones de el contador de programa, la base de la pila (rbp), y el tope de la pila (rsp)
# Parametros de setjmp
# %rdi: direccion de la estructura jmp_buf
# (%rsp): direccion del return

# Idea del longjmp:
# Rescatar el estado del programa que habiamos guardado con setjmp
# Parametros de longjmp
# %rdi: direccion de la estructura jmp_buf

.data
.text
.global main
main:

setjmp2:
    mov (%rsp), %rax     # mueve la direccion de retorno de la pila actual en rax
    mov %rax, (%rdi)     # mueve el contador de programa (pc) de jmp_buf (almacenada en rax) en la direccion de rdi
    mov %rsp, %rax       # mueve la pila a rax
    add $8, %rax         # agrega 8 a rax para que contenga la parte superior de la pila de llamadas
    mov %rax, 8(%rdi)    # mueve el tope de pila (sp) de jmp_buf (almacenado en rax) en la direccion desplazada en 8 de rdi
    mov %rbp, 16(%rdi)   # mueve la base de pila de jmp_buf en la direccion desplazada en 16 de rdi
    mov $0, %rax         # mueve el numero 0 a rax para luego retornar
    ret

longjmp2: 
    mov 8(%rdi), %rsp    # mueve el tope de pila de jmp_buf hacia el tope de pila actual
    mov 16(%rdi), %rbp   # mueve la base de la pila de jmp_buf hacia la base de pila actual
    mov $1, %rax         # mueve el numero 1 en rax para luego retornar
    jmp *(%rdi)          # salta hacia la direccion del contador de programa guardado