# Respuestas Plancha 3 - Programas de Usuario y Multiprogramación

**Alumnos:** Arroyo Joaquin, Bobe Julio, Grau Marianela

---

### 1. Espacios de direcciones

Las funciones para copiar datos entre el núcleo y el usuario están definidas en `userprog/transfer.hh`. Solo `ReadStringFromUser` está implementada. Las demás funciones (`ReadBufferFromUser`, `WriteBufferToUser`, `WriteStringToUser`) ya están implementadas en `userprog/transfer.cc`.  
**Referencia:** `userprog/transfer.cc`

---

### 2. Llamadas al sistema e interrupciones

Las llamadas al sistema definidas en `syscall.h` están implementadas en `userprog/syscall.cc`. Se verificó que las siguientes funciones están completas y robustas:

- **a)** `Create`, `Remove`, `Exit`  
  **Referencia:** `userprog/syscall.cc`

- **b)** `Read`, `Write` para consola  
  Se utiliza `SynchConsole`, implementada en `machine/synch_console.cc`.  
  **Referencia:** `machine/synch_console.cc`

- **c)** `Open`, `Close`  
  **Referencia:** `userprog/syscall.cc`

- **d)** `Read`, `Write` para archivos  
  **Referencia:** `userprog/syscall.cc`

- **e)** `Exec`, `Join`  
  Implementadas con soporte para multiprogramación y gestión de marcos de memoria física.  
  **Referencia:** `userprog/syscall.cc`, `lib/bitmap.cc`

---

### 3. Función para estado del planificador

La función interna del núcleo que imprime el estado actual del planificador está implementada en `threads/scheduler.cc`.  
**Referencia:** `threads/scheduler.cc`

---

### 4. Multiprogramación con time slicing

La multiprogramación con rebanadas de tiempo está implementada. El `Scheduler` almacena y recupera el estado de la máquina al hacer cambios de contexto.  
**Referencia:** `threads/scheduler.cc`, `machine/interrupt.cc`

---

### 5. Paso de argumentos con Exec

La llamada `Exec` permite pasar argumentos al programa de usuario. Se utiliza el estilo Unix, copiando los argumentos en la pila del usuario y pasando `argc` y `argv` en los registros correspondientes.  
**Referencia:** `userprog/args.cc`

---

### 6. Programas de usuario

#### a) Biblioteca de funciones (userland/lib.c)

La biblioteca incluye las funciones requeridas:  
- `unsigned strlen(const char *s);`
- `void puts(const char *s);`
- `void itoa(int n, char *str);`  
**Referencia:** `userland/lib.c`

#### b) Programas utilitarios: `cat`, `cp`, `rm`

Los programas utilitarios están implementados en `userland/` y compilados en el Makefile.  
**Referencia:** `userland/cat.c`, `userland/cp.c`, `userland/rm.c`, `userland/Makefile`

#### c) Shells

Los shells (`userland/shell.c` y `userland/tiny_shell.c`) permiten ejecutar comandos en primer plano. Se modificaron para soportar ejecución en segundo plano si la línea comienza con `&`.  
**Referencia:** `userland/shell.c`, `userland/tiny_shell.c`

Para ejecutar los programas hacer esto desde ```userland```

```
../userprog/nachos -x shell
-- touch test.txt
-- cat test.txt
-- rm test.txt
```