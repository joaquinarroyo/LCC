# Respuestas Plancha 1 - Introducción a NachOS

**Alumnos:** Arroyo Joaquin, Bobe Julio, Grau Marianela

---

### 1. ¿Por qué se prefiere emular una CPU en vez de utilizar directamente la CPU existente?

NachOS utiliza una CPU emulada para facilitar el debugging y evitar riesgos sobre el hardware real. Permite experimentar con el sistema operativo sin afectar la máquina anfitriona.

---

### 2. ¿Cuánta memoria tiene la máquina simulada para NachOS?

La memoria simulada es de `32*128` bytes.  
**Referencia:** `machine/mmu.hh`

---

### 3. ¿Qué modificaría para cambiar la cantidad de memoria?

Modificar la variable `NUM_PHYS_PAGES` en `machine/mmu.hh`.

---

### 4. ¿De qué tamaño es un disco?

El disco tiene tamaño `32*32*128` bytes (tracks * sectores * bytes por sector).  
**Referencia:** `machine/disk.hh`

---

### 5. ¿Cuántas instrucciones de MIPS simula la máquina virtual de NachOS?

Simula 63 instrucciones MIPS.  
**Referencia:** `machine/encoding.hh`

---

### 6. ¿En qué archivos está definida la función main? ¿En qué archivo está definida la función main del ejecutable nachos del directorio userprog?

La función `main` está definida en varios archivos, incluyendo:  
- `threads/main.cc` (main del ejecutable nachos en userprog)  
- Otros: `bin/coff2flat.c`, `bin/coff2noff.c`, `userland/halt.c`, etc.

---

### 7. Nombre los archivos fuente en los que figuran las funciones y métodos llamados por el main de Nachos al ejecutarlo en el directorio threads, hasta dos niveles de profundidad.

Ver `threads/main.cc` para la función `main`.  
Ejemplo de funciones llamadas y sus archivos:  
main:
 - Initialize                   (threads/system.cc):
   - ASSERT                     (lib/assert.hh y lib/assert.cc)
   - strcmp                     (string.h)
   - ParseDebugOpts             (threads/system.cc)
   - RandomInit                 (machine/system_dep.cc)
   - atof                       (stdlib.h)
   - atoi                       (stdlib.h)
   - SetFlags                   (lib/debug.cc)
   - SetOpts                    (lib/debug.cc)
   - Timer                      (machine/timer.cc)
   - CallOnUserAbort            (machine/system_dep.cc)
   - Machine                    (machine/machine.cc)
   - SetExceptionHandlers       (userprog/exception.cc)
   - SynchDisk                  (filesys/synch_disk.cc)
   - FileSystem                 (filesys/file_system.cc)
   - PostOffice                 (network/post.cc)
 - DEBUG                        (Macro)
   - ASSERT                     (lib/assert.hh y lib/assert.cc)
   - IsEnabled                  (lib/debug.cc)
   - fprintf                    (stdlib.h)
   - va_start                   (stdarg.h)
   - vfprintf                   (stdarg.h)
   - va_end                     (stdarg.h)
   - fflush                     (stdio.h)
   - Delay                      (machine/system_dep.cc)
   - getchar                    (stdio.h)
 - strcmp                       (string.h)
 - SysInfo
   - printf                     (stdlib.h)
 - PrintVersion                 (threads/main.cc)
   - printf                     (stdlib.h)
 - ThreadTest                   (threads/thread_test.cc)
   - DEBUG                      (lib/debug.cc)
   - Choose                     (threads/thread_test.cc)
   - Run                        (threads/thread_test.cc)
 - interrupt->Halt              (machine/interrupt.cc)
   - printf                     (stdlib.h)
   - Print                      (machine/statistics.cc)
   - Cleanup                    (threads/system.cc)
 - ASSERT                       (lib/assert.hh y lib/assert.cc)
   - fprintf                    (stdlib.h)
   - fflush                     (stdio.h)
   - abort                      (stdlib.h)
 - StartProcess                 (userprog/prod_test.cc)
   - ASSERT                     (lib/assert.hh y lib/assert.cc)
   - Open                       (filesys/file_system.cc)
   - printf                     (stdlib.h)
   - AddresSpace                (userprog/address_space.cc)
   - InitRegisters              (userprog/address_space.cc)
   - RestoreState               (userprog/address_space.cc)
   - Run                        (machine/mips_sim.cc)
 - ConsoleTest                  (userprog/prog_test.cc)
   - Console                    (machine/console.cc)
   - Semaphore                  (threads/semaphore.cc)
   - P                          (threads/semaphore.cc)
   - GetChar                    (machine/console.cc)
   - PutChar                    (machine/console.cc)
 - Copy                         (filesys/fs_test.cc)
   - ASSERT                     (lib/assert.hh y lib/assert.cc)
   - fopen                      (stdio.h)
   - printf                     (stdlib.h)
   - fseek                      (stdio.h)                     
   - ftell                      (stdio.h)
   - DEBUG                      (lib/debug.cc)
   - Create                     (filesys/file_system.cc)
   - Open                       (filesys/file_system.cc)
   - fclose                     (stdlib.h)
 - Print                        (main.cc)
   - Open                       (filesys/file_system.cc)
   - fprintf                    (stdlib.h)
   - Read                       (filesys/file_system.cc)
   - printf                     (stdlib.h)
 - printf                       (stdlib.h)
 - fileSystem->Remove           (filesys/file_system.cc)
   - ASSERT                     (lib/assert.hh y lib/assert.cc)
   - Directory                  (filesys/directory.cc)
   - FetchFrom                  (filesys/directory.cc)
   - Find                       (filesys/directory.cc)
   - FileHeader                 (filesys/file_header.cc)
   - Bitmap                     (lib/bitmap.cc)
   - Deallocate                 (filesys/file_header.cc)
   - Clear                      (lib/bitmap.cc)
   - Remove                     (filesys/directory.cc)
   - WriteBack                  (lib/bitmap.cc)
 - fileSystem->List             (filesys/file_system.cc)
   - Directory                  (filesys/directory.cc)
   - FetchFrom                  (filesys/directory.cc)
   - List                       (filesys/file_system.cc)
 - fileSystem->Print            (filesys/file_system.cc)
   - FileHeader                 (filesys/file_header.cc)
   - Bitmap                     (lib/bitmap.cc)
   - Directory                  (filesys/directory.cc)
   - FetchFrom                  (filesys/directory.cc)
   - Print                      (lib/bitmap.cc)
 - fileSystem->Check            (filesys/file_system.cc)
   - DEBUG                      (lib/debug.cc)
   - Bitmap                     (lib/bitmap.cc)
   - Mark                       (lib/bitmap.cc)
   - FileHeader                 (filesys/file_header.cc)
   - GetRaw                     (filesys/file_header.cc)
   - FetchFrom                  (filesys/file_header.cc)
   - CheckForError              (filesys/file_system.cc)
   - CheckFileHeader            (filesys/file_system.cc)
   - Directory                  (filesys/directory.cc)
   - CheckDirectory             (filesys/file_system.cc)
   - CheckBitmaps               (filesys/file_system.cc)
 - PerformanceTest              (filesys/fs_test.cc)
   - printf                     (stdlib.h)
   - Print                      (machine/statistics.cc)
   - FileWrite                  (filesys/fs_test.cc)
   - FileRead                   (filesys/fs_test.cc)
   - Remove                     (filesys/file_system.cc)
   - printf                     (stdlib.h)
 - SystemDep::Delay             (machine/system_dep.cc)
   - sleep                      (unistd.h)
 - Finish                       (threads/thread.cc)
   - SetLevel                   (machine/interrupt.cc)
   - ASSERT                     (lib/assert.hh y lib/assert.cc)
   - DEBUG                      (lib/debug.cc)
   - Sleep                      (threads/thread.cc)

---

### 8. ¿Qué efecto hacen las macros ASSERT y DEBUG definidas en lib/utility.hh?

- `ASSERT`: Verifica condiciones y aborta si son falsas, mostrando información de error.  
- `DEBUG`: Imprime mensajes de depuración si la bandera correspondiente está activa.  
**Referencia:** `lib/utility.hh`, `lib/assert.hh`, `lib/debug.cc`

---

### 9. Comente el efecto de las distintas banderas de depuración.

- `location`: Muestra archivo y línea en mensajes de debug.
- `function`: Muestra el nombre de la función llamante.
- `sleep`: Pausa tras cada mensaje de debug.
- `interactive`: Espera input del usuario tras cada mensaje de debug.  
**Referencia:** `lib/debug_opts.hh`

---

### 10. ¿Dónde están definidas las constantes USER_PROGRAM, FILESYS_NEEDED, FILESYS_STUB y NETWORK?

Definidas en los Makefile de los subdirectorios de `/code`.

---

### 11. ¿Qué argumentos de línea de comandos admite Nachos? ¿Qué efecto tiene la opción -rs?

Nachos acepta argumentos como:  
`-d`, `-do`, `-p`, `-rs`, `-z`, `-tt`, `-s`, `-x`, `-tc`, `-f`, `-cp`, `-pr`, `-rm`, `-ls`, `-D`, `-c`, `-tf`, `-n`, `-id`, `-tn`  
`-rs <random seed #>`: Establece la semilla para el generador aleatorio, afectando el orden de ejecución de los hilos.  
**Referencia:** `threads/main.cc`

---

### 12. Al ejecutar `nachos -i`, se obtiene información del sistema. Sin embargo está incompleta. Modifique el código para que se muestren los datos que faltan.

Solución en el archivo:  
`threads/sys_info.cc`  
Reemplazar los valores `UNKNOWN` por las variables correctas.

---

### 13. ¿Cuál es la diferencia entre las clases List y SynchList?

- `List`: Lista enlazada simple.
- `SynchList`: Lista con mecanismos de sincronización para acceso seguro por múltiples hilos.  
**Referencia:** `threads/synch_list.hh`, `threads/list.hh`

---

### 14. Modifique el caso de prueba simple del directorio threads para que se generen 5 hilos en lugar de 2.

Ver código en:  
`threads/thread_test_simple.cc`

---

### 15. Modifique el caso de prueba para que estos cinco hilos utilicen un semáforo inicializado en 3. Esto debe ocurrir solo si se define la macro de compilación SEMAPHORE_TEST.

Ver código en:  
`threads/thread_test_simple.cc`  
(Descomentar la bandera `-DSEMAPHORE_TEST` en `threads/Makefile`)

---

### 16. Agregue al caso anterior una línea de depuración que diga cuándo cada hilo hace un P() y cuándo un V(). La salida debe verse por pantalla solamente si se activa la bandera de depuración correspondiente.

Ver código en:  
`threads/thread_test_simple.cc`

---

### 17. En threads se provee un caso de prueba que implementa el jardín ornamental. Sin embargo, el resultado es erróneo. Corríjalo de forma que se mantengan los cambios de contexto, sin agregar nuevas variables.

Ver código corregido en:  
`threads/thread_test_garden.cc`

---

### 18. Replique el jardín ornamental en un nuevo caso de prueba. Revierta la solución anterior y solucione el problema usando semáforos esta vez.

Ver código en:  
`threads/thread_test_garden_sem.cc`,  
`threads/thread_test_garden_sem.hh`,  
`Makefile.common`,  
`threads/thread_test.cc`
