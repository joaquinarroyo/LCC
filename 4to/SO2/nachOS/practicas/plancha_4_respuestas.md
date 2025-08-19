# Respuestas Plancha 4 - Memoria Virtual

**Alumnos:** Arroyo Joaquin, Bobe Julio, Grau Marianela

---

### 1. Implemente TLB

#### a) Invalidar el estado de la TLB en cada cambio de contexto

El estado de la TLB se invalida correctamente en el método `Scheduler::Run` al realizar un cambio de contexto. Se llama al 
método `AddressSpace::RestoreState()` de `address_space.cc`.
**Referencia:** `userprog/address_space.cc`, `threads/scheduler.cc`

#### b) Reintentar lecturas/escrituras en caso de fallo

El manejador de excepciones reintenta lecturas/escrituras tras manejar fallos de página. Ver `PageFaultHandler`.
**Referencia:** `userprog/exception.cc`

#### c) Manejador de `PageFaultException`

El manejador de `PageFaultException` está implementado. Utiliza un índice circular para reemplazo en la TLB.  
**Referencia:** `machine/mmu.cc`

#### d) Manejador de `ReadOnlyException`

El manejador de `ReadOnlyException` está implementado y bloquea escrituras en páginas de solo lectura.  
**Referencia:** `userprog/exception.cc`

---

### 2. Calcular el hit ratio de la TLB

El cálculo del hit ratio de la TLB está implementado en `machine/statistics.cc`. Se registran estadísticas de fallos y aciertos.
**Referencia:** `machine/statistics.cc`

Para probar, se ejecutaron programas grandes (`matmult`, `sort`) con diferentes tamaños de TLB (32 y 64 entradas).

DIM 20, TLB_SIZE 32: faults 161 hits 709446
DIM 20, TLB_SIZE 64: faults 119 hits 709412
DIM 50, TLB_SIZE 32: faults 347318 hits 12043412
DIM 50, TLB_SIZE 64: faults 313599 hits 12027143
DIM 512, TLB_SIZE 32: 
DIM 512, TLB_SIZE 64: 

La mejora de 32 a 64 entradas para la TLB no es significativa, incluso para entradas significativamente mas grandes
por esto nos quedamos con la TLB de tamaño 32.
---

### 3. Carga por demanda (demand loading)

Cuando `DEMAND_LOADING` está activado, el constructor de espacio de direcciones no carga páginas de código/datos. Estas se cargan al primer acceso mediante el manejador de fallos de página.  
**Referencia:** `userprog/address_space.cc`, `userprog/exception.cc`

---

### 4. Intercambio de páginas (swap)

#### a) Coremap

El bitmap fue reemplazado por un coremap para gestionar marcos de memoria.  
**Referencia:** `lib/coremap.cc`

#### b) Archivos de swap

Se crean archivos `SWAP.<pid>` para cada proceso.  
**Referencia:** `userprog/address_space.cc`

#### c) Política de reemplazo

La política de reemplazo utiliza la función `PickVictim`, implementada en `lib/coremap.cc`.  
**Referencia:** `lib/coremap.cc`

#### d) Reemplazo de páginas

El reemplazo de páginas está implementado. La MMU actualiza los bits de uso/modificación en la TLB, y la tabla de páginas se sincroniza al reemplazar entradas.  
**Referencia:** `machine/translate.cc`, `lib/coremap.cc`

#### e) Estadísticas de swapping

Se agregaron estadísticas al núcleo para medir el rendimiento del sistema de swapping.  
**Referencia:** `code/statistics.cc`

---

### 5. Mejore la política de reemplazo

#### a) FIFO

La política FIFO está implementada y se activa con la bandera `PRPOLICY_FIFO`. Elije como víctima la página más antigua.
**Referencia:** `lib/coremap.cc`

También está implementada `PRPOLICY_SECOND_CHANCE` que evita eliminar páginas que han sido referenciadas recientemente.

#### b) LRU o Clock

También está implementada `PRPOLICY_SECOND_CHANCE` que evita eliminar páginas que han sido referenciadas recientemente.

**Referencia:** `lib/coremap.cc`