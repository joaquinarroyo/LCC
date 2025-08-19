# Respuestas Plancha 2 - Sincronización de Hilos

**Alumnos:** Arroyo Joaquin, Bobe Julio, Grau Marianela

---

### 1. Implemente “locks” (candados) y variables de condición.

Para implementar los “locks” y variables de condición, se deben usar semáforos como base.  
Las interfaces públicas están definidas en `threads/synch.hh`, en las clases `Lock` y `Condition`.  
Se debe implementar la función `Lock::IsHeldByCurrentThread` para verificar que el hilo que realiza un `Acquire` no posea el “lock” y que el hilo que realiza un `Release` sí lo posea.  
**Referencia:** `threads/synch.cc`

---

### 2. Nachos provee una interfaz para el test del problema del productor y consumidor.

Se debe agregar una implementación del problema del productor y consumidor utilizando las estructuras implementadas en el ejercicio anterior.  
**Referencia:** `threads/producer_consumer_test.cc`

---

### 3. Implemente paso de mensajes entre hilos a través de canales.

Se debe crear una nueva clase `Channel` con los métodos:

```cpp
void Channel::Send(int message);
void Channel::Receive(int *message);
```

- `Send` espera atómicamente hasta que se llame a `Receive` y luego copia el mensaje en el búfer de `Receive`.
- `Receive` es bloqueante si no hay emisores esperando.

La solución debe funcionar con múltiples emisores y receptores.  
**Referencia:** `threads/channel.hh`, `threads/channel.cc`

---

### 4. Implemente un método `Thread::Join`.

El método `Thread::Join` debe bloquear al llamante hasta que el hilo en cuestión termine.  
Se debe agregar un argumento al constructor de `Thread` para indicar si se llamará a `Join` sobre este hilo.  
**Referencia:** `threads/thread.hh`, `threads/thread.cc`

---

### 5. Planificación con Prioridades.

- Se debe implementar multicolas con prioridad, donde los hilos tienen prioridades fijas (positivas, con 0 como la mínima prioridad).  
  El planificador debe elegir siempre el hilo listo con mayor prioridad.  
  **Referencia:** `threads/scheduler.hh`, `threads/scheduler.cc`

- Para evitar el problema de inversión de prioridades en “locks” y variables de condición, se debe modificar la implementación.  
  **Referencia:** `threads/synch.hh`, `threads/synch.cc`

La propagación de prioridades requiere conocer qué hilo posee el recurso, algo que los semáforos no pueden proporcionar. Por eso, esta técnica solo es posible con locks y variables de condición.
