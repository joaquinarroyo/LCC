# Cosas para hacer

- Encontrar una **métrica de performance** del problema:
  - Que sea **comparable para cualquier tamaño del problema**.
  - Mejor performance para **valores más altos** (mejor ⇒ arriba).
  - Usualmente: `photons/ns`, `atoms/ns`, `cells/ns`.
  - Idealmente: **FLOPS/IPS** si se puede calcular.

- Mejorar la performance cambiando cosas, por ejemplo:
  - **Compiladores** (GCC, Clang, Intel, NVIDIA/PGI?).
  - **Opciones de compilación**: explorar mucho, pero no al azar.
  - **Mejoras algorítmicas y/o numéricas** (si las hay, e.g. RNG).
  - **Optimizaciones de cálculos** (que no haga ya el compilador).
  - **Unrolling de loops** y otras fuentes de ILP (otra vez, solo si el compilador no lo hace).
  - **Sistema de memoria**: HugePages y estrategias cache-aware (aunque es probable que no rindan sin paralelismo o en sistemas pequeños).

---

# Hints

- Tomar decisiones sobre dónde mirar primero en el código haciendo **profiling** (ej.: `perf`, VTune).

- **Automatizar TODO**, será útil todo el cuatrimestre:
  - Compilación.
  - Tests para detectar rápidamente errores.
  - Ejecución y medición de performance.
  - Procesamiento de la salida del programa (formato CSV recomendado).
  - Generación de gráficas.

---

# Entrega

- **Video privado en YouTube** con presentación de los resultados (≤ 5 minutos).
  - Penalización: **-1 punto por cada minuto adicional**.

## Elementos obligatorios:

- **Características del hardware y del software**:
  - **CPU**: modelo y velocidad.
    - Poder de cómputo de un core medido con **Empirical Roofline Toolkit** o **LINPACK**.
  - **Memoria**: capacidad, velocidad, canales ocupados.
    - Ancho de banda de un core medido con **Empirical Roofline Toolkit** o **STREAM**.
  - **Compiladores**: nombres y versiones.
  - **Sistema operativo**: nombre, versión y arquitectura.

- **Gráficas de scaling** para la versión más rápida obtenida:
  - **Performance vs. tamaño del problema** (usualmente lin-log).
  - No se espera scaling lineal: se debe explorar el comportamiento según la **jerarquía de memoria**.
  - Considerar la **calidad estadística** de los resultados.

- **Optimizaciones probadas y sus resultados**:
  - Explicación de cada optimización.
  - Medición que **valide la explicación**.
  - Intentar medir **causas** además del resultado en performance.
