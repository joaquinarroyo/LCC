# Cosas para hacer

- Paralelizar la mayor parte del tiempo de cómputo de su aplicación con directivas OpenMP.

# Entrega

## Presentación de los resultados en video (máx. 5 minutos)

La presentación debe incluir:

- **Mejora sobre el final del Lab2** a partir de la puesta en común. Este será el inicio del Lab3.
- **Explicación de las estrategias intentadas** y la implementación final.
- **Gráficas para distintos tamaños del problema** (si influyen), con series para distintas cantidades de hilos:
  - La **métrica de performance seleccionada**, comparando también contra la mejor implementación obtenida anteriormente.
  - **Eficiencia respecto a la mejor versión de un hilo disponible** (no necesariamente `OMP_NUM_THREADS=1 ./a.out`).
- **Roofline** de la configuración más veloz obtenida.
- **Análisis de los resultados obtenidos**.
- **Potenciales mejoras en la paralelización**.
