# Cosas para hacer

## Explorar qué se puede hacer respecto a autovectorización:
- Opciones de compilación.
- Cambios de código en líneas que previenen la vectorización para que el autovectorizador funcione.
- Intentar en gcc, icc, clang y otros compiladores.

## Vectorizar lo que tenga sentido a mano con:
- Intrinsics.
- ó ISPC *(ojo, esto no lo vimos, pero si alguien se quiere poner es un proyecto muy bueno)*:
    - Leer de a vectores desde memoria.
    - Procesar múltiples elementos simultáneamente.
    - Escribir de a vectores hacia memoria.

# Entrega

- Presentación de los resultados en video subido privado a YouTube de **<= 5 min**.
- Cada minuto de más, se descuentan **dos puntos**.
- **No vale grabar el video acelerado.**

## Incluir en la entrega:
- Mejoras de la versión de Lab1 luego de las presentaciones, si agregaron algo.
- Indicar el punto de partida, o sea la base desde donde largan Lab2.
- Cambios algorítmicos o *tweaks* que hicieron para que autovectorice.
- Qué partes hicieron con intrinsics.
- Cosas que **NO** funcionaron.
- Comprobación que los resultados siguen siendo correctos.
- Performance vs. tamaño del problema *(usualmente lin-log)*.
- Resumen de lo que lograron y lo que no.
- Indicar el punto de finalización en "veces de aceleración" **2x**, **7.4x**, etc.
