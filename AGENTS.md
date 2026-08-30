# lcc — guía del repo para agentes

Archivo neutral respecto del agente. `CLAUDE.md` apunta acá; no hay una segunda
copia que mantener en sync.

## Qué es

Trabajos prácticos, prácticas y apuntes de la [Licenciatura en Ciencias de la
Computación](https://dcc.fceia.unr.edu.ar) (FCEIA, UNR), de 1ro a 5to más
optativas.

**Es un archivo, no un proyecto.** No hay build, ni tests, ni CI, ni
dependencias comunes: cada carpeta es una materia y cada materia trae el
lenguaje y las herramientas que le tocaron — Haskell, C, Rust, Python, Coq,
assembler, lo que sea.

## Qué esperar de un cambio acá

Casi siempre, agregar material de una materia. Nada de esto se refactoriza:
es trabajo entregado, y reescribirlo con criterio de hoy le saca el valor de
registro que tiene.

Si vas a tocar algo, quedate dentro de la carpeta de esa materia y seguí las
convenciones que ya haya ahí, que son las de la cátedra y no las mías.

## Convenciones

- Commits en Conventional Commits, en español.
- **Nunca agregar trailers de agente** — `Co-Authored-By: Claude`, `Generated
  with …`, links de sesión, o el equivalente de cualquier otro agente. El
  mensaje explica el cambio; quién lo tipeó no es parte del registro.
- No hay compuertas de calidad que correr. No inventes un `Makefile`.
