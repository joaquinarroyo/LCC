# Respuestas Plancha 5 - Sistema de Archivos

**Alumnos:** Arroyo Joaquin, Bobe Julio, Grau Marianela

---

## 1. Sincronización para acceso concurrente

a) Archivos pueden ser usados por múltiples hilos, cada uno con su propio "seek".

Implementado en OpenFile, cada una de estas estructuras tiene su propio offset.

b) Operaciones deben ser atómicas y serializables.  

Implementado sobre OpenFile::Read, OpenFile::Write a más bajo nivel, con información de acceso concurrente en estructura FileData.

Además en FileSystem::Create, FileSystem::Open, FileSystem::Remove, FileSystem::CloseFile y FileSystem::Mkdir, se hicieron los chequeos correspondientes para permitir acceso concurrente a tablas compartidas.

c) Un archivo puede ser borrado y seguido usando si ya estaba abierto por algún hilo.

Implementado con la bandera "deleted" sobre FileData. Si el file está siendo usado, se lo marca con esta bandera para posterior eliminación en CloseFile.

## 2. Permita que el tamaño máximo de un archivo sea tan grande como el disco

Implementado con FileHeaders anidados. Cada FileHeader además de sus punteros directos, apunta a otro en caso de necesitar indirecciones. Ver file_header.cc y raw_file_header.cc

## 3. Permitir expansión de archivos

Implementado con función Expand en archivo file_header.cc

## 5. Permitir directorios jerárquicos

Implementado en file_system.cc

## Testing con programas de userland

Hacer desde filesys

```
./nachos -cp ../userland/<program> <program>
```

por ej.

```
./nachos -cp ../userland/shell shell
./nachos -cp ../userland/mkdir mkdir
./nachos -cp ../userland/cd cd
./nachos -cp ../userland/touch touch
./nachos -cp ../userland/ls ls
./nachos -cp ../userland/echo echo
./nachos -cp ../userland/write write
./nachos -cp ../userland/rm rm
```

Luego,

```
./nachos -x shell
```
