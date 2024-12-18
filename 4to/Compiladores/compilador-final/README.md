# Compiladores

Código para la materia Compiladores 2023 de [LCC](https://dcc.fceia.unr.edu.ar), [FCEIA](https://www.fceia.unr.edu.ar), [UNR](https://www.unr.edu.ar).

Este es el código a partir del cual los estudiantes empiezan a desarrollar un compilador.

## Intérprete FD4

Para correr el intérprete basta con ejecutar:

```code
cabal run
```

Las opciones soportadas por el intérprete de FD4 pueden verse utilizando el comando `:help` :

```code
FD4> :help
Lista de comandos:  Cualquier comando puede ser abreviado a :c donde
c es el primer caracter del nombre completo.

<expr>                  evaluar la expresión
let <var> = <expr>      definir una variable
:browse                 Ver los nombres en scope
:load <file>            Cargar un programa desde un archivo
:print <exp>            Imprime un término y sus ASTs sin evaluarlo
:reload                 Vuelve a cargar el último archivo cargado
:type <exp>             Chequea el tipo de una expresión
:quit, :Q               Salir del intérprete
:help, :?               Mostrar esta lista de comandos
```

## Entorno interactivo con GHCi

También pueden cargar un módulo específico del proyecto en el entorno interactivo GHCi:

```code
cabal exec ghci -- -isrc src/Parse.hs
```

La bandera `-isrc` es necesaria para indicarle a GHCi que los archivos que importa el módulo que
estamos cargando deben ser buscados dentro de la carpeta `src/`.

Alternativamente, pueden inicializar GHCi:

```code
cabal exec ghci
```

Y luego cargar el archivo deseado desde allí:

```code
ghci> :cd src/
ghci> :load Parse.hs
[1 of 3] Compiling Common           ( Common.hs, interpreted )
[2 of 3] Compiling Lang             ( Lang.hs, interpreted )
[3 of 3] Compiling Parse            ( Parse.hs, interpreted )
Ok, three modules loaded.
```

Notar que de esta forma también es necesario corregir el PATH de los archivos para no tener
problemas con las dependencias.

## Tests

Para poner a prueba el compilador utilizaremos una técnica denomidada _Test de Caja Negra_. Es
decir, trataremos al compilador como una función de la cual desconocemos su implementación y
simplemente compararemos el resultado que obtenemos al compilar un programa FD4 con el resultado
esperado. Si el resultado es el que esperamos, el compilador ha superado esa prueba, y sino lo ha
fallado.

### ¿Cómo correr los tests?
Para correr los tests, primero debemos asegurarnos de tener compilada la última versión de nuestro
compilador. Pueden hacerlo llamando a `cabal build`. Luego, bastará con llamar a `make test_all`.

```code
make test_all

OK	EVAL	tests/ok/00-basicos/000-basico.fd4
OK	EVAL	tests/ok/00-basicos/001-print.fd4
OK	EVAL	tests/ok/00-basicos/100-orden-print.fd4
OK	EVAL	tests/ok/00-basicos/101-print.fd4
OK	EVAL	tests/ok/00-basicos/200-seq.fd4
OK	EVAL	tests/ok/00-basicos/300-fun.fd4
---------------------------------
             Todo OK             
---------------------------------
```

Notar que si la versión del compilador no cambió, al volver al correr los tests los mismos no se
ejecutarán.

```code
make test_all

---------------------------------
             Todo OK             
---------------------------------

```
### ¿Cómo elegir qué tests correr?
Para cambiar los tests que queremos que se corran deberemos realizar un pequeño cambio en el archivo
`testing.mk`. Verán en las primeras líneas del mismo declarados distintos directorios que contienen
tests (algunos comentados). A medida que vayamos avanzando en las etapas del compilador, podremos ir
descomentando o agregando nuevos directorios con más tests que deberían ser soportados.

```code
TESTDIRS += tests/ok/00-basicos
#TESTDIRS += tests/ok/10-sugar
```
