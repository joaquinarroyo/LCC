#ifndef __COMANDOS_H__
#define __COMANDOS_H__
#include <ctype.h>
#include "conjuntos.h"

/**
 * Recibe un string que representa al comando escrito por consola y 
 * devuelve un entero, el cual representa a un caso del switch,
 * dependiendo del comando recibido.
 */
int opcion(char comando[]);

/**
 * Recibe un string que representa al conjunto escrito por extension y 
 * devuelve su cardinal.
 */
int cantidad_elementos(char comando[]);

/**
 * Recibe un string que representa al comando escrito por consola y 
 * devuelve el alias relacionado a la operacion recibida en el comando.
 */
char *comando_alias(char comando[]);

/**
 * Recibe un string que representa al conjunto escrito por extension o 
 * compresion, un arreglo de enteros, toma los enteros del comando, 
 * y los inserta en el arreglo.
 */
void comando_conjunto(char comando[], int conjunto[], int tipo, int cantidad);

/**
 * Recibe un string que representa al comando escrito por consola y revisa 
 * que sea un comando valido para conjunto por extension.
 */
int extension_assert(char comando[]);

/**
 * Recibe un string que representa al comando escrito por consola y revisa 
 * que sea un comandovalido para conjunto por compresion.
 */
int compresion_assert(char comando[]);

/**
 * Recibe un string que representa al comando escrito por consola y revisa 
 * que sea un comando valido para las operaciones que relacionan 
 * dos conjuntos(union, interseccion y resta).
 */
int operaciones_dos_conj_assert(char comando[]);

/**
 * Recibe un string que representa al comando escrito por consola y revisa
 * que sea un comandovalido para la operacion complemento.
 */
int compl_assert(char comando[]);

/**
 * Recibe un string que representa al comando escrito por consola el cual va 
 * a representar una operacion que relaciona dos conjuntos, y un arreglo
 * de char punteros, y va a insertar los alias de los conjuntos en el arreglo.
 * Ej "A = B | C", inserta en el arreglo de punteros B y C.
 */
void comando_aliasbyc(char comando[], char* aliasByC[]);

/**
 * Recibe un string que representa al comando escrito por consola el cual va 
 * a representar la operacion complemento y va a devolver el alias del conjunto
 * al cual se le va a calcular el complemento.
 * Ej "A = ~B", devuelve B;
 */
char *comando_alias_compl(char comando[]);

#endif /* __COMANDOS_H__ */
