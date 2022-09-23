#! /usr/bin/python
# -*- coding: utf-8 -*-

# 3ra Practica Laboratorio 
# Complementos Matematicos I
# Consigna: Implementar los siguientes metodos

"""
Recordatorio: 
- Un camino/ciclo es Euleriano si contiene exactamente 1 vez
a cada arista del grafo
- Un camino/ciclo es Hamiltoniano si contiene exactamente 1 vez
a cada vértice del grafo
"""

def chequear_argumentos(grafo, camino):
    bandera = 1
    for x in grafo[1]:
        if x[0] not in grafo[0] or x[1] not in grafo[0]:
            bandera = 0
    n = len(camino)
    for x in range(0, n - 1):
        if camino[x] not in grafo[1] or camino[x][1] != camino[x+1][0]:
            bandera = 0
    if camino[n - 1] not in grafo[1]:
        bandera = 0
    return bandera

def even(n):
    return n%2 == 0

def esCaminoEuleriano(grafo, camino):
    """Comprueba si una lista de aristas constituye un camino euleriano
    en un grafo.
    Args:
        graph (grafo): Grafo en formato de listas.
                       Ej: (['a', 'b', 'c'], [('a', 'b'), ('b', 'c')])

        path (lista de aristas): posible camino
                                 Ej: [('a', 'b'), ('b', 'c')]
    Returns:
        boolean: path es camino euleriano en graph
    Raises:
        TypeError: Cuando el tipo de un argumento es inválido
    """

    if not(chequear_argumentos(grafo, camino)):
        raise Exception("Argumentos invalidos.")

    contador = 0
    for ver in camino:
        if ver in camino:
            contador +=1
    if contador == len(grafo[1]):
        return True
    else:
        return False

def esCicloEuleriano(grafo, ciclo):
    """Comprueba si una lista de aristas constituye un ciclo euleriano
    en un grafo.

    Args:
        graph (grafo): Grafo en formato de listas.
                       Ej: (['a', 'b', 'c'], [('a', 'b'), ('b', 'c')])

        path (lista de aristas): posible ciclo
                                 Ej: [('a', 'b'), ('b', 'c')]

    Returns:
        boolean: path es ciclo euleriano en graph

    Raises:
        TypeError: Cuando el tipo de un argumento es inválido
    """

    n = len(grafo[1])
    vInicio = grafo[1][0][0]
    vFinal = grafo[1][n][1]
    if not(chequear_argumentos(grafo, ciclo)) or vInicio != vFinal:
        raise Exception("Argumentos invalidos.")

    contador = 0
    for ver in ciclo:
        if ver in ciclo:
            contador +=1
    if contador == n:
        return True
    else:
        return False


def esCaminoHamiltoniano(grafo, camino):
    """Comprueba si una lista de aristas constituye un camino hamiltoniano
    en un grafo.
    Args:
        graph (grafo): Grafo en formato de listas.
                       Ej: (['a', 'b', 'c'], [('a', 'b'), ('b', 'c')])

        path (lista de aristas): posible camino
                                 Ej: [('a', 'b'), ('b', 'c')]
    Returns:
        boolean: path es camino hamiltoniano en graph
    Raises:
        TypeError: Cuando el tipo de un argumento es inválido
    """

    if not(chequear_argumentos(grafo, camino)):
        raise Exception("Argumentos invalidos.")

    disjoint_set = {}
    for x in grafo[0]:
        disjoint_set[x] = 0
        n+=1
    for x in camino:
        disjoint_set[x[0]] = disjoint_set[x[0]] + 1
        disjoint_set[x[1]] = disjoint_set[x[1]] + 1
    val_list = list(disjoint_set.values())
    contador = 0
    bandera = 1
    for x in val_list:
        if x == 1:
            contador +=1
        if x != 2 and x != 1:
            bandera = 0
    if bandera and contador == 2:
        return True
    else: 
        return False


def esCicloHamiltoniano(grafo, ciclo):
    """Comprueba si una lista de aristas constituye un ciclo hamiltoniano
    en un grafo.

    Args:
        graph (grafo): Grafo en formato de listas.
                       Ej: (['a', 'b', 'c'], [('a', 'b'), ('b', 'c'), ('c', 'd'), ('d', 'a'), ('d', 'b')])

        path (lista de aristas): posible ciclo
                                 Ej: [('a', 'b'), ('b', 'c'), ('c', 'd'), ('d', 'a')]

    Returns:
        boolean: path es ciclo hamiltoniano en graph

    Raises:
        TypeError: Cuando el tipo de un argumento es inválido
    """

    n = len(grafo[1])
    vInicio = grafo[1][0][0]
    vFinal = grafo[1][n][1]
    if not(chequear_argumentos(grafo, ciclo)) or vInicio != vFinal:
        raise Exception("Argumentos invalidos.")

    disjoint_set = {}
    for x in grafo[0]:
        disjoint_set[x] = 0
        n+=1
    for x in ciclo:
        disjoint_set[x[0]] = disjoint_set[x[0]] + 1
        disjoint_set[x[1]] = disjoint_set[x[1]] + 1
    val_list = list(disjoint_set.values())
    bandera = 1
    for x in val_list:
        if x != 2:
            bandera = 0
    if bandera:
        return True
    else: 
        return False


def tieneCaminoEuleriano(grafo):
    """Comprueba si un grafo no dirigido tiene un camino euleriano.
    Args:
        graph (grafo): Grafo en formato de listas.
                       Ej: (['a', 'b', 'c', 'd', 'e'], 
                            [('a', 'b'), ('b', 'c'), ('d', 'e'), ('c', 'd'), ('d', 'a')])

    Returns:
        boolean: graph tiene un camino euleriano

    Raises:
        TypeError: Cuando el tipo del argumento es inválido
    """

    bandera = 1
    for x in grafo[1]:
        if x[0] not in grafo[0] or x[1] not in grafo[1]:
            bandera = 0
    if not(bandera):
        raise Exception("Argumento invalido.")

    disjoint_set = {}
    for x in grafo[0]:
        disjoint_set[x] = 0
        n+=1
    for x in grafo[1]:
        disjoint_set[x[0]] = disjoint_set[x[0]] + 1
        disjoint_set[x[1]] = disjoint_set[x[1]] + 1
    val_list = list(disjoint_set.values())

    contador = 0
    for x in val_list:
        if not(even(x)):
            contador +=1
    if contador == 2 or contador == 0:
        return True
    else: 
        return False


class Graph:
    """
    Definimos esta clase como ayuda a la implementación del algoritmo de Fleury
    """

    def __init__(self, grafo_lista):
        """
        Inicializamos el grafo a partir de un grafo en representación de lista
        """

        self.V = grafo_lista[0]
        self.graph = self.fromListToDicc(grafo_lista)

    def fromListToDicc(self, grafo_lista):
        """Toma un grafo no dirigido en representación de lista y retorna un diccionario, en donde las claves
        son vértices y los valores son listas de vértices, representando cada una de las aristas. Por ejemplo:
        {'a': ['b', 'e'],..} representa la existencia de las aristas ('a','b') y ('a','e')
        """
        graph = {v: [] for v in grafo_lista[0]}
        for (u, v) in grafo_lista[1]:
            graph[u].append(v)
            graph[v].append(u)
        return graph

    def removeEdge(self, u, v):
        """Dados dos vértices (u y v), elimina la arista (u,v) (y también la arista (v,u) puesto que es un grafo
        no dirigido)
        """
        self.graph[u].remove(v)
        self.graph[v].remove(u)

    def addEdge(self, u, v):
        """Dados dos vértices (u y v), agrega la arista (u,v) (y también la arista (v,u) puesto que es un grafo
        no dirigido)"""
        self.graph[u].append(v)
        self.graph[v].append(u)

    def reachableVertices(self, v, visited):
        """Cuenta la cantidad de vértices alcanzables desde v, haciendo una búsqueda en profundidad.
        El argumento visited es un diccionario en donde las claves son los vértices, y los valores
        corresponden a un booleano indicando si el vértice fue visitado o no.
        La primera vez que se llama al método, ningún vértice debe haber sido visitado.
        """
        count = 1
        visited[v] = True
        for i in self.graph[v]:
            if not visited[i]:
                count = count + self.reachableVertices(i, visited)
        return count

    def isElegibleNextEdge(self, u, v):
        """Determina si la arista (u,v) es elegible como próxima arista a visitar."""

        pass

    def printEuler(self, u):
        """
        Imprime un camino o ciclo euleriano comenzando desde el vértice u.
        """
        for x in self.graph():
            print("("+u+", "+x[u])
            print(", ")
            u = x[u]


def caminoEuleriano(grafo_lista):
    """Obtiene un camino euleriano en un grafo no dirigido, si es posible

    Argumentos:
        grafo: Grafo en formato de listas. 
                Ej: (['a', 'b', 'c'], [('a', 'b'), ('b', 'c')])

    Retorno:
        lista de aristas: ciclo euleriano, si existe
        None: si no existe un camino euleriano
    """
    #grafo = Graph.fromListToDicc(grafo_lista)
    pass


def main():
    pass


if __name__ == '__main__':
    main()