# 4ta Practica Laboratorio 
# Complementos Matematicos I
# Consigna: Implementar los siguientes metodos
from math import inf as INF
#import heapq

def peso(grafo,a,b):
    resultado = INF
    for x in grafo[1]:
        if ((x[0] == a and x[1] == b) or (x[0] == b and x[1] == a)):
            resultado = x[2]
    return resultado

def tomarMinimo(diccionario, lista):
    posiblesVertices = set(diccionario.keys()) - set(lista)
    buscarMinimo = {}
    for x in posiblesVertices:
        buscarMinimo[x] = diccionario[x]
    valorMin = min(buscarMinimo.values())
    minimo = list(buscarMinimo.keys())[list(buscarMinimo.values()).index(valorMin)]
    return minimo

def sucesores(grafo, vertice, lista):
    res = []
    for x in grafo[1]:
        if x[1] == vertice and x[0] not in lista:
            res.append(x[0])
        elif x[0] == vertice and x[1] not in lista:
            res.append(x[1])
    return res


def dijkstra(grafo, vertice):
    """
    Formato entrada: (['A', 'B', 'C'], [('A', 'B', 5.5), ('B', 'C', 16)]), 'C'
    Dado un grafo (en formato de listas con pesos), aplica el algoritmo de
    Dijkstra para hallar el COSTO del camino mas corto desde el vertice de origen
    al resto de los vertices.
    Formato resultado: {'A': 21.5, 'B': 16, 'C': 0}
    (Nodos que no son claves significa que no hay camino a ellos)
    """
    resultado = {}
    if vertice not in grafo[0]:
        return resultado
    visitados = []
    for x in grafo[0]:
        resultado[x] = peso(grafo,vertice,x)
    resultado[vertice] = 0
    visitados.append(vertice)
    while (set(visitados) != set(grafo[0])):
        actual = tomarMinimo(resultado, visitados)
        visitados.append(actual)
        for x in sucesores(grafo,actual,visitados):
            if resultado[x] > resultado[actual] + peso(grafo, actual, x):
                resultado[x] = resultado[actual] + peso(grafo, actual, x)
    for x in resultado:
        if resultado[x] == INF:
            del resultado[x]
    return resultado



def dijkstra_2(grafo, vertice):
    """
    Dado un grafo (en formato de listas con pesos), aplica el algoritmo de
    Dijkstra para hallar el CAMINO mas corto desde el vertice de origen
    a cada uno del resto de los vertices.
    Formato resultado: {'a': ['a'], 'b': ['a', 'b'], 'c': ['a', 'b', 'c']}
    (Nodos que no son claves significa que no hay camino a ellos)
    """
    caminoResultado = {}
    resdijkstra = {}
    visitados = []
    for x in grafo[0]:
        if peso(grafo, x, vertice) == INF:
            caminoResultado[x] = []
            resdijkstra[x] = INF
        else:
            caminoResultado[x] = [vertice,x]
            resdijkstra[x] = peso(grafo, x, vertice)
    resdijkstra[vertice] = 0
    caminoResultado[vertice] = [vertice]
    visitados.append(vertice)
    while (set(visitados) != set(grafo[0])):
        verticeActual = tomarMinimo(resdijkstra, visitados)
        caminoActual = caminoResultado[verticeActual]
        visitados.append(verticeActual)
        for x in sucesores(grafo, verticeActual, visitados):
            if resdijkstra[x] > resdijkstra[verticeActual] + peso(grafo, verticeActual, x):
                resdijkstra[x] = resdijkstra[verticeActual] + peso(grafo, verticeActual, x)
                caminoResultado[x] = caminoActual + [x]
    for x in caminoResultado:
        if caminoResultado[x] == []:
            del caminoResultado[x]
    return caminoResultado


def main():
    grafoCreado = (['A', 'B', 'C', 'D', 'E'], [('A', 'B', 4), ('A', 'C', 2), ('B', 'C', 1), ('B', 'D', 2), ('B', 'E', 3), ('D', 'C', 4), ('C', 'E', 5), ('D', 'E', 1)])
    #grafoCreado = (['A', 'B', 'C'], [('A', 'B', 4), ('A', 'C', 2), ('B', 'C', 1)])
    print(dijkstra_2(grafoCreado, 'A'))
    print(dijkstra(grafoCreado, 'A'))


if __name__ == "__main__":
    main()