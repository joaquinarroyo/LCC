#! /usr/bin/python

# 4ta Practica Laboratorio 
# Complementos Matematicos I
# Consigna: Implementar los siguientes metodos


def dijkstra(grafo, vertice):
    """
    Dado un grafo (en formato de listas con pesos), aplica el algoritmo de
    Dijkstra para hallar el COSTO del camino mas corto desde el vertice de origen
    al resto de los vertices.
    Formato de ingreso: [['a', 'b', 'c'], [('c', 'b', 5), ('b', 'a', 5)]]
    Formato resultado: {'a': 10, 'b': 5, 'c': 0}
    (Nodos que no son claves significa que no hay camino a ellos)
    """
    vertices = grafo[0]
    aristas = grafo[1]
    if vertice not in vertices:
        print("El vertice no se encuentra en el grafo.")
        return {}

    dicResultado = dict.fromkeys(vertices)
    verticesVisitados = list()
    verticesVisitados.append(vertice)
    dicResultado[vertice] = 0

    pesoAcumulado = 0
    bandera = 1
    while set(verticesVisitados) != set(vertices) and bandera:
        verticesPotenciales = []
        contador = 0
        for arista in aristas:
            if (arista[0] == vertice and arista[1] not in verticesVisitados) or (arista[1] == vertice and arista[0] not in verticesVisitados):
                contador +=1
                x = 0
                if arista[0] == vertice:
                    x = 1
                if verticesPotenciales == []:
                    menorPeso = arista[2]
                    verMenorPeso = arista[x]
                else:
                    if arista[2] < menorPeso:
                        menorPeso = arista[2]
                        verMenorPeso = arista[x]
                verticesPotenciales.append(arista[x])
                peso = arista[2] + pesoAcumulado
                if dicResultado[arista[x]] == None:
                    dicResultado[arista[x]] = peso
                else:
                    if dicResultado[arista[x]] > peso:
                        dicResultado[arista[x]] = peso
        if contador == 0:
            for x in vertices:
                if dicResultado[x] == None:
                    dicResultado.pop(x)
            bandera = 0
        if bandera:
            vertice = verMenorPeso
            dicResultado[vertice] = menorPeso + pesoAcumulado
            pesoAcumulado += menorPeso
            verticesVisitados.append(vertice)
    return dicResultado

def dijkstra_2(grafo, vertice):
    """
    Dado un grafo (en formato de listas con pesos), aplica el algoritmo de
    Dijkstra para hallar el CAMINO mas corto desde el vertice de origen
    a cada uno del resto de los vertices.
    Formato resultado: {'a': ['a'], 'b': ['a', 'b'], 'c': ['a', 'b', 'c']}
    (Nodos que no son claves significa que no hay camino a ellos)
    """
    vertices = grafo[0]
    aristas = grafo[1]
    if vertice not in vertices:
        print("El vertice no se encuentra en el grafo.")
        return {}

    dicResultado = dict()
    for x in vertices:
        dicResultado[x] = []
    verticesVisitados = list()
    verticesVisitados.append(vertice)
    dicResultado[vertice] = [[vertice], 0]

    pesoAcumulado = 0
    bandera = 1
    while set(verticesVisitados) != set(vertices) and bandera:
        verticesPotenciales = []
        contador = 0
        for arista in aristas:
            if (arista[0] == vertice and arista[1] not in verticesVisitados) or (arista[1] == vertice and arista[0] not in verticesVisitados):
                contador +=1
                x = 0
                if arista[0] == vertice:
                    x = 1
                if verticesPotenciales == []:
                    menorPeso = arista[2]
                    verMenorPeso = arista[x]
                else:
                    if arista[2] < menorPeso:
                        menorPeso = arista[2]
                        verMenorPeso = arista[x]
                verticesPotenciales.append(verMenorPeso)
                peso = pesoAcumulado + arista[2]
                if dicResultado[arista[x]] == []:
                    dicResultado[arista[x]] = [[vertice, verMenorPeso], peso]
                else:
                    lista = dicResultado[verMenorPeso]
                    if lista[1] > peso:
                        dicResultado[arista[x]] = [dicResultado[vertice][0]+[verMenorPeso], peso]
        if contador == 0:
            for x in vertices:
                if dicResultado[x] == []:
                    dicResultado.pop(x)
            bandera = 0
        if bandera:
            vertice = verMenorPeso
            pesoAcumulado += menorPeso
            verticesVisitados.append(vertice)
    for x in vertices:
        dicResultado[x] = dicResultado[x][0]
    return dicResultado

def main():
    # grafo1 = [['a', 'b', 'c'], [('c', 'b', 5), ('b', 'a', 5)]]
    grafo2 = [['a', 'b', 'c', 'd', 'e' ], [('a', 'b', 4), ('a', 'c', 2)
    ,('c', 'b', 1),('c', 'b', 3),('c', 'd', 4),('c', 'e', 5),('b', 'd', 2)
    ,('b', 'e', 3),('d', 'e', 1)]]
    print(dijkstra_2(grafo2, 'c'))
    dijkstra(grafo2, 'c')


if __name__ == "__main__":
    main()