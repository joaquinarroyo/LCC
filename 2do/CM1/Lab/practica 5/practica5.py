# 5ta Practica Laboratorio 
# Complementos Matematicos I
# Consigna: Implementar los siguientes metodos
from math import inf as INF

def menorPosibleP(lista, conjunto):
    aux = list(conjunto)
    posVal = INF
    res = None
    for x in aux:
        if not (x[0] in lista and x[1] in lista):
            if x[2] <= posVal:
                posVal = x[2]
                res = x
    return res


def prim(grafo):
    """
    Dado un grafo (en formato de listas con pesos), aplica el algoritmo de Prim
    y retorna el MST correspondiente.
    NOTA: El grafo de entrada se asume conexo.
    """
    visitados = []
    camino = []
    aristasARecorrer = set()
    actual = grafo[0][0]
    visitados.append(actual)
    while set(visitados) != set(grafo[0]):
        for x in grafo[1]:
            if x[0] == actual or x[1] == actual:
                aristasARecorrer.add(x)
        menorArista = menorPosibleP(visitados, aristasARecorrer)
        if visitados[-1] == menorArista[1]:
            camino.append((menorArista[1],menorArista[0]))
        else:
            camino.append((menorArista[0],menorArista[1]))
        if menorArista[0] in visitados:
            actual = menorArista[1]
            visitados.append(actual)
        else:
            actual = menorArista[0]
            visitados.append(actual)
    return camino
        


def kruskal(grafo):
    """
    Dado un grafo (en formato de listas con pesos), aplica el algoritmo de
    Kruskal y retorna el MST correspondiente (o un bosque, en el caso de que
    no sea conexo).
    """
    ordenSegunPeso = sorted(grafo[1], key=lambda tup: tup[2])
    conjuntos = []
    final = []
    for x in grafo[0]:
        conjuntos.append({x})
    for x,y,z in ordenSegunPeso:
        bandera = True
        for i in range(len(conjuntos)):
            if (x in conjuntos[i] and y in conjuntos[i]):
                bandera = False
        if bandera:
            conjuntoUno = None
            conjuntoDos = None
            for j in conjuntos:
                if x in j:
                    conjuntoUno = j
                elif y in j:
                    conjuntoDos = j
            agregar = conjuntoUno | conjuntoDos
            conjuntos.remove(conjuntoUno)
            conjuntos.remove(conjuntoDos)
            conjuntos.append(agregar)
            final.append((x,y))
                    
    return final


def main():
    grafoCreado = (['A', 'B', 'C', 'D', 'E'], [('A', 'B', 4), ('A', 'C', 2), ('B', 'C', 1), ('B', 'D', 2), ('B', 'E', 3), ('D', 'C', 4), ('C', 'E', 5), ('D', 'E', 1)])
    grafoCreado2 = (['A', 'B', 'C', 'D', 'E', 'F', 'G', 'H'], [('A', 'B', 4), ('A', 'C', 2), ('B', 'C', 1), ('B', 'D', 2), ('B', 'E', 3), ('D', 'C', 4), ('C', 'E', 5), ('D', 'E', 1), ('F','G',2),('G','H',5),('F','H',3)])
    print(prim(grafoCreado))
    print(kruskal(grafoCreado2))


if __name__ == "__main__":
    main()