#! /usr/bin/python

# 2da Practica Laboratorio 
# Complementos Matematicos I
# Consigna: Implementar los siguientes metodos

# Un disjointSet lo representaremos como un diccionario. 
# Ejemplo: {'A':1, 'B':2, 'C':1} (Nodos A y C pertenecen al conjunto 
# identificado con 1, B al identificado on 2)

grafo_lista =  (['A','B','C','D','E','F','G'],[('A','B'),('B','C'),('F','G')])

def make_set(lista):
    '''
    Inicializa una lista de vértices de modo que cada uno de sus elementos pasen a ser conjuntos unitarios. 
    Retorna un disjointSet.
    '''
    n = 1
    disjoint_set = {}
    for x in lista:
        disjoint_set[x] = n
        n+=1
    return disjoint_set


def find(elem, disjoint_set):
    '''
    Obtiene el identificador del conjunto de vértices al que pertenece el elemento.
    '''
    return disjoint_set.get(elem)


def union(id_1, id_2, disjoint_set):
    '''
    Dado dos identificadores de conjuntos de vértices, une dichos conjuntos.
    Retorna la estructura actualizada
    '''
    value = 0
    if id_1 < id_2:
        value = id_1
    else:
        value = id_2
    key_list = list(disjoint_set.keys())
    val_list = list(disjoint_set.values())
    disjoint_set[key_list[val_list.index(id_1)]] = value
    disjoint_set[key_list[val_list.index(id_1)]] = value
    for x in disjoint_set:
        if find(x, disjoint_set) > value:
            disjoint_set[x] -= 1
    return disjoint_set


def componentes_conexas(grafo_lista):
    '''
    Dado un grafo en representacion de lista, obtiene sus componentes conexas.
    Ejemplo:
        Entrada: [['a','b','c','d'], [('a', 'b')]]  
        Salida: [['a, 'b'], ['c'], ['d']]
    '''
    disjoint_set = make_set(grafo_lista[0])
    listaAristas = grafo_lista[1]
    for x in listaAristas:
        id_1 = find(x[0], disjoint_set)
        id_2 = find(x[1], disjoint_set)
        disjoint_set = union(id_1, id_2, disjoint_set)
    listaConexa = list()
    mayor = dic_mayor(disjoint_set)
    index = 1
    while(index < mayor+1):
        listaConexa.append([])
        index+=1
    index = 1
    for x in disjoint_set:
        if(index == disjoint_set[x]):
            listaConexa[index-1].append(x)
        else:   
            index +=1
            listaConexa[index-1].append(x)
    return listaConexa

def dic_mayor(disjoint_set):
    mayor = 1
    for x in disjoint_set:
        key = find(x, disjoint_set)
        if(key > mayor):
            mayor = key
    return mayor

def main():
    print(componentes_conexas(grafo_lista))

if __name__ == '__main__':
    main()