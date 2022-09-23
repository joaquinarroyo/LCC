#! /usr/bin/python

# 1ra Practica Laboratorio 
# Complementos Matematicos I
# Consigna: Implementar los siguientes metodos
import sys

def lee_grafo_stdin():
    '''
    Lee un grafo desde entrada estandar y devuelve su representacion como lista.
    Ejemplo Entrada: 
        3
        A
        B
        C
        A B
        B C
        C B
    Ejemplo retorno: 
        (['A','B','C'],[('A','B'),('B','C'),('C','B')])
    '''
    listaVertices = list()
    listaAristas = list()
    vertices = int(input())
    x = 0
    while(x < vertices):
        listaVertices.append(input())
        x+=1
    arista = ' '
    while(arista != ''):
        arista = input()
        if(arista not in listaAristas and arista != ''):
            listaAristas.append(tuple(arista.split(' ')))
    return (listaVertices, listaAristas)

def lee_grafo_archivo(file_path):
    '''
    Lee un grafo desde un archivo y devuelve su representacion como lista.
    Ejemplo Entrada: 
        3
        A
        B
        C
        A B
        B C
        C B
    Ejemplo retorno: 
        (['A','B','C'],[('A','B'),('B','C'),('C','B')])
    '''
    with open(file_path, 'r') as f:
        lineas = f.readlines()
        datos = list()
        for x in lineas:
            datos.append(x.rstrip('\n'))
    vertices = int(datos[0])
    listaVertices = list()
    listaAristas = list()
    del(datos[0])
    for x in range(0, vertices):
        listaVertices.append(datos[x])
    for x in range(vertices, len(datos)):
        listaAristas.append(tuple(datos[x].split(' ')))
    return (listaVertices, listaAristas)

def imprime_grafo_lista(grafo):
    '''
    Muestra por pantalla un grafo. El argumento esta en formato de lista.
    '''
    vertices = len(grafo[0])
    aristas = len(grafo[1])
    for x in range(0,vertices):
        print(grafo[0][x])
    for x in range(0, aristas):
        print(grafo[1][x][0], grafo[1][x][1])


def lista_a_incidencia(grafo_lista):
    '''
    Transforma un grafo representado por listas a su representacion 
    en matriz de incidencia.
    '''
    vertices = len(grafo_lista[0])
    listaVertices = grafo_lista[0]
    listaAristas = grafo_lista[1]
    listaIncidencia = list()
    for x in listaAristas:
        arista = [0]*vertices
        for y in range(0, len(listaVertices)):
            if(x[0] == listaVertices[y]):
                arista[y] = 1
            if(x[1] == listaVertices[y]):
                arista[y] = 1
        listaIncidencia.append(tuple(arista))
    
    return (listaVertices, listaIncidencia)


def incidencia_a_lista(grafo_incidencia):
    '''
    Transforma un grafo representado una matriz de incidencia a su 
    representacion por listas.
    '''
    vertices = len(grafo_incidencia[0])
    listaVertices = grafo_incidencia[0]
    listaIncidencia = grafo_incidencia[1]
    listaAristas = list()
    for x in listaIncidencia:
        arista = [None]*2
        z = 0
        for y in range(0, vertices):
            if(x[y] == 1):
                arista[z] = listaVertices[y]
                z+=1
        listaAristas.append(tuple(arista)) 
    return (listaVertices, listaAristas)


def imprime_grafo_incidencia(grafo_incidencia):
    '''
    Muestra por pantalla un grafo. 
    El argumento esta en formato de matriz de incidencia.
    '''
    listaVertices = grafo_incidencia[0]
    listaIncidencia = grafo_incidencia[1]
    print(' ', end='')
    for x in range(0, len(listaVertices)):
        if(x != len(listaVertices)-1):
            print(listaVertices[x], end='  ')
        else:
            print(listaVertices[x])
    for x in listaIncidencia:
        print(x)


def lista_a_adyacencia(grafo_lista):
    '''
    Transforma un grafo representado por listas a su representacion 
    en matriz de adyacencia.
    '''
    vertices = len(grafo_lista[0])
    listaVertices = grafo_lista[0] 
    listaAristas = grafo_lista[1]
    listaAdyacencia = list()
    verticesMarcados2 = list()
    for x in range(0, vertices):
        comparador = listaVertices[x]
        verticesMarcados = list()
        for y in listaAristas:
            if(y[0] == comparador or y[1] == comparador):
                if(y[0] == comparador):
                    verticesMarcados.append(y[1])
                else: 
                    verticesMarcados.append(y[0])
        verticesMarcados2.append(verticesMarcados)
        verticesMarcados = None
    verticesMarcados = verticesMarcados2
    listaIndex = list()
    for x in range(0, len(verticesMarcados)):
        lista = [0]*vertices
        for y in verticesMarcados[x]:
            contador = 0
            while(y != listaVertices[contador]):
                contador+=1
            if(y == listaVertices[contador]):
                lista[contador] = 1
        listaIndex.append(lista)
    listaAdyacencia = listaIndex
    for x in range(0, len(listaAdyacencia)):
        listaAdyacencia[x] = tuple(listaAdyacencia[x])
    return (listaVertices, listaAdyacencia)

def adyacencia_a_lista(grafo_adyacencia):
    '''
    Transforma un grafo representado una matriz de adyacencia a su 
    representacion por listas.
    '''

    listaVertices = grafo_adyacencia[0]
    listaAdyacencia = grafo_adyacencia[1]
    listaAristas = list()
    for x in range(0, len(listaAdyacencia)):
        marcador = listaVertices[x]
        lista = list()
        for y in range(0, len(listaAdyacencia[x])):
            if(listaAdyacencia[x][y] == 1):
                arista = [marcador, listaVertices[y]]
                arista = sorted(arista)
                lista.append(arista)
        for z in lista:
            listaAristas.append(z)
    listaAristas2 = list()
    for x in listaAristas:
        if x not in listaAristas2:
            listaAristas2.append(x)
    listaAristas = listaAristas2
    return (listaVertices, listaAristas)


def imprime_grafo_adyacencia(grafo_adyacencia):
    '''
    Muestra por pantalla un grafo. 
    El argumento esta en formato de matriz de adyacencia.
    '''
    listaVertices = grafo_adyacencia[0]
    listaAdyacencia = grafo_adyacencia[1]
    print('  ', end='')
    for x in range(0, len(listaVertices)):
        if(x != len(listaVertices)-1):
            print(listaVertices[x], end='  ')
        else:
            print(listaVertices[x])
    contador = 0
    for x in listaAdyacencia:
        print(listaVertices[contador], end='')
        print(x)
        contador +=1


#################### FIN EJERCICIO PRACTICA ####################
grafo_adyacencia1 = (
    ['A', 'B', 'C', 'D'], 
    [[0, 1, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0],]
)

grafo_adyacencia2 = (
    ['A', 'B', 'C', 'D'], 
    [[0, 2, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0],]
)

# import sys
def lee_entrada_0():
	count = 0
	for line in sys.stdin:
		count = count + 1
		print ('Linea: [{0}]'.format(line.strip()))
	print ('leidas {0} lineas'.format(count))

	
def lee_entrada_1():
	count = 0
	try:
		while True:
			line = input().strip()
			count = count + 1
			print ('Linea: [{0}]'.format(line))
	except EOFError:
		pass
	
	print ('leidas {0} lineas'.format(count))
   

def lee_archivo(file_path):
	print('leyendo archivo: {0}'.format(file_path))
	count = 0

	with open(file_path, 'r') as f:
		first_line = f.readline()
		print ('primer linea: [{}]'.format(first_line))
		for line in f:
			count = count + 1
			print ('Linea: [{0}]'.format(line))
	print ('leidas {0} lineas'.format(count))


def main():
	#imprime_grafo_lista(lee_grafo_stdin())
    grafoLista = lee_grafo_archivo('C:\\Users\\Usuario\\Desktop\\Facultad\\Complementos\\Lab\\practica 1\\grafo.txt')
    #grafoListaInc = lista_a_incidencia(grafoLista)
    #imprime_grafo_incidencia(grafoListaInc)
    print(lista_a_adyacencia(grafoLista))
    #imprime_grafo_adyacencia(grafoListaAdy)

if __name__ == '__main__':
    main()