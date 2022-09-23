# 1-2-14-4 , 2-3-4-12-3
# [["1","2","14","4"],["2","3"","4","12","3"]]
# [ [["1 ", "2 ", "14"], ["4 ", "  ", "  "]], [["2 ","3 ", "4 "], ["12", "3 ", "  "]] ]

l = [[["1 ","2 ","3 "], ["4 ","5 ","6 "], ["  ","  ","  "]], [["1 ","21","3 "], ["4 ","5 ","6 "], ["31","  ","  "]]]

def maxLen(cartas):
    x = 0
    for carta in cartas:
        if len(carta) > x:
            x = len(carta)
    return x

def imprimir(cartas, cantCartas):
    n = len(cartas[0])
    x = 0
    while x < n:
        for y in range(0, cantCartas):
            l = cartas[y][x]
            for c in l:
                print(c, end=" ")
            print("|", end =" ")
        print("")
        x += 1

imprimir(l, 2)


    
        
