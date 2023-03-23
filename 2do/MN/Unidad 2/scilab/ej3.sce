//Funcion algoritmo de Horner
//Recibe un polinomio p y un valor x.
function suma = hornerP(p, x)
    n = degree(p)
    bn = coeff(p, n)
    for i = n-1:-1:0
        bi = coeff(p, i) + x*bn
        bn = bi
    end
    suma = bn
endfunction
//Resultados obtenidos:
//p = poly([1 2 -3 -0.02 0 214 -7.11], 'x', 'coeff')
//1+2x-3x^2-0.02x^3+214x^5-7.11x^6
//hornerP(p, -1) = -225.09
//p = poly([1 2 -3], 'x', 'coeff')
//1+2x-3x^2
//hornerP(p, -0.0314) = 0.9342421

//Funcion algoritmo de horner generalizado
//Recibe un polinomio p y un valor x
function resultados = hornerGen(p, x)
    n = degree(p)
    h2 = coeff(p, n)
    suma = h2
    for i = n-1:-1:1
        aux = coeff(p, i) + x*h2
        h2 = aux
        suma = suma + h2
    end
    h = coeff(p, 0) + x*h2
    printf("%d\n",h)
    resultados(1) = h
    resultados(2) = suma
endfunction
//Resultados obtenidos:
//p = poly([1 2 -3 -0.02 0 214 -7.11], 'x', 'coeff')
//1+2x-3x^2-0.02x^3+214x^5-7.11x^6 
//hornerGen(p, 2) = 6385.8
//                  6178.93
//hornerGen(p, -1) = -225.09
//                   215.98
