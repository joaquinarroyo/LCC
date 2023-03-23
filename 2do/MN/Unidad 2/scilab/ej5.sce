//Funcion derivar, metodo numderivative(Ej 4)
function derivada = derivar(f, v, n, h)
    deff("y=DF0(x)", "y="+f)
    if n == 0 then
        derivada = DF0(v);
    else
        for i=1:(n-1)
            deff("y=DF"+string(i)+"(x)", "y=numderivative(DF"+string(i-1)+",x,"+string(h)+",4)")
        end
        deff("y=DFN(x)", "y=numderivative(DF"+string(n-1)+",x,"+string(h)+",4)")
        derivada = DFN(v)
    end
endfunction

//Calcula el valor de f(v) aproximandolo por su polinomio de taylor, donde calcula
//las n derivadas a traves del metodo numderivative del ejercicio 4.
//f es un string que representa a la funcion, v un valor y n el grado del polinomio de taylor
function resultado = taylor(f, v, n)
    resultado = derivar(f, 0, 0, 000.1)
    for i=1:n-1
        resultado = resultado + (derivar(f, 0, i, 000.1)/factorial(i))*((v)^(i))
    end
endfunction
//Resultados obtenidos:
//taylor("(x^2-2)/3*x", 2, 1) = 0
//taylor("(x^2-2)/3*x", 2, 2) = -1.33333
//taylor("(x^2-2)/3*x", 2, 3) = -1.33333
//taylor("(x^2-2)/3*x", 2, 4) = 1.33333

