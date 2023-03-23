//caso cociente incremental
//Calcula la derivada de orden n en el punto v de la funcion f, con el metodo de cociente incremental
//f es un string que representa a una funcion, v el valor en el cual se evalua la derivada, n el orden de la derivada
//y h el paso.
function derivada = derivarInc(f, v, n, h)
    deff("y=DF0(x)", "y="+f)
    if n == 0 then
        derivada = DF0(v);
    else
        for i=1:n-1
            deff("y=DF"+string(i)+"(x)", "y=(DF"+string(i-1)+"(v+"+string(h)+")-DF"+string(i-1)+"(v))/"+string(h))
        end
        deff("y=DFn(x)", "y=(DF"+string(n-1)+"(v+"+string(h)+")-DF"+string(n-1)+"(v))/"+string(h))
        derivada = DFn(v)
    end
endfunction

//caso numderivative
//Calcula la derivada de orden n en el punto v de la funcion f, con el metodo de numDerivative de scilab
//f es un string que representa a una funcion, v el valor en el cual se evalua la derivada, n el orden de la derivada
// y h el paso.
function derivada = derivarNum(f, v, n, h)
    deff("y=DF0(x)", "y="+f)
    if n == 0 then
        derivada = DF0(v);
    else
        for i=1:n-1
            deff("y=DF"+string(i)+"(x)", "y=numderivative(DF"+string(i-1)+",x,"+string(h)+",4)")
        end
        deff("y=DFN(x)", "y=numderivative(DF"+string(n-1)+",x,"+string(h)+",4)")
        derivada = DFN(v)
    end
endfunction

//Funcion que encapsula los dos metodos
//Recibe una funcion f(string), un valor v, un orden n, y un metodo.
//Si el metodo es 1 -> metodo cociente incremental
//Si el metodo es 2 -> metodo numDerivative
//Cualquier otro valor distinto a los anteriores deparara en un error.
function derivada = derivadaGen(f, v, n, h, metodo)
    if metodo == 1 then
        derivada = derivarInc(f, v, n, h)
    else
        if metodo == 2 then
            derivada = derivarNum(f, v, n, h)
        else
            derivada = 0
            printf("Metodo invalido. Este debe ser 1 o 2.\n")
        end
    end
endfunction
//Resultados obtenidos:
//derivadaGen("x^3-2*x+2", 2, 2, 0.01, 2) = 12.
//derivadaGen("x^3-2*x+2", 2, 2, 0.01, 1) = 0.
//
//derivadaGen("x^3-2*x+2", 2, 1, 0.01, 2) = 10.
//derivadaGen("x^3-2*x+2", 2, 1, 0.01, 1) = 10.0601.
//Podemos ver facilmente que en el caso de aplicar cociente
//incremental el error es mayor que el que obtenemos al 
//aplicar el caso numDerivative.
//Esto pasa ya que cuando utilizamos cociente incremental y debemos
//derivar n veces, vamos obteniendo un cociente cada vez mas grande, 
//y este va arrastrando errores hasta llegar a calcular el ultimo cociente.



