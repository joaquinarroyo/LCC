function result = derivar(f, v, n, h)
    // Inicialización del valor de la derivada
    result = 0;
    
    // Calculo del valor de la derivada de orden n usando el cociente incremental
    for k = 0:n
        result = result + ((-1)^k * factorial(n) / (factorial(k) * factorial(n - k))) * f(v + (n - k) * h);
    end
    
    // División final por h^n
    result = result / (h^n);
endfunction

deff('y = f(x)', 'y = x^2');  // Definimos la función f(x) = x^2
v = 2;  // Punto donde queremos evaluar la derivada
n = 1;  // Orden de la derivada
h = 0.001;  // Paso

resultado = derivar(f, v, n, h);
disp(resultado);  // Muestra el resultado de la derivada

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
function result = derivar_numderivative(f, v, n, h)
    // Calculo de la derivada usando numderivative
    result = numderivative(f, v, h, n);
endfunction

deff('y = f(x)', 'y = x^2');  // Definimos la función f(x) = x^2
v = 2;  // Punto donde queremos evaluar la derivada
n = 1;  // Orden de la derivada
h = 0.001;  // Paso

resultado = derivar_numderivative(f, v, n, h);
disp(resultado);  // Muestra el resultado de la derivada