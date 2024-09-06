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

function result = taylor(f, a, n, x)
    // Inicialización del polinomio de Taylor
    result = 0;
    h = 0.001;  // Paso para el cálculo de las derivadas
    
    // Calculo de cada término del polinomio de Taylor
    for k = 0:n
        // Calculo de la k-ésima derivada en el punto 'a' usando numderivative
        derivada_k = derivar(f, a, k, h);
        
        // Calculo del término k del polinomio de Taylor
        term = derivada_k / factorial(k) * (x - a)^k;
        
        // Suma del término al resultado
        result = result + term;
    end
endfunction

// Definimos la función f(x) = e^x
deff('y = f(x)', 'y = exp(x)');

// Definimos el punto de expansión, el grado del polinomio y el punto de evaluación
a = 0;  // Punto de expansión
n = 3;  // Grado del polinomio de Taylor
x = 1;  // Punto donde se evaluará el polinomio de Taylor

// Calculamos el polinomio de Taylor
resultado = taylor(f, a, n, x);
disp(resultado);  // Muestra el resultado