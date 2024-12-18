// Joaquin Arroyo

// ----- Jacobi
// A matriz de coeficientes
// b vector de variables
// vector valores iniciales
// epsilon para error (criterio parada)
// maxsteps máximo de pasos
function x1 = jacobi(A, b, x0, eps, maxsteps)
    [n, m] = size(A);
    if n <> m then
        error("La matriz no es cuadrada.");
        abort;
    end
    
    x1 = x0; // x1 actual, x0 previo
    cont = 0;
    delta = 1;
    invDiagA = diag(1 ./ diag(A)); // Precalculo la matriz de valores inversos de la diagonal de A
    nonDiagA = A - diag(diag(A)); // Precalculo la matriz A sin su diagonal
    
    while (delta > eps) && (cont ~= maxsteps)
        // suma(i) = A(1,1)*x0(1) + A(2,i)*x0(2) +...+ A(i,i)*x0(i) +...+ A(n,i)*x0(n)
        // donde A(i,i) = 0 por nonDiagA
        // Luego puedo operar todas las filas a la vez
        suma = nonDiagA * x0;
        
        // Calculo todo x1 a la vez
        x1 = invDiagA * (b - suma);
        
        delta = norm(x1 - x0);
        x0 = x1; // Guardo el actual como previo antes de iterar
        cont = cont + 1;
    end

    disp("Iteraciones: " + string(cont));
endfunction

// ----- Matriz de Iteración de Jacobi
// A matriz de coeficientes
function M = matriz_jacobi(A)
    [n, m] = size(A);
    if n <> m then
        error("La matriz no es cuadrada.");
        abort;
    end
    
    I = eye(n, n);
    invD = diag(1 ./ diag(A));
    
    M = I-(invD*A);
endfunction

// ----- Gauss-Seidel
// A matriz de coeficientes
// b vector de variables
// vector valores iniciales
// epsilon para error (criterio parada)
// maxsteps máximo de pasos
function x1 = gauss_seidel(A, b, x0, eps, maxsteps)
    [n, m] = size(A);
    if n <> m then
        error("La matriz no es cuadrada.");
        abort;
    end
    
    x1 = x0; // x1 actual, x0 previo
    cont = 0;
    delta = 1;
    invDiagA = 1 ./ diag(A); // Precalculo el vector de los valores inversos de la diagonal de A
    nonDiagA = A - diag(diag(A)); // Precalculo la matriz A sin su diagonal
    
    while (delta > eps) && (cont ~= maxsteps)
        // for every row
        for i = 1:n
            // suma = A(1,1)*x0(1) + A(2,i)*x0(2) +...+ A(i,i)*x0(i) +...+ A(n,i)*x0(n)
            // donde A(i,i) = 0 por nonDiagA
            suma = nonDiagA(i, :) * x1;

            // Calculo x1 por componente ya que depende del val anterior
            // val_actual(i) = elem_diag(i) * (val_res(i) - suma)
            x1(i) = invDiagA(i) * (b(i) - suma);
        end
        
        delta = norm(x1 - x0);
        x0 = x1; // Guardo el actual como previo antes de iterar
        cont = cont + 1;
    end

    disp("Iteraciones: " + string(cont));
endfunction

// ----- Matriz de Iteración de Gauss-Seidel
// A matriz de coeficientes
function M = matriz_gauss_seidel(A)
    [n, m] = size(A);
    if n <> m then
        error("La matriz no es cuadrada.");
        abort;
    end
    
    for i = 1:n
        LD(i, 1:i) = A(i, 1:i);
        LD(i, i+1:n) = zeros(1, n-i);
    end
    
    M = eye(n, n) - (inv(LD) * A); // I-((L+D)**(-1)*A)
endfunction

// ----- Cálculo del w óptimo para relajación para matrices definidas positivas y tridiagonales
// A matriz de coeficientes
function w = optimal_w(A)
    n = size(A, 1);
    I = eye(n);
    invD = diag(1 ./ diag(A));
    Tj = (I - invD * A);
    p = max(abs(spec(Tj)));
    
    w = 2 / (1 + sqrt(1 - p**2));
endfunction

// ----- Radio espectral
// A matriz
function rho = spectral_radius(A)
    rho = max(abs(spec(A)));
endfunction

// ----- Métodos de relajación
// A matriz de coeficientes
// b vector de variables
// vector valores iniciales
// epsilon para error (criterio parada)
// maxsteps máximo de pasos
// w factor de escala (1 para gauss_seidel, entre 0 y 1 para subrelajación, mayor a 1 para sobrerelajación)
function x1 = relajacion(A, b, x0, eps, maxsteps, w)
    [n, m] = size(A);
    if n <> m then
        error("La matriz no es cuadrada.");
        abort;
    end
    
    // si no se da un valor para w asume el cálculo de w óptimo
    if argn(2) < 6 then
        w = optimal_w(A);
        disp("w óptimo: " + string(w));
    end
    
    x1 = x0; // x1 actual, x0 previo
    cont = 0;
    delta = 1;
    invDiagA = w ./ diag(A); // Precalculo el vector de los valores w/A(i,i)
    nonDiagA = A - diag(diag(A)); // Precalculo la matriz A sin su diagonal
    
    while (delta > eps) && (cont ~= maxsteps)
        // for every row
        for i = 1:n
            // suma = A(1,1)*x0(1) + A(2,i)*x0(2) +...+ A(i,i)*x0(i) +...+ A(n,i)*x0(n)
            // donde A(i,i) = 0 por nonDiagA
            suma = nonDiagA(i, :) * x1;

            // Calculo x1 por componente ya que depende del val anterior
            // val_actual(i) = elem_diag(i) * (val_res(i) - suma)
            x1(i) = (1-w) * x0(i) + invDiagA(i) * (b(i) - suma);
        end
        
        delta = norm(x1 - x0);
        x0 = x1; // Guardo el actual como previo antes de iterar
        cont = cont + 1;
    end

    disp("Iteraciones: " + string(cont));
endfunction
