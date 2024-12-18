// Joaquin Arroyo

// ----- Método de la Potencia
// A matriz de numeros reales
// z0 vector estimación inicial del autovector
// eps tolerancia para diferencia en un paso
// maxiter max iteraciones
function [eigval, eigvec] = potencia(A, z0, eps, maxi)
    iter = 0;
    delta = 1;
    last = 0;
    
    while (iter < maxi) && (delta > eps)
        w = A*z0;
        z1 = w / norm(w,%inf);
        
        delta = norm(z1-z0); // Verificar si usar norma común o inifinita
        last = z0;
        z0 = z1;
        iter = iter +1;
    end
    
    eigvec = z1;
    [m,j] = max(abs(w));
    eigval = w(j) / last(j);
    
    disp("Iteraciones: " + string(iter));
endfunction

// ----- Plot Circulo
// r radio
// x coordenada
// y coordenada
function circ(r,x,y)
    xarc(x-r,y+r,2*r,2*r,0,360*64)
endfunction

// ----- Calcula Gershgorin
// A matriz
function [point, radius] = gershgorin(A)
    n = size(A, 1);
    point = diag(A);
    nonDiagA = abs(A - diag(diag(A)));
    radius = nonDiagA * ones(n, 1);
endfunction

// ----- Plotea Circulos de Gershgorin y Eigenvalues
// A matriz
// tras condicional, 1 para plotear también circulos de matriz traspuesta
function plotGershgorin(A, tras)
    [point, radius] = gershgorin(A);
    eigval = spec(A);
    
    // si no se da valor tras se asume 0
    if argn(2) < 2 then
        tras = 0;
    end
    
    scf();
    n = size(A, 1);
    for i = 1:n
        xset("color", 4);
        circ(radius(i), real(point(i)), imag(point(i)));
        if tras then
            xset("color", 2);
            circ(radius(i), -real(point(i)), imag(point(i)));
        end
    end
    
    xset("color", 0)
    plot(real(eigval), imag(eigval), '.');
    
    a = gca();
    a.x_location = "origin";
    a.y_location = "origin";
endfunction
