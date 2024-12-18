
function A = make_matrix(c, n)
    A = zeros(n, n)
    for i = 1:n
        for j = 1:n
            if i == j then
                A(i, j) = 1+2*c
            elseif abs(i - j) == 1 then
                A(i, j) = -c
            end 
        end
    end
endfunction

function [P, L, U] = gaussLU(A)
    [n, m] = size(A);
    P = eye(n,n);
    L = eye(n,n);
    
    if n ~= m then
        error('gaussLU - A no cuadrada');
        abort;
    end;

    // for every pivot element
    for k = 1:n-1
        // find max elem at or below pivot and swap files if bigger (pivot)
        [mval, mpos] = max(abs(A(k:n,k)));
        mpos = mpos + (k-1); // ajustar mpos ya que max retorna índice para submatriz
        if(mval > A(k,k)) then
            A([k mpos],:) = A([mpos k],:);
            P([k mpos],:) = P([mpos k],:);
            L([k mpos],1:k-1) = L([mpos k],1:k-1);
        end;
        
        // for every row below it
        for i = k+1:n
            // operate over every column item from pivot onwards if first item is not zero
            if(A(i,k) ~= 0) then
                mult = A(i, k) / A(k, k);
                A(i, k:n) = A(i, k:n) - (A(k, k:n) * mult);
                L(i, k) = mult;
            end;
        end;
    end;
    
    U = A
endfunction

function x = resolucionLU(P, L, U, b)
    Pb = P * b;
    y = sustProgresiva([L, Pb]);
    x = sustRegresiva([U, y]);
endfunction

function ej1()
    c = 1;
    n = 5;
    A = make_matrix(c, n);
    [P, L, U] = gaussLU(A);
    disp("Matriz L: ");
    disp(L);
    disp("Matriz U: ");
    disp(U);
    xi = [10 12 12 12 10]'
    for i = 1:4
        xi = resolucionLU(P, L, U, xi)
        disp("Solucion x" + string(i) + " = ");
        disp(xi');
    end
endfunction

function rho = spectral_radius(A)
    rho = max(abs(spec(A)));
endfunction

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

function M = matriz_jacobi(A)
    [n, m] = size(A);
    if n <> m then
        error("La matriz no es cuadrada.");
        abort;
    end
    
    I = eye(n, n);
    invD = diag(1 ./ diag(A));
    
    M = I-(invD*A); // I - (D^-1 * A)
endfunction

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

function ej2()
    A = [10 -1 2 0 ; -1 11 -1 3 ; 2 -1 10 -1 ; 0 3 -1 8];
    M1 = matriz_gauss_seidel(A);
    M2 = matriz_jacobi(A);
    rho1 = spectral_radius(M1);
    rho2 = spectral_radius(M2);
    disp(rho1);
    disp(rho2);
    x0 = [0 0 0 0]';
    b = [6 25 -11 15]';
    eps = 10**(-5);
    maxiter = 1000;
    x1 = gauss_seidel(A, b, x0, eps, maxiter);
    disp("Solucion Gauss Seidel")
    disp(x1')
    x2 = jacobi(A, b, x0, eps, maxiter);
    disp("Solucion Jacobi")
    disp(x2')
endfunction

function [U, ind] = choleskyU(A, eps)
    if argn(2) < 2 then
        eps = 1.0e-8;
    end

    n = size(A, 1);
    U = zeros(n, n);
    ind = 1;

    for k = 1:n
        if k == 1 then
            t = A(k, k);
        else
            U_slice = U(1:k-1, k);
            t = A(k, k) - U_slice' * U_slice;
        end

        if t <= eps then
            disp("choleskyU - Matriz no es positiva definida.");
            ind = 0;
            return;
        end

        U(k, k) = sqrt(t);

        for j = k+1:n
            if k == 1 then
                U(k, j) = A(k, j) / U(k, k);
            else
                U_slice = U(1:k-1, j);
                U(k, j) = (A(k, j) - U_slice' * U_slice) / U(k, k);
            end
        end
    end
endfunction

function x = cholesky(A, b)
    [U, ind] = choleskyU(A);
    x = sustRegresiva([U, sustProgresiva([U', b])]);
endfunction

function ej3()
    a = [0.2 0.2 0.2 0.2 0.2];
    A1 = [1 a ; a' eye(5, 5)];
    A2 = [eye(5, 5) a' ; a 1];
    [U1, ind1] = choleskyU(A1);
    [U2, ind2] = choleskyU(A2);
    disp(A1)
    disp(U1' * U1)
endfunction
