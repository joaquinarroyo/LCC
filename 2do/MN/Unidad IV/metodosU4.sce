// Francisco Bolzan

// ----- Eliminación Progresiva
// A matriz de coeficientes
// b vector de variables
// Devuelve matriz AUMENTADA
function a = elimProgresiva(A, b)
    [nA, mA] = size(A);
    [nb, mb] = size(b);
    
    if nA ~= mA || mA ~= nb then
        error('elimProgresiva - A no cuadrada o distinta de b');
        abort;
    end;

    a = [A, b];
    n = nA;
    // for every pivot element
    for k = 1:n-1
        // find max elem at or below pivot and swap rows if bigger (pivot)
        [mval, mpos] = max(abs(a(k:n,k)));
        mpos = mpos + (k-1); // ajustar mpos ya que max retorna índice para submatriz
        if(mval > a(k,k)) then
            a([k mpos],:) = a([mpos k],:);
        end;
        
        // for every row below it
        for i = k+1:n
            // operate over every column item from pivot onwards if first item is not zero
            if(a(i,k) ~= 0) then
                a(i, k:n+mb) = a(i, k:n+mb) - (a(k, k:n+mb) * a(i, k) / a(k, k));
            end;
        end;
    end;
endfunction

// ----- Eliminación Regresiva
// A matriz de coeficientes
// b vector de variables
// Devuelve matriz AUMENTADA
function a = elimRegresiva(A, b)
    [nA, mA] = size(A);
    [nb, mb] = size(b);
    
    if nA ~= mA || mA ~= nb then
        error('elimRegresiva - A no cuadrada o distinta de b');
        abort;
    end;

    a = [A, b];
    n = nA;
    // for every pivot element
    for k = n:-1:2
        // find max elem at or above pivot and swap rows if bigger (pivot)
        [mval, mpos] = max(abs(a(1:k,k)));
        if(mval > a(k,k)) then
            a([k mpos],:) = a([mpos k],:);
        end;
        
        // for every row above it
        for i = k-1:-1:1
            //operate over every column of extended part
            a(i, n+1:n+mb) = a(i, n+1:n+mb) - a(k, n+1:n+mb) * a(i, k) / a(k, k);
            // operate over every column item up to and including pivot
            a(i, 1:k) = a(i, 1:k) - a(k, 1:k) * a(i, k) / a(k, k);
        end;
    end;
endfunction

// ----- Sustitución Regresiva
// a matriz AUMENTADA
// Devuelve vector x de soluciones
function x = sustRegresiva(a)
    [n, m] = size(a);
    mb = m - n;  // numero de columnas b

    if n > m then
        error('sustRegresiva - Dimensiones inválidas para matriz aumentada');
        return;
    end;

    x = zeros(n, mb);
    // for every column b
    for cb = 1:mb
        x(n, cb) = a(n, n+cb) / a(n, n);
        for i = n-1:-1:1
            x(i, cb) = (a(i, n+cb) - a(i, i+1:n) * x(i+1:n, cb)) / a(i, i);
        end
    end
end


// ----- Sustitución Progresiva
// a matriz AUMENTADA
// Devuelve vector x de soluciones
function x = sustProgresiva(a)
    [n, m] = size(a);
    mb = m - n;  // numero de columnas b

    if n > m then
        error('sustProgresiva - Dimensiones inválidas para matriz aumentada');
        return;
    end;

    x = zeros(n, mb);
    // for every column b
    for cb = 1:mb
        x(1, cb) = a(1, n+cb) / a(1, 1);
        for i = 2:n
            x(i, cb) = (a(i, n+cb) - a(i, 1:i-1) * x(1:i-1, cb)) / a(i, i);
        end
    end
end

// ----- Eliminación Gaussiana
// A matriz de coeficientes
// b vector de variables
// Devuelve vector x de soluciones
function x = gaussElim(A, b)
    x = sustRegresiva(elimProgresiva(A, b));
endfunction
// A = [1 2 -2 1; 4 5 -7 6; 5 25 -15 -3; 6 -12 -6 22];


// ----- Determinante mediante elimProgresiva
// A matriz cuadrada
function d = determinante(A)
    [nA, mA] = size(A);
    
    if nA ~= mA then
        error('determinante - Matriz no cuadrada');
        abort;
    end;
    
    // genero vector zero ya que elimProgresiva está pensado  para matrices aumentadas, se podría adaptar para matrices cualquiera
    z = zeros(nA, 1);
    d = prod(diag(elimProgresiva(A,z)));
endfunction

// ----- Método factorización PA = LU
// A matriz
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
//A = [1 2 -2 1; 4 5 -7 6; 5 25 -15 -3; 6 -12 -6 22];
//[P, L, U] = gaussLU(A);
//b1 = [1; 2; 0; 1];
//b2 = [2; 2; 1; 0];
//disp(resolucionLU(P, L, U, b1));
//disp(resolucionLU(P, L, U, b2));

function [L, U] = doolittleLU(A)
    [n, m] = size(A);
    L = eye(n, n);
    U = zeros(n, n);

    if n ~= m then
        error('doolittleLU - A no cuadrada');
        abort;
    end;

    U(1,:) = A(1,:); // Inicializo la primera fila de U
    // For every diagonal element
    for i = 1:n
        // Calculo filas sobre diagonal (incluída) de U
        for k = i:n
            suma = L(i,1:i-1)*U(1:i-1,k);
            if suma == [] 
                suma = 0;
            end
            U(i,k) = A(i,k) - suma;
        end

        // Calculo columnas bajo diagonal de L
        for k = i+1:n
            suma = L(k,1:i-1)*U(1:i-1,i);
            if suma == [] 
                suma = 0;
            end
            L(k,i) = (A(k,i) - suma) / U(i,i);
        end
    end
endfunction

function x = doolittle(A, b)
    [L, U] = doolittleLU(A);
    x = sustRegresiva([U, sustProgresiva([L, b])]);
endfunction

// ----- Factorización de Cholesky
// A matriz
// eps argumento del algoritmo
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

// ----- Factorización QR
// A matriz con columnas linealmente independientes
function [Q, R] = qr_factorization(A)
    [m, n] = size(A);
    Q = zeros(m, n);
    R = zeros(n, n);

    for j = 1:n
        v = A(:, j);

        for i = 1:j-1
            R(i, j) = A(:, j)' * Q(:, i);
            v = v - R(i, j) * Q(:, i);
        end

        R(j, j) = norm(v);

        if R(j, j) ~= 0
            Q(:, j) = v / R(j, j);
        else
            Q(:, j) = zeros(m, 1);
        end
    end
endfunction

function x = solveQR(A, b)
    [Q, R] = qr_factorization(A);
    x = sustRegresiva([R, (Q'*b)]);
endfunction
