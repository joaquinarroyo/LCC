// Francisco Bolzan

// Calculo de coeficientes mediante gauss
// A matriz a usar en el metodo mincuadrados
// b vector de resultados
function [a,err] = coeff_gauss(A,b)
    a = gaussElim((A')*A,(A')*(b'));
    err = norm(A*a-(b'));
endfunction

// Calculo de coeficientes mediante inversa
// A matriz a usar en el metodo mincuadrados
// b vector de resultados
function [a,err] = coeff_inv(A,b)
    a = inv((A')*A)*((A')*(b'));
    err = norm(A*a-(b'));
endfunction

// Calculo de coeficientes mediante QR
// A matriz a usar en el metodo mincuadrados
// b vector de resultados
function [a,err] = coeff_qr(A,b)
    [Q, R] = qr(A, "e");
    a = inv(R)*(Q')*(b');
    err = norm(A*a-(b'));
endfunction

// Matriz de Vandermonde - Version generica en Matriz_MinCuad
// vector de valores x
// grado del polinomio
//function A = Vandermonde(x,grado)
//    m = length(x)
//    A = ones(m,1)
//    for j=1:grado
//        A = [A, (x').^j]
//    end
//endfunction

// Matriz genérica
// x vector de valores x
// lista de funciones en formato list("1", "x", "x**2")
function A = Matriz_MinCuad(x, f)
    n = length(f);
    m = length(x);
    A = zeros(m, n);
    for i=1:n
        deff('y = g(x)', 'y = '+f(i));
        A(:,i) = (g(x))'
    end
endfunction

// Combina métodos anteriores a eleccion
// x vector de valores x
// y vector de valores y
// f lista de funciones en formato list("1", "x", "x**2")
function [p, err] = MinCuadrados(x, y, f)
    A = Matriz_MinCuad(x, f);
    d = det((A')*A);
    
    if d == 0 then
        abort();
    end
    
    [a, err] = coeff_inv(A, y);
    p = poly(a,"x","coeff"); // cambiar en caso de usar funciones no polinomiales
endfunction

// ----- Eliminación Gaussiana
// A matriz de coeficientes
// b vector de variables
// Devuelve vector x de soluciones
function x = gaussElim(A, b)
    [nA, mA] = size(A);
    [nb, mb] = size(b);
    if nA ~= mA || mA ~= nb then
        error('elimProgresiva - A no cuadrada o distinta de b');
        abort;
    end;
    
    a = [A, b];
    n = nA;
    for k = 1:n-1
        [mval, mpos] = max(abs(a(k:n,k)));
        mpos = mpos + (k-1); // ajustar mpos ya que max retorna índice para submatriz
        if(mval > a(k,k)) then
            a([k mpos],:) = a([mpos k],:);
        end;
        for i = k+1:n
            if(a(i,k) ~= 0) then
                a(i, k:n+mb) = a(i, k:n+mb) - (a(k, k:n+mb) * a(i, k) / a(k, k));
            end;
        end;
    end;
    
    [n, m] = size(a);
    mb = m - n;  // numero de columnas b
    if n > m then
        error('sustRegresiva - Dimensiones inválidas para matriz aumentada');
        return;
    end;
    x = zeros(n, mb);
    for cb = 1:mb
        x(n, cb) = a(n, n+cb) / a(n, n);
        for i = n-1:-1:1
            x(i, cb) = (a(i, n+cb) - a(i, i+1:n) * x(i+1:n, cb)) / a(i, i);
        end
    end
endfunction

// Funcion de ploteo de puntos e interpolaciones
// x vector de valores x
// y vector de valores y
// h paso
// p array de polinomios
function plotInterpolacion(x, y, h, p)
    n = length(x);
    xx = (x(1)-0.1):h:(x(n)+0.1);
    plot2d(x,y,-1);
    
    for i = 1:length(p)
        plot2d(xx,horner(p(i),xx'),i+1)
    end
    
    legend("puntos", "p3", "p5", "p7", "p9")
endfunction

// - Ejercicio 8 - //
//x=[4,4.2,4.5,4.7,5.1,5.5,5.9,6.3,6.8,7.1]
//y=[102.56,113.18,130.11,142.05,167.53,195.14,224.87,256.73,299.5,326.72]
//
//[p1,err1] = MinCuadrados(x,y,list("1","x"));
//[p2,err2] = MinCuadrados(x,y,list("1","x","x**2"));
//[p3,err3] = MinCuadrados(x,y,list("1","x","x**2","x**3"));
//
//xx=4:0.001:7.2
//plot2d(x,y,-1)
//plot2d(xx,[horner(p1,xx'),horner(p2,xx'),horner(p3,xx')],[2,3,4],leg="p1(x)@p2(x)@p3(x)")
//a = gca();
//a.x_location = "origin";
//a.y_location = "origin";
