x = 0:10;
y = [0.68 0.85 -0.25 -0.76 -0.46 -0.28 0.76 0.16 0.74 -0.42 -0.55];

// Calculo de coeficientes mediante inversa
// A matriz a usar en el metodo mincuadrados
// b vector de resultados
function [a,err] = coeff_inv(A,b)
    a = inv((A')*A)*((A')*(b'));
    err = norm(A*a-(b'));
endfunction

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


[p1, e1] = MinCuadrados(x, y, list("1", "x"))
[p2, e2] = MinCuadrados(x, y, list("1", "x", "x**2"))
[p3, e3] = MinCuadrados(x, y, list("1", "x", "x**2", "x**3"))

// Redefino MinCuadrados usando a+b*cos(x)+c*sin(x)
function [p, err] = MinCuadrados(x, y, f)
    A = Matriz_MinCuad(x, f);
    d = det((A')*A);
    
    if d == 0 then
        abort();
    end
    
    [a, err] = coeff_inv(A, y);
    deff("y = p(k)", "y = "+string(a(1))+" + "+string(a(2))+"*cos(k) + "+string(a(3))+"*sin(k)");
endfunction

[g1, e4] = MinCuadrados(x, y, list("1", "cos(x)", "sin(x)"))

function plotInterpolacion(x, y, h, p)
    n = length(x);
    np = length(p);
    xx = (x(1)-0.1):h:(x(n)+0.1);
    plot2d(x,y,-1);
    
    for i = 1:np-1
        plot2d(xx,horner(p(i),xx'),i+1)
    end
    plot2d(xx, p(np)(xx), np+1)
    legend("puntos", "p1", "p2", "p3", "g1")
endfunction

plotInterpolacion(x, y, 0.01, list(p1, p2, p3, g1))
