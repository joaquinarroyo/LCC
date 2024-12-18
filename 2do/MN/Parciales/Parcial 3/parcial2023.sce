// Parcial 3 - 2023

// ----- Metodo del Trapecio Compuesto
// f funcion a integrar
// a limite inferior del intervalo de integracion
// b limite superior del intervalo de integracion
// n número de subintervalos en que se desea dividir [a,b]
// Devuelve el valor de la integral aproximado y el error
function integral = trapecio_compuesto(f, a, b, n)
    h = (b - a) / n;
    integral = (1/2) * (f(a) + f(b));
    for i = 1:n-1
        xi = a + i * h;
        integral = integral + f(xi);
    end
    
    integral = integral * h;
endfunction
// deff('y = f(x)', 'y = x^2');
// trapecio_compuesto(f, 0, 1, 1000);

function aprox = Si(b, n)
    deff('y = f(x)', 'y = sin(x)/x');
    aprox = trapecio_compuesto(f, 1, b, n);
endfunction

//deff('y = f(x)', 'y = sin(x)/x');
//aprox1 = Si(2, 100);
//real1 = intg(1, 2, f);
//disp(real1-aprox1)
//aprox2 = Si(5, 100);
//real2 = intg(1, 5, f);
//disp(real2-aprox2)
//aprox3 = Si(10, 100);
//real3 = intg(1, 10, f);
//disp(real3-aprox3)
//aprox4 = Si(15, 100);
//real4 = intg(1, 15, f);
//disp(real4-aprox4)

//---------------------------------------------------------------
//x = 0:10;
//y = [0.68 0.85 -0.25 -0.76 -0.46 -0.28 0.76 0.16 0.74 -0.42 -0.55];
//
//function [p,err] = MinCuad_inv(A,b)
//    a = inv((A')*A)*((A')*(b'));
//    p = poly(a,"x","coeff");
//    err = norm(A*a-(b'));
//endfunction
//
//// Matriz_MinCuad([1 2 3], list("1", "x", "x**2"))
//// Matriz genérica del método de mínimo cuadrados polinomial
//function A = Matriz_MinCuad(x, f)
//    n = length(f);
//    m = length(x);
//    A = zeros(m, n);
//    for i=1:n
//        deff('y = g(x)', 'y = '+f(i));
//        A(:,i) = (g(x))'
//    end
//endfunction
//
//function [p, err] = MinCuadrados(x, y, f)
//    A = Matriz_MinCuad(x, f);
//    d = det((A')*A);
//    
//    if d == 0 then
//        abort();
//    end
//    
//    [p, err] = MinCuad_inv(A, y);
//endfunction
//
////[p1, e1] = MinCuadrados(x, y, list("1", "x"))
////[p2, e2] = MinCuadrados(x, y, list("1", "x", "x**2"))
////[p3, e3] = MinCuadrados(x, y, list("1", "x", "x**2", "x**3"))
//////
////[g1, e4] = MinCuadrados(x, y, list("1", "cos(x)", "sin(x)"))
//
//function plotInterpolacion(x, y, h, p)
//    n = length(x);
//    xx = (x(1)-0.1):h:(x(n)+0.1);
//    plot2d(x,y,-1);
//    
//    for i = 1:length(p)
//        plot2d(xx,horner(p(i),xx'),i+1)
//    end
//    
//    legend("puntos", "p1", "p2", "p3", "g1")
//endfunction
//
////plotInterpolacion(x, y, 0.01, [p1, p2, p3, g1])

//----------------------------------------------------------------------------------------------
//deff('y = f1(x)', 'y = x^2+1');
//deff('y = f2(x)', 'y = x+3');
//xx = -1:0.1:2;
//plot2d(xx,f2(xx),3);
//plot2d(xx,-1*f2(xx),3);

//deff('y = f1(x)', 'y = (x^2+1)^2');
//deff('y = f2(x)', 'y = (x+3)^2');
//real1 = %pi * intg(-1, 2, f1);
//real2 = %pi * intg(-1, 2, f2);
//aprox1 = %pi * trapecio_compuesto(f1, -1, 2, 1100);
//aprox2 = %pi * trapecio_compuesto(f2, -1, 2, 400);
//disp(real1 - aprox1)
//disp(real2 - aprox2)

//--------------------------------------------------------------------------------------------
x = 0:30
y = [35, 23, 47, 59, 82, 113, 143, 179, 233, 269, 303, 335, 371, 404, 434, 446, 457, 470, 481, 482, 476, 465, 454, 436, 424, 397, 385, 359, 340, 322, 303]

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

// Redefino MinCuadrados usando a+b*cos(x)+c*sin(x)
function [p, err] = MinCuadrados(x, y, f)
    A = Matriz_MinCuad(x, f);
    d = det((A')*A);
    
    if d == 0 then
        abort();
    end
    
    [a, err] = coeff_inv(A, y);
    a(1) = log(-a(1));
    a(2) = -a(2);
    p = poly(a,"x","coeff");
//    deff("y = p(k)", "y = "+string(a(1))+" + "+string(a(2))+"*k");
endfunction

b = log(y);
[g, err] = MinCuadrados(x, b, list("1", "x"))

function plotInterpolacion(x, y, h, p)
    n = length(x);
    xx = (x(1)-0.1):h:(x(n)+0.1);
    plot2d(x,y,-1);
    
    plot2d(xx,horner(p, xx'),2)
    legend("puntos", "g")
endfunction

plotInterpolacion(x, y, 0.1, g)
