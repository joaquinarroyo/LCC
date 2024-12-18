// Parcial 2022 - 1
//Ej 1
x = 1:10;
y1 = [32.9 30.8 26.4 24.2 19.2 16.5 19.3 21 23 26.2];
y2 = [19.5 15.5 13.1 9.8 5.7 2.2 5.3 4.7 6 10.5];
y = (y1 + y2) / 2;

function p = MinCuad_inv(A,b)
    a = inv((A')*A)*((A')*(b'));
    p = poly(a,"x","coeff");
    err = norm(A*a-(b'));
    disp(err);
endfunction

function p = MinCuad_qr(A,b)
    [Q, R] = qr(A, "e");
    a = inv(R)*(Q')*(b');
    p = poly(a,"x","coeff");
    err = norm(A*a-(b'));
    disp(err);
endfunction

function A = Vandermonde(x,grado)
    m = length(x);
    A = ones(m,1);
    for j=1:grado
        A = [A, (x').^j];
    end
endfunction

function p = MinCuadrados(x, y, grado)
    A = Vandermonde(x, grado);
    d = det((A')*A);
    
    if d == 0 then
        abort();
    end
    
    p = MinCuad_inv(A, y);
endfunction

function plotInterpolacion(x, y, h, p)
    n = length(x);
    xx = (x(1)-0.1):h:(x(n)+0.1);
    plot2d(x,y,-1);
    
    for i = 1:length(p)
        plot2d(xx,horner(p(i),xx'),i+1)
    end
    
    legend("puntos", "p3", "p5", "p7", "p9")
endfunction

// item a y b) cambiar en MinCuadrados el método de MinCuad a utilizar (mediante inversa o qr)
//p1 = MinCuadrados(x, y, 3);
//p2 = MinCuadrados(x, y, 5);
//p3 = MinCuadrados(x, y, 7);
//p4 = MinCuadrados(x, y, 9);
//plotInterpolacion(x, y, 0.1, [p1 p2 p3 p4])


// Ej2
function integral = trapecio_compuesto(f, a, b, n)
    if argn(2) < 4 then
        n = 1;
    end
    
    h = (b - a) / n;
    integral = (h/2) * (f(a) + f(b));
    
    for i = 1:n
        xi = a + i * h;
        integral = integral + f(xi);
    end
    
    integral = integral * h;
endfunction
deff('y = f(x)', 'y = 1/x');
disp(trapecio_compuesto(f, 1, 2, 500));
