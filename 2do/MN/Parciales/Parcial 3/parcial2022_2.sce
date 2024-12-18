// Parcial 2022 - 2
// Ej1
function ej1()
    // item b)
    x = [0 0 1 2 2 2];
    v = [0 1 0 0 1 2];
    y = [1.42 1.85 0.78 0.18 0.60 1.05];
    
    n = length(x);
    A = [ones(n, 1), x', v'];
    a = inv((A')*A)*((A')*(y'));
    a1 = a(1);
    a2 = a(2);
    a3 = a(3);
    deff("y = p(x,v)", "y = a1+a2*x+a3*v");
    
    // item c)
    //set(gca(),"auto clear","off")
    xx = 0:0.1:2;
    vv = 0:0.1:2;
    n = length(xx);
    pp = zeros(n, n);
    for i = 1:n
        for j = 1:n
            pp(i, j) = p(xx(i), vv(j));
        end
    end
    plot3d(xx, vv, pp);
endfunction

// Ej2
function integral = simpson_compuesto(f, a, b, n)
    if argn(2) < 4 then
        n = 1;
    end
    
    h = (b - a) / n;
    x0 = a;
    x1 = a + h;
    x2 = b;
    
    integral = (h/3) * (f(x0) + 4 * f(x1) + f(x2));
    for i = 1:n
        xi = a + i * h;
        integral = integral + f(xi);
    end
    
    integral = integral * h;
endfunction

deff("y = f(x)", "y = exp(x)*sin(x)");
integ = simpson_compuesto(f, 1, 3, 15);
