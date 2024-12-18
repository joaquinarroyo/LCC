// Joaquin Arroyo

// ----- Metodo del Trapecio Simple
// f funcion a integrar
// a limite inferior del intervalo de integracion
// b limite superior del intervalo de integracion
// Devuelve el valor de la integral aproximado y el error
function integral = trapecio_simple(f, a, b)
    h = b - a;
    integral = (h/2) * (f(a) + f(b));
endfunction

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
// trapecio_simple(f, 0, 1);
// trapecio_compuesto(f, 0, 1, 1000);


// ----- Metodo de Simpson Simple
// f funcion a integrar
// a limite inferior del intervalo de integracion
// b limite superior del intervalo de integracion
// Devuelve el valor de la integral aproximado
function integral = simpson_simple(f, a, b)
    h = (b - a) / 2;
    integral = (h/3) * (f(a) + 4 * f(a+h) + f(b));
endfunction

// ----- Metodo de Simpson Compuesto
// f funcion a integrar
// a limite inferior del intervalo de integracion
// b limite superior del intervalo de integracion
// n número de subintervalos en que se desea dividir [a,b] (par)
// Devuelve el valor de la integral aproximado
function integral = simpson_compuesto(f, a, b, n)
    h = (b - a) / n;
    integral = f(a);
    for i = 1:2:n-1
        xi = a + i * h;
        xp = a + (i + 1)*h;
        integral = integral + 4*f(xi) + 2*f(xp);
    end
    
    integral = (integral - f(b)) * (h/3);
endfunction
// deff('y = f(x)', 'y = x^2');
// simpson_simple(f, 0, 1);
// simpson_compuesto(f, 0, 1, 1000);
// intg(a,b,f) evalua la integral definida de a a b en f(t)dt
// plot3d(xx, vv, pp);


// el hecho de resolver este ejercicio definiendo nuevas funciones No
// es lo esperado y solo se hace así por motivos didácticos.
//function v=DobleTn(f,a,b,c,d,n,m)
//    h = (b-a)/n
//    deff("z=fxa(y)","z=f("+string(a)+",y)")
//    deff("z=fxb(y)","z=f("+string(b)+",y)")
//    v = Tn(fxa,c(a),d(a),m)/2+Tn(fxb,c(b),d(b),m)/2
//    for i=1:n-1
//        xi = a+i*h;
//        deff("z=fxi(y)","z=f("+string(xi)+",y)");
//        v = v + Tn(fxi,c(xi),d(xi),m);
//    end
//    v = h*v;
//endfunction
