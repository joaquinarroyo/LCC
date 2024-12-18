// Francisco Bolzan

// ---------- Criterios de parada
// Distancia luego de una iteración abs(x_k - x_k-1) < eps
// Distancia luego de N iteraciones abs(x_k - x_k-N) < eps
// Distancia relativa en una iteración abs(x_k - x_k-1)/abs(x_k-1) < eps
// Diferencia de valor luego de N iteraciones abs(f(x_k) - f(x_k-1)) < eps
// Proximidad a 0 abs(f(x_k)) < eps


// ---------- Aproximación de derivada evaluada en un punto (recursiva)
// f funcion
// x0 valor puntual de x
// n órden de derivación
// h paso
function der = deriv_R(f, x0, n, h)
    if n == 0 then
        der = f(x0)
    else
        der = (deriv_R(f, x0+h, n-1, h) - deriv_R(f, x0, n-1, h))/h
    end
endfunction


// ---------- Aproximación de derivada evaluada en un punto (iterativa)
// f funcion
// x0 valor puntual de x
// n órden de derivación
// h paso
function der = deriv_I(f,x0,n,h)
    deff("y=DF0(x)","y="+f)
    if n == 0 then
        der = DF0(x0)
    else
        for i=1:(n-1)
            deff("y=DF"+string(i)+"(x)","y=(DF"+string(i-1)+"(x+"+string(h)+")-DF"+string(i-1)+"(x))/"+string(h));
        end
        
        deff("y=DFn(x)","y=(DF"+string(n-1)+"(x+"+string(h)+")-DF"+string(n-1)+"(x))/"+string(h));
        der = DFn(x0);
    end
endfunction


// ---------- Método de la Bisección
// f funcion
// a, b valores de dom(f)
// err cota de error
// it máximo de iteraciones
function c = metodo_biseccion(f, a, b, err, it)
    if f(a)*f(b) < 0 then
        c = (a + b)/2
        
        while b - c > err && f(c) ~= 0 && it ~= 0
            if f(a)*f(c)<0 then 
                b = c
            else
                a = c
            end
            
            c = (a + b)/2
            it = it - 1
        end
        
        if it == 0 then
            printf("Max iteraciones alcanzado")
            r = %nan
        else
            r = c
        end
    end
endfunction


// ---------- Método de Newton
// f funcion
// x0 valor de dom(f) suficientemente cercano a raíz
// dif distancia luego de una iteración
// h paso para la derivación
// it máximo de iteraciones
function r = metodo_newton(f, x0, dif, h, it)
    fx0 = f(x0)
    x1 = x0 - fx0 * (h/(f(x0+h) - fx0))
    
    while abs(x1 - x0) >= dif && it ~= 0
        x0 = x1
        fx0 = f(x0)
        x1 = x0 - fx0 * (h/(f(x0+h) - fx0))
        it = it - 1
    end
    
    if it == 0 then
        printf("Max iteraciones alcanzado")
        r = %nan
    else 
        r = x1
    end
endfunction


// ---------- Método Iterativo de Punto Fijo
// g funcion
// x0 valor de dom(g) suficientemente cercano a raíz
// dif distancia luego de una iteración
// it máximo de iteraciones
function r = metodo_punto_fijo(g, x0, dif, it)
    x1 = g(x0)
    
    while abs(x1 - x0) >= dif && it ~= 0
        x0 = x1
        x1 = g(x0)
        it = it - 1
    end
    
    if it == 0 then
        printf("Max iteraciones alcanzado")
        r = %nan
    else 
        r = x1
    end
endfunction
// deff("y=g2(x)","y=log(3*(x**2))")
// metodo_punto_fijo(g2, 2, 0.000000001, 10)


// ---------- Método de Punto Fijo mediante Tail Recursion
function r = metodo_pfijo_tr(g, x0, dif, it)
    r = metodo_pfijo_tr_aux(g, x0, dif, it-1, g(x0))
endfunction

function r = metodo_pfijo_tr_aux(g, x0, dif, it, carry)
    if it == 0 then
        printf("Max iteraciones alcanzado")
        r = %nan
    else
        if abs(carry - x0) < dif
            r = carry
        else
            r = metodo_pfijo_tr_aux(g, carry, dif, it-1, g(carry)) // Preguntar si esto hace tail recursion siendo que return no existe, el r= es obligatorio y se forma algo tipo r=r=r=...=val
        end
    end
endfunction


// ---------- Método de la Secante
// f funcion
// x0 valor de dom(f)
// x1 valor de dom(f)
// dif distancia luego de una iteración
// it máximo de iteraciones
function r = metodo_secante(f, x0, x1, dif, it)
    fx0 = f(x0)
    fx1 = f(x1)
    xn = x1 - fx1 * ((x1-x0)/(fx1-fx0))
    
    while abs(xn - x1) >= dif && it ~= 0
        x0 = x1
        x1 = xn
        
        fx0 = f(x0)
        fx1 = f(x1)
        xn = x1 - fx1 * ((x1-x0)/(fx1-fx0))
        
        it = it - 1
    end
    
    if it == 0 then
        printf("Max iteraciones alcanzado")
        r = %nan
    else 
        r = xn
    end
endfunction


// ---------- Método de Regula Falsi
// f funcion
// a valor de dom(f)
// b valor de dom(f)
// err distancia luego de una iteración
// it máximo de iteraciones
function c = metodo_regula_falsi(f, a, b, err, it)
    if f(a)*f(b) < 0 then
        fa = f(a)
        fb = f(b)
        c = xb - fxb * ((b-a)/(fb-fa))
        
        while b - c > err && f(r) ~= 0 && it ~= 0
            if f(a)*f(c)<0 then 
                b = c
            else
                a = c
            end
            
            fa = f(a)
            fb = f(b)
            c = xb - fxb * ((b-a)/(fb-fa))
            it = it - 1
        end
        
        if it == 0 then
            printf("Max iteraciones alcanzado")
            r = %nan
        else
            r = c
        end
    end
endfunction
