function salida = newton(fun, x0, tol, iter)
    deff("y=f(x)","y="+fun);
    i = 0;
    x1 = (x0 - f(x0)) / numderivative(f, x0);
    
    while(abs(x1-x0)>tol) && i < iter)
        i = i+1;
        x0 = x1
        x1 = (x0 - f(x0)) / numderivative(f, x0);
    
    if (abs(x1-x0) > tol) then disp("Se alcanzo el maximo de iteraciones.") end
    disp(i);
    if (abs(x1 - x0) < tol then disp("Se paso la tolerancia.")end;
    salida = x1;
        
endfunction
