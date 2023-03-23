//Calcula las raices del polinomio p con el metodo robusto.
//p es un polinomio de grado 2
function misraices(p)
    r = []
    c = coeff(p,0);     //Tomamos los 3 coeficientes para aplicar el metodo
    b = coeff(p,1);     //robusto para calcular las raices del polinomio
    a = coeff(p,2);
    if b >= 0 then
        r(1) = (-b + sqrt(b^2-4*a*c))/(2*a);
        r(2) = (2*c)/(-b+sqrt(b^2-4*a*c));
        error(r(1), r(2))
    end
    if b < 0 then
        r(1) = (2*c)/(-b-sqrt(b^2-4*a*c));
        r(2) = (-b - sqrt(b^2-4*a*c))/(2*a);
        error(r(1), r(2))
    end
endfunction

//Funcion utilizada para imprimir los errores del caso particular del 
//ejercicio 1
function error(r1, r2)
    e1 = 1e-8;
    error1 = abs(r1-e1)/e1;
    error2 = abs(r2-e1)/e1;
    printf("Esperado : %e\n", e1);
    printf("raiz1 : %e (error= %e)\n", r1, error1);
    printf("raiz2 : %e (error= %e)\n", r2, error2);
endfunction

//Evauluando esta funcion en siguiente polinomio:
//p = poly([-0.0001 10000.0 0.0001], 'x', 'coeff')
//-0.0001 +10000x +0.0001x^2
//Obtenemos:
//Esperado : 1.000000e-08
//raiz1 : 9.094947e-09 (error= 9.050530e-02)
//raiz2 : -1.099512e+08 (error= 1.099512e+16)
