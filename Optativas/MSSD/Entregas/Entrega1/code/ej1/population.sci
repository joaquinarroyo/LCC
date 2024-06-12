function xk1 = population(xk, k)
  b = 0.1;
  a = 0.01;
  xk1 = xk + b * xk - a * k^2;
end
