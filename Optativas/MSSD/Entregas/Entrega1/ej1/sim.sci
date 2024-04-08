function x = sim(x0, tf)
  b = 0.1;
  d = 0.02;
  x = zeros(1, tf);
  x(1) = x0;
  for k = 1:tf-1
    x(k+1) = x(k)*(1 + b - d)
  end
end