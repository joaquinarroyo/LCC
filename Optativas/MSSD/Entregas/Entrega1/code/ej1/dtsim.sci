function x = dtsim(f, x0, tf)
  x = zeros(1, tf);
  x(:,1) = x0;
  for k = 1:tf-1
    x(:,k+1) = f(x(:,k), k);
  end
end
