function x = discreteSEIRD(x, k)
  TI=3;
  TR=12;
  R0=1.5;
  N=1e6;
  pre_x = x(:,k);
  pre_S=pre_x(1);
  pre_E=pre_x(2);
  pre_I=pre_x(3);
  pre_R=pre_x(4);
  NET = calculateNET(x, k, TI, TR, R0, N);
  NETR = calculateNET(x, k - TR, TI, TR, R0, N);
  NETI = calculateNET(x, k - TI, TI, TR, R0, N);
  S = pre_S - NET;
  E = pre_E + NET - NETI;
  I = pre_I + NETI - NETR;
  R = pre_R + NETR;
  x=[S;E;I;R];
end

function x = calculateNET(x, k, TI, TR, R0, N)
  if k < 1
  then x = 0;
  else
    pre_S = x(:,k)(1);
    pre_I = x(:,k)(3);
    x = (R0 / (TR - TI)) * ((pre_I * pre_S) / N);
  end
endfunction


