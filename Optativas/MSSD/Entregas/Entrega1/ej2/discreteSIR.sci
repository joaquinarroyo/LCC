function x=discreteSIR(pre_x, t)
  al=1;
  gam=0.5;
  N=1e6;
  pre_S=pre_x(1);
  pre_I=pre_x(2);
  pre_R=pre_x(3);
  S = pre_S - (al * pre_S * pre_I) / N;
  I = pre_I + ((al * pre_S * pre_I) / N) - gam * pre_I;
  R = pre_R + gam * pre_I;
  x=[S;I;R];
end
