model discreteSIRimp
  parameter Real N = 1e6;
  discrete Real S(start = N), I(start = 10), R,imp,exp;
  parameter Real alpha = 1, gamma = 0.5, m=0.01;
algorithm
  when sample(0, 1) then
    S := pre(S) - alpha * pre(S) * pre(I) / N;
    I := pre(I) + alpha * pre(S) * pre(I) / N - gamma * pre(I) + imp - exp;
    R := pre(R) + gamma * pre(I);
    exp:= m* pre(I);
  end when;
end discreteSIRimp;
