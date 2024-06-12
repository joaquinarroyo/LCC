model discreteSEIR
parameter Real alpha = 1, gamma = 0.5, mu = 0.5, N = 1e6, b = 0.1;
discrete Real S(start = N), I(start = 10), R(start = 0), E(start = 0);
algorithm
when sample(0, 1) then
S := pre(S) - alpha * pre(S) * pre(I) / N;
E := pre(E) + alpha * pre(S) * pre(I) / N - mu * pre(E);
I := pre(I) + mu * pre(E) - gamma * pre(I);
R := pre(R) + gamma * pre(I);
end when;
end discreteSEIR;
