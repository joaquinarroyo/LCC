model discreteSIR
parameter Real N = 1e6;
discrete Real S(start = N), I(start = 10), R;
parameter Real alpha = 1, gamma = 0.5;
algorithm
when sample(0, 1) then
S := pre(S) - alpha * pre(S) * pre(I) / N;
I := pre(I) + alpha * pre(S) * pre(I) / N - gamma * pre(I);
R := pre(R) + gamma * pre(I);
end when;
end discreteSIR;
