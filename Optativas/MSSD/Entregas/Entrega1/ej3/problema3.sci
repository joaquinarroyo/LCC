S0=1e6;
E0=0;
I0=10;
R0=0;
x0=[S0,E0,I0,R0];
[t,x]=dtsim(discreteSEIR,x0,0,365);
plot(t,x);
