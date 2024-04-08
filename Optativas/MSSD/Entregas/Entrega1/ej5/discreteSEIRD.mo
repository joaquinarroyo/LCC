model discreteSEIRD
parameter Integer TI=3, TR=12;
parameter Real R0=1.5, N=1e6, Cte=R0/(TR-TI);
discrete Real S(start = N), I(start = 10), R(start = 0), E(start = 0);
discrete Real NE[500], NETI, NETR;
discrete Integer C(start = 1);
algorithm
when sample(0, 1) then
  NE[C] := Cte * ((pre(I) * pre(S)) / N);
  
  if C-TI >= 1 then
    NETI := NE[C-TI];
  else
    NETI := 0;
  end if;
  
  if C-TR >= 1 then
    NETR := NE[C-TR];
  else
    NETR := 0;
  end if;
  
  S := pre(S) - NE[C];
  E := pre(E) + NE[C] - NETI;
  I := pre(I) + NETI - NETR;
  R := pre(R) + NETR;
  C := C+1;
end when;
end discreteSEIRD;
