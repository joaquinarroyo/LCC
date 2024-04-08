model multiSIR
  discreteSIRimp M1, M2(I.start = 0), M3(I.start = 0);
algorithm
  when sample(0, 1) then
    M1.imp := 0.5 * pre(M2.exp);
    M2.imp := pre(M1.exp) + pre(M3.exp);
    M3.imp := 0.5 * pre(M2.exp);
  end when;
end multiSIR;
