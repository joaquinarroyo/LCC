model robotP2
  parameter Real L=4, h=0.1, Kv=1, Kdir=2, Ky=0.5, vref=2, yref=1;
  discrete Real Accel(start = 0), Rotspeed(start = 0), DirRef(start = 0);
  discrete Real X(start = 0), Y(start = 0), Vel(start = 0), Cangl(start = 0), Wangl(start = 0);
  discrete Real C(start = 0);
algorithm
  when sample(0, h) then
    DirRef := Ky * (atan(yref - Y)/(L - Cangl));
    Accel := Kv * (vref - Vel);
    Rotspeed := Kdir * (DirRef - Wangl);
  
    X := pre(X) + h * (cos(pre(Cangl))*cos(pre(Wangl))*pre(Vel));
    Y := pre(Y) + h * (sin(pre(Cangl))*cos(pre(Wangl))*pre(Vel));
    Cangl := pre(Cangl) + h * ((sin(pre(Wangl))*pre(Vel))/L);
    Vel := pre(Vel) + h * Accel;
    Wangl := pre(Wangl) + h * Rotspeed;

    C := C+h;
  end when;
end robotP2;
