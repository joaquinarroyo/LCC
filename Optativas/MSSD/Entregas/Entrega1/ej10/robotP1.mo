model robotP1
  parameter Real L=1, h=0.1;
  discrete Real Accel(start = 0), Rotspeed(start = 0);
  discrete Real X(start = 0), Y(start = 0), Vel(start = 0), Cangl(start = 0), Wangl(start = 0);
  discrete Real C(start = 0);
algorithm
  when sample(0, h) then
    if C < 2 then
      Accel := 1;
    else
      Accel := 0;
    end if;
  
    if C < 1 then
      Rotspeed := 0.1;
    elseif C < 2 then
      Rotspeed := -0.1;
    else
      Rotspeed := 0;
    end if;
  
    X := pre(X) + h * (cos(pre(Cangl))*cos(pre(Wangl))*pre(Vel));
    Y := pre(Y) + h * (sin(pre(Cangl))*cos(pre(Wangl))*pre(Vel));
    Cangl := pre(Cangl) + h * ((sin(pre(Wangl))*pre(Vel))/L);
    Vel := pre(Vel) + h * Accel;
    Wangl := pre(Wangl) + h * Rotspeed;

    C := C+h;
  end when;
end robotP1;
