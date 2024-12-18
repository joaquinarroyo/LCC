y = [6.03 6.63 7.68 8.4 7.77 5.95 6.34 12.44 12.75 8.3 12.81 25.47 20.61 13.24 11.01 8.83 4.18 4.58 4.03 4.17 3.47 2.69 2.43];
leny = length(y);
x = 1:leny;
delta = 5;
xp = leny + 1:leny + delta;
yp = interp1(x, y, xp, 'linear', 'extrap');
disp(xp);
disp(yp);
