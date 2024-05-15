#include "controlador.h"
void controlador::init(double t,...) {
//The 'parameters' variable contains the parameters transferred from the editor.
va_list parameters;
va_start(parameters,t);
//To get a parameter: %Name% = va_arg(parameters,%Type%)
//where:
//      %Name% is the parameter name
//	%Type% is the parameter type

Lref=va_arg(parameters,double); 
K1=va_arg(parameters,double);
K2=va_arg(parameters,double);

sigma=1e20;
ac_error=0;
}
double controlador::ta(double t) {
//This function returns a double.
return sigma;

}
void controlador::dint(double t) {
sigma=1e20;
}
void controlador::dext(Event x, double t) {
p//The input event is in the 'x' variable.
//where:
//     'x.value' is the value (pointer to void)
//     'x.port' is the port number
//     'e' is the time elapsed since last transition

error = Lref - (-x.getDouble());
ac_error += error;

double pre_prob = K1*error + K2*ac_error;
if (pre_prob < 0) {
	prob = 0;
} else if (pre_prob > 1) {
	prob = 1;
} else {
	prob = pre_prob;
}

sigma=0;


}
Event controlador::lambda(double t) {
//This function returns an Event:
//     Event(%&Value%, %NroPort%)
//where:
//     %&Value% points to the variable which contains the value.
//     %NroPort% is the port number (from 0 to n-1)

y=prob;
return Event(&y, 0);
}
void controlador::exit() {
//Code executed at the end of the simulation.

}
