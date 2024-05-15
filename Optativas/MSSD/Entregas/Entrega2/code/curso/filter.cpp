#include "filter.h"
void filter::init(double t,...) {
//The 'parameters' variable contains the parameters transferred from the editor.
va_list parameters;
va_start(parameters,t);
//To get a parameter: %Name% = va_arg(parameters,%Type%)
//where:
//      %Name% is the parameter name
//	%Type% is the parameter type
sigma=1e20;

}
double filter::ta(double t) {
//This function returns a double.
return sigma;
}
void filter::dint(double t) {
sigma=1e20;
}
void filter::dext(Event x, double t) {
//The input event is in the 'x' variable.
//where:
//     'x.value' is the value (pointer to void)
//     'x.port' is the port number
//     'e' is the time elapsed since last transition

if(x.port==1) {
	prob = x.getDouble();
} else if(x.port==0) {
	random = (double)rand()/(double)RAND_MAX;
	if (random < prob) {
		outport = 0;
	} else {
		outport = 1;
	}
	outvalue = x.getDouble();
	sigma=0;
}


}
Event filter::lambda(double t) {
//This function returns an Event:
//     Event(%&Value%, %NroPort%)
//where:
//     %&Value% points to the variable which contains the value.
//     %NroPort% is the port number (from 0 to n-1)

y = outvalue;
return Event(&y, outport);
}
void filter::exit() {
//Code executed at the end of the simulation.

}
