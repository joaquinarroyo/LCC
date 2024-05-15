#include "extcola.h"
void extcola::init(double t,...) {
//The 'parameters' variable contains the parameters transferred from the editor.
va_list parameters;
va_start(parameters,t);
//To get a parameter: %Name% = va_arg(parameters,%Type%)
//where:
//      %Name% is the parameter name
//	%Type% is the parameter type

busy=false;
sigma=1e20;

}
double extcola::ta(double t) {
//This function returns a double.
return sigma;
}
void extcola::dint(double t) {
busy=true;
cola.pop();
sigma=1e20;
}
void extcola::dext(Event x, double t) {
//The input event is in the 'x' variable.
//where:
//     'x.value' is the value (pointer to void)
//     'x.port' is the port number
//     'e' is the time elapsed since last transition
if(x.port==1 && cola.empty()) {
	busy=false;
	sigma=1e20;
}else if(x.port==1 && !cola.empty()) {
	busy=false;
	sigma=0;
}else if(x.port==0 && busy) {
	cola.push(x.getDouble());
	sigma=1e20;
}else if(x.port==0 && !busy) {
	cola.push(x.getDouble());
	sigma=0;
}
}
Event extcola::lambda(double t) {
//This function returns an Event:
//     Event(%&Value%, %NroPort%)
//where:
//     %&Value% points to the variable which contains the value.
//     %NroPort% is the port number (from 0 to n-1)

y=cola.front();
return Event(&y,0);
}
void extcola::exit() {
//Code executed at the end of the simulation.

}
