//CPP:curso/fuente.cpp
#if !defined fuente_h
#define fuente_h

#include "simulator.h"
#include "event.h"
#include "stdarg.h"



class fuente: public Simulator { 
// Declare the state,
// output variables
// and parameters

// estados
double z,sigma;

// salida
double y;

// parametros
double Jmin, Jmax, Tmax;
public:
	fuente(const char *n): Simulator(n) {};
	void init(double, ...);
	double ta(double t);
	void dint(double);
	void dext(Event , double );
	Event lambda(double);
	void exit();
};
#endif
