//CPP:curso/procesador.cpp
#if !defined procesador_h
#define procesador_h

#include "simulator.h"
#include "event.h"
#include "stdarg.h"



class procesador: public Simulator { 
// Declare the state,
// output variables
// and parameters

// estados
bool busy;
double sigma;

// salida
double y;
	
public:
	procesador(const char *n): Simulator(n) {};
	void init(double, ...);
	double ta(double t);
	void dint(double);
	void dext(Event , double );
	Event lambda(double);
	void exit();
};
#endif
