//CPP:curso/controlador.cpp
#if !defined controlador_h
#define controlador_h

#include "simulator.h"
#include "event.h"
#include "stdarg.h"



class controlador: public Simulator { 
// Declare the state,
// output variables
// and parameters

// estado 
double sigma;
double error;
double ac_error;
double prob;

// salida
double y;

// parametro
double Lref;
double K1;
double K2;






public:
	controlador(const char *n): Simulator(n) {};
	void init(double, ...);
	double ta(double t);
	void dint(double);
	void dext(Event , double );
	Event lambda(double);
	void exit();
};
#endif
