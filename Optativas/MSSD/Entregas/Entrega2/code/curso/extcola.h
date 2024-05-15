//CPP:curso/extcola.cpp
#if !defined extcola_h
#define extcola_h

#include "simulator.h"
#include "event.h"
#include "stdarg.h"

#include "queue"


class extcola: public Simulator { 
// Declare the state,
// output variables
// and parameters

// estado
bool busy;
double sigma;
std::queue<double> cola;

// salida
double y;
public:
	extcola(const char *n): Simulator(n) {};
	void init(double, ...);
	double ta(double t);
	void dint(double);
	void dext(Event , double );
	Event lambda(double);
	void exit();
};
#endif
