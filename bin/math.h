#ifndef MATH_H
#define MATH_H


#include "vf__floating_point.h"

double fabs(double x);
    //@ requires real_of_double(x) == some(?rx);
    //@ ensures real_of_double(result) == some(?rresult) &*& rresult >=0 &*& rresult == rx || rresult == -rx;
    //@ terminates;


/*@ 

lemma void congruentie_lemma(real x, real a, real y);
    requires x * a == y * a;
    ensures x == y;
    
lemma void substitution_lemma(real x, real a, real b, real z);
    requires a == b &*& x == a * z;
    ensures x == b * z;
    
lemma void substitution_lemma2(real x, real a, real b, real y);
    requires x == a * y &*& x == b * y;
    ensures a == b;
    
fixpoint real real_div(real x, real y);
/*
lemma real real_div(real x, real y);
    requires true;
    ensures x == result * y;
*/
lemma void real_div_lemma(real x, real y, real result);
    requires real_div(x,y) == result;
    ensures x == y * result;
    
lemma void real_div_lemma2(real x, real y, real result);
    requires x == y * result;
    ensures real_div(x,y) == result;



lemma void rr_lemma(real rr); //lemma for ceiling_test2 (tester.c)
    requires true;
    ensures rr <= 0 &*& rr > -1.0;

lemma option<real> real_of_double_lemma(double x);
    requires true; //isreal(x);
    ensures result == some(?rx);

lemma void real_of_int_lemma(int x, real rx);
    requires true;
    ensures real_of_int(x) == rx;
    
lemma void int_add_lemma(int x, int y, int result);
    requires some(real_of_int(x)) == some(?rx) &*& some(real_of_int(y)) == some(?ry) &*& some(real_of_int(result)) == some(?rresult) &*& x + y == result;
    ensures rresult == rx + ry;

fixpoint real real_sqrt(real x);


lemma void real_sqrt_lemma(real x, real sqrt);
    requires sqrt * sqrt == x;
    ensures real_sqrt(x) == sqrt;
    
lemma void real_sqrt_lemma2(real x, real sqrt);
    requires real_sqrt(x) == sqrt;
    ensures sqrt * sqrt == x;

fixpoint real real_vector_size(real x, real y){
    return real_sqrt(x * x + y * y);
} 

fixpoint int real_ceiling(real x);

lemma void real_ceiling_lemma(real x, int ceil);
    requires real_of_int(ceil) >= x &*& real_of_int(ceil) - x < 1;
    ensures real_ceiling(x) == ceil;

@*/



#endif