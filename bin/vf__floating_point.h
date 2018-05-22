#ifndef VF__FLOATING_POINT_H
#define VF__FLOATING_POINT_H

#define float_eps 1.192093e-7
#define double_eps 2.220446e-16
#define long_double_eps 1.084202e-19
#define f_eps 1.192093e-7
#define d_eps 2.220446e-16
#define ld_eps 1.084202e-19

#define md_eps 0.9999999999999997779554 // = 1 - d_eps
#define pd_eps 1.0000000000000002220446 // = 1 + d_eps

//#include "math.h"
// VeriFast interprets floating-point operations as calls of the functions declared below.

// A floating-point constant of type T is interpreted as a call of the T_of_real function.

//lemma multiplication


/*@
fixpoint real real_div(real x, real y);
fixpoint real real_abs(real x) {return x < 0 ? -x : x; }

lemma void product_sign_lemma(real x, real y);
    requires x>=0 && y>=0 || x<=0 && y<=0;
    ensures x*y >= 0;


lemma void strict_product_sign_lemma(real x, real y);
    requires x>=0 && y>=0 || x<=0 && y<=0;
    ensures x*y >= 0 &*& x == 0 || y == 0 ? x * y == 0 : 0 < x * y;

lemma void multiply_zero_lemma(real x, real y);
    requires x == 0 || y == 0;
    ensures x * y == 0;

fixpoint option<real> real_of_long_double(long double x);

fixpoint option<real> real_of_double(double x);

fixpoint option<real> real_of_float(float x);

fixpoint real real_of_int(int x);

fixpoint bool is_pos_infinity(double x);

fixpoint bool is_neg_infinity(double x);

fixpoint real next(real x);

fixpoint real prev(real x);

lemma void next_lemma(real x, real next);
    requires next == next(x);
    ensures next > x &*&
    next <= x + real_abs(x * d_eps);
    
lemma void prev_lemma(real x, real prev);
    requires prev == prev(x);
    ensures prev < x &*&
    prev >= x - real_abs(x * d_eps);
    
lemma void next_prev_lemma(real x, real nextprev);
    requires nextprev == next(prev(x));
    ensures nextprev >= x;
    
lemma void prev_next_lemma(real x, real prevnext);
    requires prevnext == prev(next(x));
    ensures prevnext <= x;

fixpoint bool relative_error(real x, real approximation, real epsilon) {
    return x == 0 ? approximation == 0 : approximation <= x + real_abs(epsilon * x) && approximation >= x - real_abs(epsilon * x);
}


@*/


float vf__float_of_real(real x);
    //@ requires true;
    //@ ensures true;
    //@ terminates;

double vf__double_of_real(real x);
    //@ requires true;
    //@ ensures real_of_double(result) == some(?rx) &*& relative_error(x,rx,double_eps) == true;
    //@ terminates;

long double vf__long_double_of_real(real x);
    //@ requires true;
    //@ ensures true;
    //@ terminates;

float vf__float_of_int(int x);
    //@ requires true;
    //@ ensures true;
    //@ terminates;

double vf__double_of_int(int x);
    //@ requires some(real_of_int(x)) ==  some(?rx);
    //@ ensures real_of_double(result) == some(rx) &*& rx == real_of_int(x);
    //@ terminates;

long double vf__long_double_of_int(int x);
    //@ requires true;
    //@ ensures real_of_long_double(result) == some(?rresult) &*& rresult == real_of_int(x);
    //@ terminates;

float vf__float_of_unsigned_int(unsigned int x);
    //@ requires true;
    //@ ensures true;
    //@ terminates;

double vf__double_of_unsigned_int(unsigned int x);
    //@ requires true;
    //@ ensures true;
    //@ terminates;

long double vf__long_double_of_unsigned_int(unsigned int x);
    //@ requires true;
    //@ ensures true;
    //@ terminates;

double vf__double_of_float(float x);
    //@ requires real_of_float(x) == some(?rx);
    //@ ensures  real_of_double(result) == some(rx);
    //@ terminates;

long double vf__long_double_of_float(float x);
    //@ requires true;
    //@ ensures true;
    //@ terminates;

float vf__float_of_double(double x);
    //@ requires real_of_double(x) == some(?rx);
    //@ ensures real_of_float(result) == some (?rr) &*& relative_error(rx,rr,float_eps) == true;
    //@ terminates;

long double vf__long_double_of_double(double x);
    //@ requires real_of_double(x) == some(?rx);
    //@ ensures real_of_long_double(result) == some(?rresult) &*& rresult == rx;
    //@ terminates;

float vf__float_of_long_double(long double x);
    //@ requires true;
    //@ ensures true;
    //@ terminates;

double vf__double_of_long_double(long double x);
    //@ requires real_of_long_double(x) == some(?rx);
    /*@ ensures real_of_double(result) == some(?rr) &*& 
    relative_error(rx, rr, double_eps) == true;
    @*/
    //@ terminates;

bool vf__float_eq(float x, float y);
    //@ requires true;
    //@ ensures true;
    //@ terminates;

bool vf__double_eq(double x, double y);
    //@ requires real_of_double(x) == some(?rx) &*& real_of_double(y) == some(?ry);
    //@ ensures result == (rx == ry);
    //@ terminates;

bool vf__long_double_eq(long double x, long double y);
    //@ requires true;
    //@ ensures true;
    //@ terminates;

bool vf__float_neq(float x, float y);
    //@ requires true;
    //@ ensures true;
    //@ terminates;

bool vf__double_neq(double x, double y);
    //@ requires true;
    //@ ensures true;
    //@ terminates;

bool vf__long_double_neq(long double x, long double y);
    //@ requires true;
    //@ ensures true;
    //@ terminates;

bool vf__float_lt(float x, float y);
    //@ requires true;
    //@ ensures true;
    //@ terminates;

bool vf__double_lt(double x, double y);
    //@ requires real_of_double(x) == some(?rx) &*& real_of_double(y) == some(?ry);
    //@ ensures result == (rx < ry);
    //@ terminates;

bool vf__long_double_lt(long double x, long double y);
    //@ requires true;
    //@ ensures true;
    //@ terminates;

bool vf__float_le(float x, float y);
    //@ requires true;
    //@ ensures true;
    //@ terminates;

bool vf__double_le(double x, double y);
    //@ requires real_of_double(x) == some(?rx) &*& real_of_double(y) == some(?ry);
    //@ ensures result == (rx <= ry);
    //@ terminates;

bool vf__long_double_le(long double x, long double y);
    //@ requires true;
    //@ ensures true;
    //@ terminates;

bool vf__float_gt(float x, float y);
    //@ requires true;
    //@ ensures true;
    //@ terminates;

bool vf__double_gt(double x, double y);
    //@ requires real_of_double(x) == some(?rx) &*& real_of_double(y) == some(?ry);
    //@ ensures result == (rx > ry);
    //@ terminates;

bool vf__long_double_gt(long double x, long double y);
    //@ requires true;
    //@ ensures true;
    //@ terminates;

bool vf__float_ge(float x, float y);
    //@ requires true;
    //@ ensures true;
    //@ terminates;

bool vf__double_ge(double x, double y);
    //@ requires real_of_double(x) == some(?rx) &*& real_of_double(y) == some(?ry);
    //@ ensures result == (rx >= ry);
    //@ terminates;

bool vf__long_double_ge(long double x, long double y);
    //@ requires true;
    //@ ensures true;
    //@ terminates;

float vf__float_add(float x, float y);
    //@ requires true;
    //@ ensures true;
    //@ terminates;

double vf__double_add(double x, double y);
    /*@ requires real_of_double(x) == some(?rx) &*& 
    real_of_double(y) == some(?ry) &*&
    rx == 0 ? ensures real_of_double(result) == some(?rr) &*& rr == ry:
    ry == 0 ? ensures real_of_double(result) == some(?rr) &*& rr == rx: true;
    @*/ 
    /*@ ensures real_of_double(result) == some(?rr) &*& 
        rr == next(rx + ry) || rr == prev(rx + ry) || rr == rx + ry &*& // naar boven afgerond, naar beneden afgerond of exacts
    	relative_error(rx + ry, rr, double_eps) == true;
    @*/
    //@ terminates;

long double vf__long_double_add(long double x, long double y);
    //@ requires real_of_long_double(x) == some(?rx) &*& real_of_long_double(y) == some(?ry);
    /*@ ensures real_of_long_double(result) == some(?rr) &*& 
    relative_error(rx + ry, rr, long_double_eps) == true;
    @*/
    //@ terminates;

float vf__float_sub(float x, float y);
    //@ requires true;
    //@ ensures true;
    //@ terminates;

double vf__double_sub(double x, double y);
    /*@ requires real_of_double(x) == some(?rx) &*& 
    is_pos_infinity(y) ? ensures is_neg_infinity(result) == true:
    is_neg_infinity(y) ? ensures is_pos_infinity(result) == true:	
    ensures real_of_double(y) == some(?ry) &*& 
    real_of_double(result) == some(?rr) &*& 
    rr == next(rx - ry) || rr == prev(rx - ry) || rr == rx - ry &*&
    relative_error(rx - ry, rr, double_eps) == true;
    @*/
    //@ ensures true;
    //@ terminates;

long double vf__long_double_sub(long double x, long double y);
    //@ requires true;
    //@ ensures true;
    //@ terminates;

float vf__float_mul(float x, float y);
    //@ requires true;
    //@ ensures true;
    //@ terminates;

double vf__double_mul(double x, double y);
    //@ requires real_of_double(x) == some(?rx) &*& real_of_double(y) == some(?ry);
    //@ ensures real_of_double(result) == some(?rr) &*& relative_error(rx * ry, rr, double_eps) == true;
    //@ terminates;

long double vf__long_double_mul(long double x, long double y);
    //@ requires true;
    //@ ensures true;
    //@ terminates;

float vf__float_div(float x, float y);
    //@ requires true;
    //@ ensures true;
    //@ terminates;

double vf__double_div(double x, double y);
    /*@ requires real_of_double(x) == some(?rx) &*&
    real_of_double(y) == some(?ry) &*&
    rx > 0 && ry == 0 ? ensures is_pos_infinity(result) == true &*& 
    			is_neg_infinity(result) == false:
    rx < 0 && ry == 0 ? ensures is_neg_infinity(result) == true &*& 
    			is_pos_infinity(result) == false: 
    true; 
    @*/ /*@
    ensures real_of_double(result) == some(?rr) &*& 
    relative_error(real_div(rx,ry), rr, double_eps) == true;
    @*/
    //@ terminates;

long double vf__long_double_div(long double x, long double y);
    //@ requires real_of_long_double(x) == some(?rx) &*& real_of_long_double(y) == some(?ry);
    //@ ensures real_of_long_double(result) == some(?rr) &*& relative_error(real_div(rx,ry), rr, long_double_eps) == true;
    //@ terminates;

#endif