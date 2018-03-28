#ifndef MATH_H
#define MATH_H


#include "vf__floating_point.h"

double fabs(double x);
    //@ requires real_of_double(x) == some(?rx);
    //@ ensures real_of_double(result) == some(?rresult) &*& rresult >=0 &*& rresult == rx || rresult == -rx;
    //@ terminates;


/*@ 
lemma void leq_trans_lemma(real a, real b, real c);
    requires a <= b &*& b <= c;
    ensures a <= c;

lemma void equal(real x, real y);
    requires true;
    ensures x == y;

lemma void dummy_lemma(real a, real b, real c);
    requires true;
    ensures a - b <= b - c;
    
lemma void dummy_lemma2(real x, real a);
    requires true;
    ensures x > 1 ? real_abs(a) == a : true;

lemma void congruentie_lemma(real x, real a, real y);
    requires x * a == y * a &*& a != 0;
    ensures x == y;
    
lemma void substitution_lemma(real x, real a, real b, real z);
    requires a == b &*& x == a * z;
    ensures x == b * z;
    
lemma void substitution_lemma2(real x, real a, real b, real y);
    requires x == a * y &*& x == b * y;
    ensures a == b;
    
fixpoint real real_div(real x, real y);

lemma void real_div_lemma(real x, real y, real result);
    requires real_div(x,y) == result;
    ensures x == y * result;
    
lemma void real_div_lemma2(real x, real y, real result);
    requires x == y * result;
    ensures real_div(x,y) == result;

lemma void division_lemma(real numerator, real smallDenominator, real bigDenominator);
    requires smallDenominator <= bigDenominator &*& numerator >=0;
    ensures real_div(numerator,smallDenominator) >= real_div(numerator,bigDenominator);
    
lemma void division_lemma2(real num1, real num2, real denom);
    requires num1 < num2 &*& denom > 0;
    ensures real_div(num1,denom) < real_div(num2,denom);
    
lemma void equality_division_lemma(real a, real b, real c);
    requires a == b &*& c != 0;
    ensures real_div(a,c) == real_div(b,c);
    
lemma void real_div_sum_lemma(real a, real b, real c);
    requires c != 0;
    ensures real_div(a + b, c) == real_div(a,c) + real_div(b,c);
    
lemma void real_div_geq1(real a, real b);
    requires a >= b &*& a >= 0 &*& b > 0;
    ensures real_div(a,b) >= 1;
    
lemma void real_div_subs_lemma(real a, real b, real c);
    requires a <= b &*& c > 0;
    ensures real_div(a,c) <= real_div(b,c);
    
lemma void real_div_extraction_lemma(real b, real c, real d);
    requires d != 0;
    ensures real_div(b * c, d) == b * real_div(c,d);
    
lemma void real_div_sub_lemma(real a, real x, real y);
    requires y != 0;
    ensures a - real_div(x,y) == real_div(a * y - x , y);
    
lemma void real_div_add_lemma(real a, real x, real y);
    requires y != 0;
    ensures a + real_div(x,y) == real_div(a * y + x,y);
   
lemma void real_div_pos_lemma(real x, real y);
    requires (x >= 0 && y > 0) || (x <= 0 && y < 0);
    ensures real_div(x,y) >= 0;

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
    
lemma void sqrt_congruence_lemma(real x, real y);
    requires x <= y &*& x>=0 &*& y>=0;
    ensures real_sqrt(x) <= real_sqrt(y);
    
lemma void strict_sqrt_congruence_lemma(real x, real y);
    requires x < y &*& x>=0 &*& y>=0;
    ensures real_sqrt(x) < real_sqrt(y);
    
lemma void average_approximation_lemma2(real under, real over);
    requires under <= over;
    ensures (under + over) / 2 <= over &*& (under + over) / 2 >= under;

fixpoint real real_vector_size(real x, real y){
    return real_sqrt(x * x + y * y);
} 

fixpoint int real_ceiling(real x);

lemma void real_ceiling_lemma(real x, int ceil);
    requires real_of_int(ceil) >= x &*& real_of_int(ceil) - x < 1;
    ensures real_ceiling(x) == ceil;
    
lemma void real_ceiling_gt_lemma(real a, real b);
    requires a - b >= 1;
    ensures real_ceiling(a) > real_ceiling(b);

lemma void real_ceiling_pos_lemma(real a);
    requires a >= 0;
    ensures real_ceiling(a) >= 0;
@*/



#endif