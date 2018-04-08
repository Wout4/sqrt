#ifndef MATH_H
#define MATH_H


#include "vf__floating_point.h"

double fabs(double x);
    //@ requires real_of_double(x) == some(?rx);
    //@ ensures real_of_double(result) == some(?rresult) &*& rresult >=0 &*& rresult == rx || rresult == -rx;
    //@ terminates;


/*@ 
    
lemma void leq_substitution_lemma(real x, real y, real z);
    requires x <= y &*& y == z;
    ensures x <= z;
    
lemma void geq_substitution_lemma(real x, real y , real z);
    requires x >= y &*& y == z;
    ensures x >= z;

lemma void substitution_lemma(real x, real y, real z, real w);
    requires x == y + z &*& y == w;
    ensures x == w + z;   
    
lemma void product_substitution_lemma(real a, real b, real c);
    requires b <= c &*& a >= 0;
    ensures a * b <= a * c;
    
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
    
lemma void real_div_sub_lemma2(real a, real x, real y);
    requires y != 0;
    ensures real_div(x,y) - a == real_div(x - a * y, y);
    
lemma void real_div_add_lemma(real a, real x, real y);
    requires y != 0;
    ensures a + real_div(x,y) == real_div(a * y + x,y);
   
lemma void real_div_pos_lemma(real x, real y);
    requires (x >= 0 && y > 0) || (x <= 0 && y < 0);
    ensures real_div(x,y) >= 0;

lemma void real_of_int_lemma(int x, real rx);
    requires true;
    ensures real_of_int(x) == rx;


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
    
lemma void sqrt_extraction_lemma(real x, real y);
    requires x >= 0 &*& y >= 0;
    ensures real_sqrt(x*y) == real_sqrt(x) * real_sqrt(y);
    
lemma void sqrt_zero_lemma(real x);
    requires x == 0;
    ensures real_sqrt(x) == 0;
    
lemma void sqrt_pos_lemma(real x);
    requires x > 0;
    ensures real_sqrt(x) > 0;
    
lemma void sqrt_leq_one_lemma(real x);
    requires x <= 1 &*& x >= 0;
    ensures real_sqrt(x) <= 1;
    
lemma void sqrt_geq_one_lemma(real x);
    requires x >= 1;
    ensures real_sqrt(x) >= 1;
    
fixpoint real real_vector_size(real x, real y){
    return real_sqrt(x * x + y * y);
} 

fixpoint int real_ceiling(real x);
    
lemma void real_ceiling_gt_lemma(real a, real b);
    requires a - b >= 1;
    ensures real_ceiling(a) > real_ceiling(b);

lemma void real_ceiling_pos_lemma(real a);
    requires a >= 0;
    ensures real_ceiling(a) >= 0;
    
    
lemma void lemma1(real orr2,real ordiv2,real rx,real sqrx)
    requires orr2 >= sqrx &*& 
    rx == orr2 * ordiv2 &*&
    sqrx * sqrx == rx &*&
    sqrx > 0;
    ensures ordiv2 <= sqrx &*& 
    real_div(rx,orr2) == ordiv2 &*&
    (orr2 + ordiv2)/2 >= sqrx;
    {
    real_div_lemma2(rx,orr2,ordiv2);
    real rr2 = (orr2 + ordiv2)/2;
    real b1 = orr2 - sqrx;
    assert ordiv2 == real_div(rx,sqrx + b1);
    real_div_sub_lemma(sqrx, b1 * sqrx, b1 + sqrx);
    assert ordiv2 == sqrx - real_div(b1 * sqrx, b1 + sqrx);
    real_div_sub_lemma(b1, b1 * sqrx, b1 + sqrx);
    product_sign_lemma(b1,b1);
    real_div_pos_lemma(b1 * b1, sqrx + b1);
    assert b1 - real_div(b1 * sqrx, b1 + sqrx) >= 0;
    assert (rr2) >= sqrx;
    product_sign_lemma(sqrx,b1);
    assert sqrx * b1 >= 0;
    real_div_pos_lemma(b1 * sqrx, b1 + sqrx);
    assert real_div(b1 * sqrx, b1 + sqrx) >= 0;
    assert ordiv2 <= sqrx;
}

lemma void lemma2(real orr1, real ordiv1, real rx, real sqrx)
    requires orr1 < sqrx &*& 
    rx == orr1 * ordiv1 &*&
    sqrx * sqrx == rx &*&
    orr1 > 0 &*&
    ordiv1 == real_div(rx,orr1) &*&
    sqrx > 0;
    ensures ordiv1 >= sqrx &*& 
    real_div(rx,orr1) == ordiv1 &*&
    (orr1 + ordiv1)/2 >= sqrx;
    {
    real rr1 = (orr1 + ordiv1)/2;
    assert sqrx > orr1;
    real b = sqrx - orr1;
    assert ordiv1 == real_div(rx,sqrx - b); 
    real_div_add_lemma(sqrx, b * sqrx, sqrx - b);
    assert ordiv1 == sqrx + real_div(b * sqrx, sqrx - b); 
    real_div_sub_lemma2(b, b * sqrx, sqrx - b);
    product_sign_lemma(b,b);
    real_div_pos_lemma(b * b, sqrx - b);
    assert real_div(b * sqrx,sqrx - b) - b >= 0; 
    assert rr1 >= sqrx;
    assert real_abs(sqrx - orr1) == sqrx - orr1;
    assert rr1 <= ordiv1;
    assert rr1 >= orr1;
    }
    
lemma void lemma3(real rr, real nrr, real sqrx)
    requires rr - nrr >= 0.000004*nrr &*&
    sqrx > 0 &*&
    nrr >= sqrx;
    ensures real_ceiling(real_div(rr,sqrx)*1000000) > real_ceiling(real_div(nrr,sqrx)*1000000) &*&
    real_ceiling(real_div(nrr,sqrx)*1000000) >= 0;
    {
    real c = rr - nrr;
    assert c >= 0.000004*nrr;
    real_div_sum_lemma(nrr,c,sqrx);
    assert real_div(rr,sqrx) == real_div(nrr, sqrx) + real_div(c,sqrx);
        
    real_div_subs_lemma(0.000004*nrr,c,sqrx);
    assert real_div(c,sqrx) >= real_div(0.000004*nrr,sqrx);
    real_div_extraction_lemma(0.000004,nrr,sqrx);
    assert real_div(c,sqrx) >= 0.000004*real_div(nrr,sqrx);
    real_div_geq1(nrr,sqrx);
    assert real_div(nrr,sqrx) >= 1;
    assert real_div(c,sqrx) >= 0.000004;
       
    real_ceiling_gt_lemma(real_div(rr,sqrx)*1000000,real_div(nrr,sqrx)*1000000);
    assert real_ceiling(real_div(rr,sqrx)*1000000) > real_ceiling(real_div(nrr,sqrx)*1000000);
        
    real_ceiling_pos_lemma(real_div(nrr,sqrx)*1000000);
    assert real_ceiling(real_div(nrr,sqrx)*1000000) >= 0;
    }
    
@*/



#endif