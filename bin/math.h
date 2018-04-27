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
    
lemma void leq_transitivity_lemma(real a, real b, real c)
    requires a <= b &*& b <= c;
    ensures a <= c;
    {}
    
lemma void associativity_lemma(real a, real b, real c);
    requires true;
    ensures a * b * c == a * (b * c);
    
lemma void leq_preservation_lemma(real x, real y, real z);
    requires x <= y &*& z >= 0;
    ensures x * z <= y * z;
    
lemma void eq_preservation_lemma(real x, real y ,real z);
    requires x == y;
    ensures z * x == z * y;
    
lemma void geq_substitution_lemma(real x, real y , real z);
    requires x >= y &*& y == z;
    ensures x >= z;

lemma void substitution_lemma(real x, real y, real z, real w);
    requires x == y + z &*& y == w;
    ensures x == w + z;   
    
lemma void product_substitution_lemma(real a, real b, real c);
    requires b <= c &*& a >= 0;
    ensures a * b <= a * c;
    

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
    
lemma void real_div_elimination_lemma(real a, real b, real c);
    requires a != 0;
    ensures real_div(a * b, a * c) == real_div(b,c);
    
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
    requires (x >= 0 && y > 0);
    ensures real_div(x,y) >= 0;
   
lemma void real_div_product_lemma(real a, real b, real c, real d);
    requires b != 0 &*& d != 0;
    ensures real_div(a,b) * real_div(c,d) == real_div(a * c, b * d);

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
    
lemma void sqrt_congruence_lemma2(real x, real y);
    requires real_sqrt(x) <= real_sqrt(y);
    ensures  x <= y;
    
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
    


lemma void overestimation_lemma1(real orr, real sqrx, real rx, real ordiv, real eps)
    requires orr >= 1.000001 * sqrx &*&
    rx == orr * ordiv &*&
    sqrx * sqrx == rx &*&
    eps > 0 &*&
    eps < 4.9e-13 &*&
    sqrx > 0;
    ensures (1 + eps) * (orr + ordiv) / 2 <= orr &*&
    (1 - eps) * (orr + ordiv) / 2 >=  sqrx;
    {
    real_div_lemma2(rx,orr,ordiv);
    real nrre = (orr + ordiv)/2;
    real b = orr - sqrx;

    assert ordiv == real_div(rx,sqrx + b);
    real_div_sub_lemma(sqrx, b * sqrx, b + sqrx);
    assert ordiv == sqrx - real_div(b * sqrx, b + sqrx);
    real_div_sub_lemma(b, b * sqrx, b + sqrx);
    product_sign_lemma(b,b);
    real_div_pos_lemma(b * b, sqrx + b);

    assert b - real_div(b * sqrx, b + sqrx) >= 0;
    assert (nrre) >= sqrx;
    product_sign_lemma(sqrx,b);
    assert nrre == sqrx + real_div(b * b, sqrx + b) / 2;


    assert sqrx <= 1000000 * b;
    assert sqrx + b <= 1000001 * b;
    division_lemma(b,sqrx + b, 1000001 * b);
    assert real_div(b,sqrx + b ) >= real_div(b,1000001 * b);
    real_div_elimination_lemma(b, 1, 1000001);
    real_div_lemma(1,1000001,real_div(1,1000001));
    assert real_div(1,1000001) == 1 / 1000001;
    assert real_div(b,1000001 * b) == 1 / 1000001;
    assert real_div(b,sqrx + b) >= 1 / 1000001;
    
    real_div_lemma(b,sqrx,real_div(b,sqrx));
    assert b >= 0.000001 * sqrx;
    assert b / 2 >= 0.0000005 * sqrx;
    leq_preservation_lemma(0.0000005 * sqrx, b / 2, real_div(b,sqrx + b));
    assert b / 2 * real_div(b,sqrx + b) >= 0.0000005 * sqrx * real_div(b,sqrx + b);
    leq_preservation_lemma(1 / 1000001, real_div(b,sqrx + b), 0.0000005* sqrx);
    assert 0.0000005 * sqrx * real_div(b,sqrx + b)>= 0.0000005 * sqrx * 1 / 1000001;
    assert 0.0000005 * sqrx * real_div(b,sqrx + b) >=  0.0000005 * sqrx * 1 / 1000001;
    assert b / 2 * real_div(b,sqrx + b) >= 0.0000005 * sqrx * 1 / 1000001;
    real_div_extraction_lemma(b, b, sqrx + b);
    assert b / 2 * real_div(b,sqrx + b) == real_div(b * b, sqrx + b) / 2;
    assert real_div(b * b, sqrx + b) / 2 >= 0.0000005 * sqrx * 1 / 1000001;
    assert sqrx + real_div(b * b, sqrx + b) / 2 >= (0.0000005 * 1 / 1000001 + 1) * sqrx;
    assert (orr + ordiv) / 2 >= (0.0000005 * 1 / 1000001 + 1) * sqrx;
    assert sqrx <= 1000001 / 1000001.0000005 * (orr + ordiv) / 2 ;
    assert (orr + ordiv) / 2 == sqrx + real_div(b*b,sqrx + b) / 2;
    
    assert (1 - eps) >= 1000001 / 1000001.0000005;
    leq_preservation_lemma(1000001 / 1000001.0000005,(1 - eps),(orr + ordiv) / 2);
    assert 1000001 / 1000001.0000005 * (orr + ordiv) / 2 <= (1 - eps) * (orr + ordiv) / 2 ;
    assert (1 - eps) * (orr + ordiv) / 2 >=  sqrx;
    
    

    division_lemma(sqrx,1.000001 * sqrx, sqrx + b);
    assert real_div(sqrx, sqrx + b) <= real_div(1 * sqrx , 1.000001 * sqrx);
    real_div_elimination_lemma(sqrx,1,1.000001);
    real_div_lemma(1,1.000001,real_div(1, 1.000001));
    assert real_div(sqrx, sqrx + b) <= 1 / 1.000001;
    
    assert (0.5 * 1 / 1.000001 * 1 / 1.000001 + 0.5) * (1 + eps) <= 1;
    leq_preservation_lemma(real_div(sqrx, sqrx + b),1 / 1.000001, 1 / 1.000001);
    real_sqrt_lemma(real_div(sqrx, sqrx + b) * real_div(sqrx, sqrx + b),real_div(sqrx, sqrx + b));
    real_sqrt_lemma(1 / 1.000001 * 1 / 1.000001 ,1 / 1.000001 );
    sqrt_congruence_lemma2(real_div(sqrx, sqrx + b) * real_div(sqrx, sqrx + b),1 / 1.000001 * 1 / 1.000001);
    assert 0.5 * real_div(sqrx, sqrx + b) * real_div(sqrx, sqrx + b) + 0.5 <= (0.5 * 1 / 1.000001 * 1 / 1.000001 + 0.5);
    leq_preservation_lemma(0.5 * real_div(sqrx, sqrx + b) * real_div(sqrx, sqrx + b) + 0.5,0.5 * 1 / 1.000001 * 1 / 1.000001 + 0.5, 1 + eps);
    assert (0.5 * real_div(sqrx, sqrx + b) * real_div(sqrx, sqrx + b) + 0.5) * (1 + eps) <= 1;
    real_div_product_lemma(sqrx,sqrx + b,sqrx, sqrx + b);
    assert real_div(sqrx, sqrx + b) * real_div(sqrx, sqrx + b) == real_div(sqrx * sqrx, (sqrx + b) * (sqrx + b));        
    strict_product_sign_lemma(sqrx + b, sqrx + b);
    real_div_extraction_lemma(0.5, sqrx * sqrx, (sqrx + b) * (sqrx + b));
    assert (0.5 * real_div(sqrx * sqrx, (sqrx + b) * (sqrx + b)) + 0.5)== (real_div(0.5 * sqrx * sqrx, (sqrx + b) * (sqrx + b)) + 0.5);
    real_div_add_lemma(0.5, 0.5 * sqrx * sqrx, (sqrx + b) * (sqrx + b));
    assert (0.5 * real_div(sqrx * sqrx, (sqrx + b) * (sqrx + b)) + 0.5) == real_div(0.5 * ((sqrx * sqrx) + (sqrx + b) * (sqrx + b)),(sqrx + b) * (sqrx + b));
    eq_preservation_lemma((0.5 * real_div(sqrx * sqrx, (sqrx + b) * (sqrx + b)) + 0.5),real_div(0.5 * ((sqrx * sqrx) + (sqrx + b) * (sqrx + b)),(sqrx + b) * (sqrx + b)),(1 + eps));
    assert real_div(0.5 * ((sqrx * sqrx) + (sqrx + b) * (sqrx + b)),(sqrx + b) * (sqrx + b)) * (1 + eps) <= 1;
    leq_preservation_lemma((1 + eps) * real_div(0.5 * ((sqrx * sqrx) + (sqrx + b) * (sqrx + b)),(sqrx + b) * (sqrx + b)), 1, sqrx + b); 
    assert (1 + eps) * real_div(0.5 * ((sqrx * sqrx) + (sqrx + b) * (sqrx + b)),(sqrx + b) * (sqrx + b)) * (sqrx + b) <= sqrx + b;

    real_div_extraction_lemma(sqrx + b, 0.5 * ((sqrx * sqrx) + (sqrx + b) * (sqrx + b)),(sqrx + b) * (sqrx + b));
    real_div_elimination_lemma(sqrx + b, 0.5 * ((sqrx * sqrx) + (sqrx + b) * (sqrx + b)),(sqrx + b));
    eq_preservation_lemma(real_div(0.5 * ((sqrx * sqrx) + (sqrx + b) * (sqrx + b)),(sqrx + b) * (sqrx + b)) * (sqrx + b), real_div(0.5 * ((sqrx * sqrx) + (sqrx + b) * (sqrx + b)),sqrx + b), (1 + eps));
    assert (1 + eps) * (real_div(0.5 * ((sqrx * sqrx) + (sqrx + b) * (sqrx + b)),(sqrx + b) * (sqrx + b)) * (sqrx + b)) == (1 + eps) * real_div(0.5 * ((sqrx * sqrx) + (sqrx + b) * (sqrx + b)), sqrx + b);
    associativity_lemma((1 + eps),real_div(0.5 * ((sqrx * sqrx) + (sqrx + b) * (sqrx + b)),(sqrx + b) * (sqrx + b)),(sqrx + b));
    assert (1 + eps) * (real_div(0.5 * ((sqrx * sqrx) + (sqrx + b) * (sqrx + b)),(sqrx + b) * (sqrx + b)) * (sqrx + b)) == (1 + eps) * real_div(0.5 * ((sqrx * sqrx) + (sqrx + b) * (sqrx + b)),(sqrx + b) * (sqrx + b)) * (sqrx + b);
    assert (1 + eps) * real_div(0.5 * ((sqrx * sqrx) + (sqrx + b) * (sqrx + b)), sqrx + b) <= sqrx + b;
    assert (sqrx + b) * (sqrx + b) == sqrx * sqrx + 2 * sqrx * b + b*b;
    assert (1 + eps) * real_div(0.5 * (sqrx * sqrx + sqrx * sqrx + 2 * sqrx * b + b*b), sqrx + b) <= sqrx + b;
    assert (1 + eps) * real_div(sqrx * (sqrx + b) + 0.5 *  b*b, sqrx + b) <= sqrx + b;
    real_div_sum_lemma(sqrx * (sqrx + b),0.5 *  b*b, sqrx + b);
    eq_preservation_lemma(real_div(sqrx * (sqrx + b) + 0.5 *  b*b, sqrx + b), real_div(sqrx * (sqrx + b),sqrx + b) + real_div(0.5 *  b*b, sqrx + b), 1 + eps);
    assert (1 + eps) * real_div(sqrx * (sqrx + b) + 0.5 *  b*b, sqrx + b) == (1 + eps) * ((real_div(sqrx * (sqrx + b),sqrx + b) + real_div(0.5 *  b*b, sqrx + b)));
    assert (1 + eps) * (real_div(sqrx * (sqrx + b),sqrx + b) + real_div(0.5 *  b*b, sqrx + b)) <= sqrx + b;
    real_div_extraction_lemma(0.5, b*b, sqrx + b);
    real_div_elimination_lemma(sqrx + b, sqrx, 1);
    real_div_lemma(sqrx, 1, real_div(sqrx,1));
    eq_preservation_lemma(sqrx + real_div(b * b, sqrx + b) / 2,sqrx + real_div(0.5 *  b*b, sqrx + b), 1 + eps);
    assert (1 + eps) * (sqrx + real_div(b * b, sqrx + b) / 2 )== (1 + eps) *( sqrx + real_div(0.5 *  b*b, sqrx + b));
    assert (1 + eps) * (sqrx + real_div(b * b, sqrx + b) / 2) <= sqrx + b;
    assert (sqrx + real_div(b * b, sqrx + b) / 2) * (1 + eps) <= sqrx + b;
    eq_preservation_lemma(nrre, sqrx + real_div(b * b, sqrx + b) / 2, 1 + eps);
    assert nrre * (1 + eps) <= sqrx + b;
    }

lemma void overestimation_lemma2(real orr, real sqrx, real rx, real ordiv, real eps);
    requires orr <= 0.999999 * sqrx &*&
    rx == orr * ordiv &*&
    sqrx * sqrx == rx &*&
    eps > 0 &*&
    eps < 4.9e-13 &*&
    sqrx > 0;
    ensures (1 + eps) * (orr + ordiv) / 2 <= orr &*&
    (1 - eps) * (orr + ordiv) / 2 >=  sqrx;

    
lemma void lemma3(real rr, real nrr, real sqrx)
    requires rr - nrr >= 1e-14*nrr &*&
    sqrx > 0 &*&
    nrr >= sqrx;
    ensures real_ceiling(real_div(rr,sqrx)*1e14) > real_ceiling(real_div(nrr,sqrx)*1e14) &*&
    real_ceiling(real_div(nrr,sqrx)*1e14) >= 0;
    {
    real c = rr - nrr;
    assert c >= 1e-14*nrr;
    real_div_sum_lemma(nrr,c,sqrx);
    assert real_div(rr,sqrx) == real_div(nrr, sqrx) + real_div(c,sqrx);
        
    real_div_subs_lemma(1e-14*nrr,c,sqrx);
    assert real_div(c,sqrx) >= real_div(1e-14*nrr,sqrx);
    real_div_extraction_lemma(1e-14,nrr,sqrx);
    assert real_div(c,sqrx) >= 1e-14*real_div(nrr,sqrx);
    real_div_geq1(nrr,sqrx);
    assert real_div(nrr,sqrx) >= 1;
    assert real_div(c,sqrx) >= 1e-14;
       
    real_ceiling_gt_lemma(real_div(rr,sqrx)*1e14,real_div(nrr,sqrx)*1e14);
    assert real_ceiling(real_div(rr,sqrx)*1e14) > real_ceiling(real_div(nrr,sqrx)*1e14);
        
    real_ceiling_pos_lemma(real_div(nrr,sqrx)*1e14);
    assert real_ceiling(real_div(nrr,sqrx)*1e14) >= 0;
    }

lemma void error_lemma(real orr, real ordiv, real rx, real nrr, real rsum, real rlr)
    requires rx > 0 &*&
    orr > 0 &*&
    relative_error(real_div(rx,orr), ordiv, long_double_eps) == true &*&
    relative_error(orr + ordiv, rsum, long_double_eps) == true &*&
    relative_error(real_div(rsum,2), rlr, long_double_eps) == true &*&
    relative_error(rlr,nrr, double_eps) == true;
    ensures relative_error((orr + real_div(rx,orr)) / 2,nrr,(1 + ld_eps) * (1 + ld_eps) * (1 + ld_eps) * (1 + d_eps) - 1) == true;
    {
    real_div_lemma2(orr + ordiv,2, (orr + ordiv)/2);
    real_div_lemma2(rsum,2,rsum/2);
    real_div_pos_lemma(rx,orr);
    real_div_lemma2((orr + ordiv)*(1 + ld_eps),2,(orr + ordiv)*(1 + ld_eps)/2);  
    real_div_lemma2(orr + real_div(rx,orr)*(1 + ld_eps),2,(orr + real_div(rx,orr)*(1 + ld_eps))/2);
    real_div_lemma2(orr*(1 + ld_eps) + real_div(rx,orr)*(1 + ld_eps),2,(orr*(1 + ld_eps) + real_div(rx,orr)*(1 + ld_eps))/2);    
    real_div_extraction_lemma((1 + long_double_eps), orr + real_div(rx,orr),2);
    assert nrr <= ((orr + real_div(rx,orr)) / 2) * (1 + long_double_eps) * (1 + long_double_eps) * (1 + long_double_eps) * (1 + double_eps);
    
    /*
    assert nrr >= (rsum / 2) * (1 - ld_eps) * (1 - d_eps);
    assert nrr >= ((orr + ordiv) / 2) * (1 - ld_eps) * (1 - ld_eps) * (1 - d_eps);
    assert nrr >= ((orr + real_div(rx,orr) * (1 - ld_eps)) / 2) * (1 - ld_eps) * (1 - ld_eps) * (1 - d_eps);
    assert nrr >= ((orr + real_div(rx,orr)) / 2) * (1 - ld_eps) * (1 - ld_eps) * (1 - ld_eps) * (1 - d_eps);
    assert (orr + real_div(rx,orr)) / 2 > 0;
    assert nrr <= ((orr + real_div(rx,orr)) / 2) + ((orr + real_div(rx,orr)) / 2) * ((1 + ld_eps) * (1 + ld_eps) * (1 + ld_eps) * (1 + d_eps) - 1);
    */
    //assert ((orr + real_div(rx,orr)) / 2) * ((1 + ld_eps) * (1 + ld_eps) * (1 + ld_eps) * (1 + d_eps) - 1) >= 0;
    assert nrr >= ((orr + real_div(rx,orr)) / 2) - real_abs(((orr + real_div(rx,orr)) / 2) * ((1 + ld_eps) * (1 + ld_eps) * (1 + ld_eps) * (1 + d_eps) - 1));
    assert relative_error((orr + real_div(rx,orr)) / 2 , nrr, ((1 + ld_eps) * (1 + ld_eps) * (1 + ld_eps) * (1 + d_eps) - 1)) == true;
    }
    
lemma void stop_condition_lemma(real ra, real ru, real rl, real rct1, real rct2, real nrr, real rx);
    requires ra <= ru &*&
    ra >= rl &*&
    rx > 0 &*&
    relative_error(nrr * nrr, ra, double_eps) == true &*&
    relative_error(0.99999, rct2, d_eps) == true &*&
    relative_error(1.00001, rct1, d_eps) == true &*&
    relative_error(rx * rct2, rl , d_eps) == true &*&
    relative_error(rx * rct1, ru , d_eps) == true;
    ensures relative_error(real_sqrt(rx), nrr, 0.00001) == true;
/*{
        
        product_sign_lemma(rx,rct2);
        assert rl >= rx * rct2 * (1 - d_eps);
        assert rct2 >= 0.99999*(1-d_eps);
        assert rx * (1 - d_eps) > 0;
        leq_preservation_lemma(0.99999 * (1-d_eps), rct2, rx * (1 - d_eps));
        assert rct2 * rx * (1-d_eps) >= 0.99999*(1-d_eps) * rx * (1 - d_eps);
        leq_transitivity_lemma(rx * 0.99999 * (1 - d_eps) * (1 - d_eps),rx * rct2 * (1 - d_eps),rl);
        assert rl >= rx * 0.99999 * (1 - d_eps) * (1 - d_eps);
        product_sign_lemma(rx,rct1);
        assert ru <= rx * rct1 * (1 + d_eps);
        assert rct1 <= 1.00001 * (1 + d_eps);
        leq_preservation_lemma(rct1, 1.00001 * (1 + d_eps),rx * (1 + d_eps));
	assert ru <= rx * 1.00001 * (1 + d_eps) * (1 + d_eps);
        
	assert ra <= nrr * nrr * (1 + double_eps);
	assert ra >= nrr * nrr * (1 - double_eps);
	assert ra / 1.0000000000000002220446 <= nrr * nrr; // 1 + double_eps
	assert ra / 0.9999999999999997779554 >= nrr * nrr; // 1 - double_eps;
	sqrt_congruence_lemma(ra / 1.0000000000000002220446, nrr * nrr);
	sqrt_congruence_lemma(nrr * nrr, ra / 0.9999999999999997779554);
	real_sqrt_lemma(nrr*nrr,nrr);
	assert nrr >= real_sqrt(ra / 1.0000000000000002220446);
	assert nrr <= real_sqrt(ra / 0.9999999999999997779554);
	sqrt_congruence_lemma(rl / 1.0000000000000002220446, ra / 1.0000000000000002220446);
	sqrt_congruence_lemma(ra / 0.9999999999999997779554, ru / 0.9999999999999997779554);
	assert nrr >= real_sqrt(rl / 1.0000000000000002220446);
	assert nrr <= real_sqrt(ru / 0.9999999999999997779554);
	sqrt_congruence_lemma(rx * 0.99999 * (1 - d_eps) * (1 - d_eps) / 1.0000000000000002220446, rl / 1.0000000000000002220446);
	assert nrr >= real_sqrt(rx * 0.99999 * (1 - d_eps) * (1 - d_eps) / 1.0000000000000002220446);
	sqrt_congruence_lemma(ru / 0.9999999999999997779554,rx * 1.00001 * (1 + d_eps) * (1 + d_eps) / 0.9999999999999997779554);
	assert nrr <= real_sqrt(rx * 1.00001 * (1 + d_eps) * (1 + d_eps) / 0.9999999999999997779554);
	sqrt_extraction_lemma(rx,1.00001 * (1 + d_eps) * (1 + d_eps) / 0.9999999999999997779554);
	sqrt_extraction_lemma(rx,0.99999 * (1 - d_eps) * (1 - d_eps) / 1.0000000000000002220446);	
	assert nrr <= real_sqrt(rx) * real_sqrt(1.00001 * (1 + d_eps) * (1 + d_eps) / 0.9999999999999997779554);
	assert nrr >= real_sqrt(rx) * real_sqrt(0.99999 * (1 - d_eps) * (1 - d_eps) / 1.0000000000000002220446);	
	sqrt_congruence_lemma(0.99999*0.99999, 0.99999 * (1 - d_eps) * (1 - d_eps) / 1.0000000000000002220446);
	real_sqrt_lemma(0.99999*0.99999,0.99999);
	sqrt_congruence_lemma(1.00001 * (1 + d_eps) * (1 + d_eps) / 0.9999999999999997779554, 1.00001*1.00001);
	real_sqrt_lemma(1.00001*1.00001,1.00001);
	assert real_sqrt(1.00001 * (1 + d_eps) * (1 + d_eps) / 0.9999999999999997779554) <= 1.00001;
	assert real_sqrt(0.99999 * (1 - d_eps) * (1 - d_eps) / 1.0000000000000002220446) >= 0.99999;
	sqrt_pos_lemma(rx);
        leq_preservation_lemma(real_sqrt(1.00001 * (1 + d_eps) * (1 + d_eps) / 0.9999999999999997779554),1.00001,real_sqrt(rx));
	assert real_sqrt(1.00001 * (1 + d_eps) * (1 + d_eps) / 0.9999999999999997779554) * real_sqrt(rx) <= 1.00001 * real_sqrt(rx);

        leq_preservation_lemma(0.99999,real_sqrt(0.99999 * (1 - d_eps) * (1 - d_eps) / 1.0000000000000002220446),real_sqrt(rx));
	assert nrr <= real_sqrt(rx) * 1.00001;
	assert nrr >= real_sqrt(rx) * 0.99999;
	assert relative_error(real_sqrt(rx), nrr, 0.00001) == true;
}*/

lemma void not_stop_condition_lemma(real ra, real ru, real rl, real rct1, real rct2, real nrr, real rx);
    requires ra > ru || ra < rl &*&
    rx > 0 &*&
    relative_error(nrr * nrr, ra, double_eps) == true &*&
    relative_error(0.99999, rct2, d_eps) == true &*&
    relative_error(1.00001, rct1, d_eps) == true &*&
    relative_error(rx * rct2, rl , d_eps) == true &*&
    relative_error(rx * rct1, ru , d_eps) == true;
    ensures nrr > real_sqrt(rx) * 1.000001 || nrr < real_sqrt(rx) * 0.999999;

@*/



#endif