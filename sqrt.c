#include <math.h>



float vector_size(float x, float y)
    //@ requires real_of_float(x) == some(?rx) &*& real_of_float(y) == some(?ry);
    //@ ensures real_of_float(result) == some(?rr) &*& rx == 0 && ry == 0 ? rr == 0 : 0 < rr &*& relative_error(real_vector_size(rx,ry),rr,0.0000100001) == true;
{
    //@ strict_product_sign_lemma(rx,rx);
    //@ strict_product_sign_lemma(ry,ry);
    double x2 = (double)x * x;
    double y2 = (double)y * y;
    double sum = x2 + y2;
    double sqrt = my_sqrt(sum);
    //double sqrt = my_sqrt((double)x * x + (double)y * y);
    //@ assert real_of_double(x2) == some(?rx2);
    //@ assert real_of_double(y2) == some(?ry2);
    //@ assert real_of_double(sum) == some(?rsum);
    //@ assert real_of_double(sqrt) == some(?rsqrt);

    //@ assert rx2 == rx * rx;
    //@ assert ry2 == ry * ry;
    //@ assert relative_error(rx2 + ry2,rsum,double_eps) == true;
    //@ assert rsum <= (rx2 + ry2)*(1 + double_eps);
    //@ sqrt_congruence_lemma(rsum, (rx2 + ry2)*(1 + double_eps)); // NODIG?
    //@ assert real_sqrt(rsum) <= real_sqrt((rx2 + ry2)*(1 + double_eps));
   
    //@ assert real_vector_size(rx,ry) == real_sqrt(rx2 + ry2);
    //@ sqrt_extraction_lemma(rx2 + ry2,1 + double_eps);
    //@ assert real_sqrt((rx2 + ry2)*(1 + double_eps)) == real_sqrt(rx2 + ry2)*real_sqrt(1 + double_eps);
    //@ assert real_sqrt(rsum) <= real_vector_size(rx,ry) * real_sqrt(1 + double_eps);
    //@ sqrt_congruence_lemma((rx2 + ry2)*(1-double_eps),rsum);
    //@ sqrt_extraction_lemma(rx2 + ry2,1 - double_eps);
    //@ assert real_sqrt(rsum) >= real_vector_size(rx,ry) * real_sqrt(1 - double_eps);
    /*@ if (rsum == 0) {
 	sqrt_zero_lemma(rsum);
        assert relative_error(real_sqrt(rsum),rsqrt,0.00001) == true;   
    
        
    } else {
	assert relative_error(real_sqrt(rsum),rsqrt,0.00001) == true;
	
	sqrt_pos_lemma(rx2 + ry2);    
        assert real_vector_size(rx,ry) != 0;
        
        real epsilon = (1 - real_sqrt(1 - double_eps) * 0.99999);
        real rvs = real_vector_size(rx,ry);
        //geq_substitution_lemma(rsqrt,real_vector_size(rx,ry) - real_vector_size(rx,ry) * (1 - real_sqrt(1 - double_eps) * 0.99999),real_vector_size(rx,ry) -  real_abs(real_vector_size(rx,ry) * (1 - real_sqrt(1 - double_eps) * 0.99999)));
	//leq_substitution_lemma(rsqrt, real_vector_size(rx,ry) + real_vector_size(rx,ry)*(1 - real_sqrt(1 - double_eps) * 0.99999), real_vector_size(rx,ry) + real_abs(real_vector_size(rx,ry)*(1 - real_sqrt(1 - double_eps) * 0.99999)));
	//assert rvs == 0 ? rsqrt == 0 : rsqrt <= real_abs(epsilon * rvs) + rvs && rsqrt >= rvs - real_abs(epsilon * rvs);
	//assert relative_error(rvs,rsqrt,epsilon) == true;
    } 
    @*/
    //@ assert real_sqrt(rsum) >= real_vector_size(rx,ry) * real_sqrt(1 - double_eps);
    
    //@ assert rsqrt >= real_sqrt(rsum) * 0.99999;
    //@ assert rsqrt >= real_vector_size(rx,ry) * real_sqrt(1 - double_eps) * 0.99999;
    //@ assert rsqrt >= real_vector_size(rx,ry) * (1 - (1 - real_sqrt(1 - double_eps) * 0.99999));
    //@ assert rsqrt >= real_vector_size(rx,ry) - real_vector_size(rx,ry) * (1 - real_sqrt(1 - double_eps) * 0.99999);
    
    //@ assert real_sqrt(rsum) <= real_vector_size(rx,ry) * real_sqrt(1 + double_eps);
    
    //@ assert rsqrt <= real_sqrt(rsum) * 1.00001;
    //@ assert rsqrt <= real_vector_size(rx,ry) * real_sqrt(1 + double_eps) * 1.00001;
    //@ assert rsqrt <= real_vector_size(rx,ry) * (1 - (1 - real_sqrt(1 + double_eps) * 1.00001));
    //@ assert rsqrt <= real_vector_size(rx,ry) - real_vector_size(rx,ry) * (1 - real_sqrt(1 + double_eps) * 1.00001);
    //@ assert rsqrt <= real_vector_size(rx,ry) + real_vector_size(rx,ry) * (real_sqrt(1 + double_eps) * 1.00001 - 1);
    
    //@ real_sqrt_lemma(0.0000100001*0.0000100001,0.0000100001);
    //@ assert real_sqrt(0.0000100001*0.0000100001) == 0.0000100001;
    //@ real_sqrt_lemma2(1 + double_eps,real_sqrt(1 + double_eps));
    //@ assert real_sqrt(1 + double_eps)*real_sqrt(1 + double_eps) == 1 + double_eps;
    
    //@ assert (1 + double_eps)*1.00001*1.00001 - 2 * 1.00001 + 1 <= 0.0000100001*0.0000100001;
    //@ sqrt_geq_one_lemma(1 + double_eps);
    //@ assert real_sqrt(1 + double_eps) >= 1;
    //@ assert (1 + double_eps)*1.00001*1.00001 - 2 * real_sqrt(1 + double_eps) * 1.00001 + 1 <= 0.0000100001*0.0000100001;
    
    //@ real_sqrt_lemma((1+ double_eps)*(1+double_eps),1 + double_eps);
    //@ sqrt_congruence_lemma(1 + double_eps, (1+ double_eps)*(1+double_eps));
    //@ assert real_sqrt(1 + double_eps) <= 1 + double_eps;
    //@ assert (1 + double_eps)*1.00001*1.00001 - 2 * real_sqrt(1 + double_eps) * 1.00001 + 1 >= 0;
    
    //@ assert (real_sqrt(1 + double_eps) * 1.00001 - 1)*(real_sqrt(1 + double_eps) * 1.00001 - 1) == real_sqrt(1 + double_eps) * real_sqrt(1 + double_eps)  * 1.00001 * 1.00001 - 2 * real_sqrt(1 + double_eps) * 1.00001 + 1;
    //@ assert real_sqrt(1 + double_eps) * 1.00001 * real_sqrt(1 + double_eps) * 1.00001 == (1 + double_eps)*1.00001*1.00001;
    //@ substitution_lemma((real_sqrt(1 + double_eps) * 1.00001 - 1)*(real_sqrt(1 + double_eps) * 1.00001 - 1),real_sqrt(1 + double_eps) * real_sqrt(1 + double_eps)  * 1.00001 * 1.00001, 1 - 2 * real_sqrt(1 + double_eps) * 1.00001,(1 + double_eps)*1.00001*1.00001);
    //@ assert (real_sqrt(1 + double_eps) * 1.00001 - 1)*(real_sqrt(1 + double_eps) * 1.00001 - 1) == (1 + double_eps)*1.00001*1.00001 - 2 * real_sqrt(1 + double_eps) * 1.00001 + 1;
    //@ real_sqrt_lemma((1 + double_eps)*1.00001*1.00001 - 2 * real_sqrt(1 + double_eps) * 1.00001 + 1, real_sqrt(1 + double_eps) * 1.00001 - 1);
    //@ assert real_sqrt((1 + double_eps)*1.00001*1.00001 - 2 * real_sqrt(1 + double_eps) * 1.00001 + 1) == real_sqrt(1 + double_eps) * 1.00001 - 1;
    //@ sqrt_congruence_lemma((1 + double_eps)*1.00001*1.00001 - 2 * real_sqrt(1 + double_eps) * 1.00001 + 1, 0.0000100001*0.0000100001);
    //@ assert (real_sqrt(1 + double_eps) * 1.00001 - 1) <= 0.0000100001;
    
    //@ assert (1 - double_eps)*0.99999*0.99999 - 2 * 0.99999 + 1 <= 0.00001*0.00001;
    //@ sqrt_congruence_lemma(0.999999999999999*0.999999999999999, 1-double_eps);
    //@ real_sqrt_lemma(0.999999999999999*0.999999999999999,0.999999999999999);
    //@ assert real_sqrt(1 - double_eps) >= 0.999999999999999;
    //@ assert (1 - double_eps)*0.99999*0.99999 - 2 * real_sqrt(1 - double_eps) * 0.99999 + 1 <= (1 - double_eps)*0.99999*0.99999 - 2 * 0.999999999999999 * 0.99999 + 1;
    //@ assert (1 - double_eps)*0.99999*0.99999 - 2 * 0.999999999999999 * 0.99999 + 1 <= 0.0000100001*0.0000100001;
    //@ assert (1 - double_eps)*0.99999*0.99999 - 2 * real_sqrt(1 - double_eps) * 0.99999 + 1 <= 0.0000100001*0.0000100001;
    
    //@ sqrt_leq_one_lemma(1 - double_eps);
    //@ assert (1 - double_eps)*0.99999*0.99999 - 2 * real_sqrt(1 - double_eps) * 0.99999 + 1 >= 0;
    
    //@ real_sqrt_lemma2(1 - double_eps,real_sqrt(1 - double_eps));
    //@ assert (1 - real_sqrt(1 - double_eps) * 0.99999)*(1 - real_sqrt(1 - double_eps) * 0.99999) == real_sqrt(1-double_eps)*real_sqrt(1-double_eps)*0.99999*0.99999 - 2 * real_sqrt(1 - double_eps) * 0.99999 + 1;
    //@ substitution_lemma((1 - real_sqrt(1 - double_eps) * 0.99999)*(1 - real_sqrt(1 - double_eps) * 0.99999),real_sqrt(1-double_eps)*real_sqrt(1-double_eps)*0.99999*0.99999, 1 - 2 * real_sqrt(1 - double_eps) * 0.99999,(1 - double_eps)*0.99999*0.99999);
    //@ real_sqrt_lemma((1 - double_eps)*0.99999*0.99999 - 2 * real_sqrt(1 - double_eps) * 0.99999 + 1,1 - real_sqrt(1 - double_eps) * 0.99999);
    //@ assert real_sqrt((1 - double_eps)*0.99999*0.99999 - 2 * real_sqrt(1 - double_eps) * 0.99999 + 1) == 1 - real_sqrt(1 - double_eps) * 0.99999;
    //@ sqrt_congruence_lemma((1 - double_eps)*0.99999*0.99999 - 2 * real_sqrt(1 - double_eps) * 0.99999 + 1, 0.0000100001*0.0000100001);    
    //@ assert (1 - real_sqrt(1 - double_eps) * 0.99999) <= 0.0000100001;
    
    
    //@ assert rsqrt <= real_vector_size(rx,ry) + real_vector_size(rx,ry) * (real_sqrt(1 + double_eps) * 1.00001 - 1);
    //@ product_substitution_lemma(real_vector_size(rx,ry),(real_sqrt(1 + double_eps) * 1.00001 - 1),0.0000100001);
    //@ assert real_vector_size(rx,ry) * (real_sqrt(1 + double_eps) * 1.00001 - 1) <= real_vector_size(rx,ry) * 0.0000100001;
    //@ assert rsqrt <= real_vector_size(rx,ry) + real_vector_size(rx,ry) * 0.0000100001;

    //@ assert rsqrt >= real_vector_size(rx,ry) - real_vector_size(rx,ry) * (1 - real_sqrt(1 - double_eps) * 0.99999);
    //@ product_substitution_lemma(real_vector_size(rx,ry),1 - real_sqrt(1 - double_eps) * 0.99999,0.0000100001);
    //@ assert rsqrt >= real_vector_size(rx,ry) - real_vector_size(rx,ry) * 0.0000100001;
    
    /*
    //@ sqrt_leq_one_lemma(1 - double_eps);
    //@ assert real_sqrt(1 - double_eps) <= 1;
    //@ assert real_sqrt(1 - double_eps) * 0.99999 <= 0.99999;
    //@ product_sign_lemma((1 - real_sqrt(1 - double_eps) * 0.99999),real_vector_size(rx,ry));
    //@ assert real_vector_size(rx,ry) * (1 - real_sqrt(1 - double_eps) * 0.99999) >= 0;
    //@ assert real_abs(real_vector_size(rx,ry) * (1 - real_sqrt(1 - double_eps) * 0.99999)) == real_vector_size(rx,ry) * (1 - real_sqrt(1 - double_eps) * 0.99999);
    //@ geq_substitution_lemma(rsqrt,real_vector_size(rx,ry) - real_vector_size(rx,ry) * (1 - real_sqrt(1 - double_eps) * 0.99999),real_vector_size(rx,ry) -  real_abs(real_vector_size(rx,ry) * (1 - real_sqrt(1 - double_eps) * 0.99999)));
    //@ assert rsqrt >= real_vector_size(rx,ry) - real_abs(real_vector_size(rx,ry) * (1 - real_sqrt(1 - double_eps) * 0.99999));
    
    //@ assert rsqrt <= real_vector_size(rx,ry) + real_vector_size(rx,ry) * (1 - real_sqrt(1 - double_eps) * 0.99999);
    //@ assert real_vector_size(rx,ry) + real_vector_size(rx,ry)*(1 - real_sqrt(1 - double_eps) * 0.99999) == real_vector_size(rx,ry) + real_abs(real_vector_size(rx,ry)*(1 - real_sqrt(1 - double_eps) * 0.99999));
    //@ assert rsqrt <= real_vector_size(rx,ry) + real_vector_size(rx,ry)*(1 - real_sqrt(1 - double_eps) * 0.99999);
    //@ leq_substitution_lemma(rsqrt, real_vector_size(rx,ry) + real_vector_size(rx,ry)*(1 - real_sqrt(1 - double_eps) * 0.99999), real_vector_size(rx,ry) + real_abs(real_vector_size(rx,ry)*(1 - real_sqrt(1 - double_eps) * 0.99999)));
    //@ assert rsqrt <= real_vector_size(rx,ry) + real_abs(real_vector_size(rx,ry)*(1 - real_sqrt(1 - double_eps) * 0.99999));


    //@ real epsilon = (1 - real_sqrt(1 - double_eps) * 0.99999);
    //@ real rvs = real_vector_size(rx,ry);
    //@ assert rsqrt <= real_abs(epsilon * rvs) + rvs && rsqrt >= rvs - real_abs(epsilon * rvs);
    // assert real_sqrt(1 - double_eps) <= 1;
    // assert real_sqrt(1 - double_eps) * 0.99999 <= 0.99999;
    // assert real_vector_size(rx,ry) >= 0;
    // assert real_vector_size(rx,ry) * real_sqrt(1 - double_eps) * 0.99999 <= real_vector_size(rx,ry) * 0.99999;
    // assert relative_error(rvs,rsqrt,epsilon) == true;

    */
    return (float) sqrt;
}


double my_sqrt(double x)
    //@ requires real_of_double(x) == some(?rx) &*& 0 <= rx;
    //@ ensures real_of_double(result) == some(?rr) &*& rx == 0 ? rr == 0 : 0 < rr &*& relative_error(real_sqrt(rx),rr,0.00001) == true;
    //@ terminates;
{
    if (x == 0.0) return 0.0;
    double result = 1.0;
    double oldResult = result;
    long double div = (long double) x / result;
    //@ real_of_int_lemma(2,2);
    result = (oldResult + div) / 2;
    //@ assert real_of_double(oldResult) == some(?orr1);
    //@ assert real_of_long_double(div) == some(?ordiv1);
    //@ real_sqrt_lemma(orr1 * orr1,orr1);   	    
    //@ real_div_lemma2(rx,orr1,ordiv1);
    //@ real sqrx = real_sqrt(rx);
    //@ real_sqrt_lemma2(rx,sqrx);
    //@ real_div_lemma2(rx,sqrx,sqrx);
    /*@ if (orr1 * orr1 >= rx) {
    	    
    	    sqrt_congruence_lemma(rx, orr1 * orr1);
    	    division_lemma(rx,sqrx,orr1);
    	    lemma1(orr1,ordiv1,rx,sqrx);
    	} else {
    	    strict_sqrt_congruence_lemma(orr1 * orr1, rx);
	    lemma2(orr1,ordiv1,rx,sqrx);
    	}
    @*/
    oldResult = result;
    div = (long double) x / result;
    result = (oldResult + div) / 2;
    //@ assert real_of_double(oldResult) == some(?orr2);
    //@ assert real_of_long_double(div) == some(?ordiv2);
    
    //@ lemma1(orr2,ordiv2,rx,sqrx);
    
    for (;;)
        /*@ invariant 
        real_of_double(result) == some(?rr) &*& 
        real_of_double(oldResult) == some(?orr) &*& 
	real_of_long_double(div) == some(?ordiv) &*&
        rr >= real_sqrt(rx) &*&
        rr - real_sqrt(rx) <= real_abs(real_sqrt(rx) - orr) &*&
        rr == (orr + ordiv)/2;
        @*/
        //@ decreases real_ceiling(real_div(rr,sqrx)*1000000);
    {
        oldResult = result;
        div = (long double)x / result;
        result = (result + div) / 2;
    	//@ assert real_of_long_double(div) == some(?rdiv);
    	//@ assert real_of_double(result) == some(?nrr);
    	//@ lemma1(rr,rdiv,rx,sqrx);
        double rDif = oldResult - result;
        if (rDif < 0.000004*result) {
            break;
        }
        //@ lemma3(rr,nrr,sqrx);
    }
    return result;
}