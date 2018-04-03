#include <math.h>



float vector_size(float x, float y)
    //@ requires real_of_float(x) == some(?rx) &*& real_of_float(y) == some(?ry);
    //@ ensures real_of_float(result) == some(?rr) &*& rx == 0 && ry == 0 ? rr == 0 : 0 < rr &*& relative_error(real_vector_size(rx,ry),rr,0.00001) == true;
{
    //@ strict_product_sign_lemma(rx,rx);
    //@ strict_product_sign_lemma(ry,ry);
    double sqrt = my_sqrt((double)x * x + (double)y * y);
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