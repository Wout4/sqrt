#include <math.h>


/*
float vector_size(float x, float y)
    //@ requires real_of_float(x) == some(?rx) &*& real_of_float(y) == some(?ry);
    //@ ensures real_of_float(result) == some(?rr) &*& rx == 0 && ry == 0 ? rr == 0 : 0 < rr &*& relative_error(real_vector_size(rx,ry),rr,0.0000102) == true;
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
    //@ sqrt_zero_lemma(0);

    //@ assert relative_error(rx * rx, rx2, double_eps) == true;
    //@ assert relative_error(ry * ry, ry2, double_eps) == true;
    //@ assert relative_error(rx2 + ry2,rsum,double_eps) == true;
    //@ assert relative_error(real_sqrt(rsum),rsqrt,0.00001) == true;

    //@ assert rx2 <= (rx * rx) * (1 + double_eps);
    //@ assert ry2 <= (ry * ry) * (1 + double_eps);
    //@ assert rsum <= (rx2 + ry2)*(1 + double_eps);
    //@ assert rsqrt <= real_sqrt(rsum)*1.00001;
    
    //@ assert rsum <= (1 + double_eps) * (1 + double_eps) * (rx * rx + ry * ry);
    //@ real_sqrt_lemma((1 + double_eps) * (1 + double_eps), (1 + double_eps));
    //@ sqrt_extraction_lemma((1 + double_eps) * (1 + double_eps),(rx * rx + ry * ry));
    //@ sqrt_congruence_lemma(rsum, (1 + double_eps) * (1 + double_eps) * (rx * rx + ry * ry));
    //@ assert real_sqrt(rsum) <= (1 + double_eps) * real_vector_size(rx, ry);
    //@ assert rsqrt <= 1.00001 * (1 + double_eps) * real_vector_size(rx, ry);
        
    //@ assert rx2 >= (rx * rx) * (1 - double_eps);
    //@ assert ry2 >= (ry * ry) * (1 - double_eps);
    //@ assert rsum >= (rx2 + ry2) * (1 - double_eps);
    //@ assert rsqrt >= real_sqrt(rsum)*0.99999;
    
    //@ assert rsum >= (1 - double_eps) * (1 - double_eps) * (rx * rx + ry * ry);
    //@ real_sqrt_lemma((1 - double_eps) * (1 - double_eps), (1 - double_eps));
    //@ sqrt_extraction_lemma((1 - double_eps) * (1 - double_eps),(rx * rx + ry * ry));
    //@ sqrt_congruence_lemma((1 - double_eps) * (1 - double_eps) * (rx * rx + ry * ry), rsum);
    //@ assert real_sqrt(rsum) >= real_vector_size(rx,ry) * (1 - double_eps);
    //@ assert rsqrt >= real_vector_size(rx,ry) * (1 - double_eps) * 0.99999;

    //@ assert rsqrt >= real_vector_size(rx,ry) - real_vector_size(rx,ry) * (1 - (1 - double_eps) * 0.99999);
    //@ assert rsqrt <= real_vector_size(rx,ry) + real_vector_size(rx,ry) * ((1 + double_eps) * 1.00001 - 1);
    //@ assert rsqrt >= real_vector_size(rx,ry) - real_vector_size(rx,ry) * 0.0000100001;
    //@ assert rsqrt <= real_vector_size(rx,ry) + real_vector_size(rx,ry) * 0.0000100001;
   
    return (float) sqrt;
}
*/

double next(double r, double x)
    /*@ requires real_of_double(x) == some(?rx) &*& 
    0 < rx &*&
    real_of_double(r) == some(?rr) &*&
    rr > 0;
    @*/
    /*@ ensures real_of_double(result) == some(?rresult) &*& 
    rresult > 0 &*& 
    relative_error((rr + real_div(rx,rr)) / 2,rresult,(1 + ld_eps) * (1 + ld_eps) * (1 + ld_eps) * (1 + d_eps) - 1) == true;
    @*/
    //@ terminates;
{
    //@ real_of_int_lemma(2,2);
    double oldResult = r;
    long double div = (long double) x / r;
    long double sum = oldResult + div;
    long double longResult = (sum) / 2;
    double result = (double) longResult;
    return result;
    //@ assert real_of_double(oldResult) == some(?orr1);
    //@ assert real_of_long_double(div) == some(?ordiv1);
    //@ assert real_of_double(result) == some(?nrr1);
    //@ assert real_of_long_double(sum) == some(?rsum);
    //@ assert real_of_long_double(longResult) == some(?rlr);
    //@ real nrre = (orr1 + real_div(rx,orr1)) / 2;
    //@ real sqrx = real_sqrt(rx);
    //@ real_sqrt_lemma2(rx,sqrx);
    //@ real_div_lemma2(rx,sqrx,sqrx);
    //@ sqrt_pos_lemma(rx);
    //@ error_lemma(orr1, ordiv1, rx, nrr1, rsum, rlr);
    //@ real eps = (1 + ld_eps) * (1 + ld_eps) * (1 + ld_eps) * (1 + d_eps) - 1;
    //@ assert relative_error((orr1 + real_div(rx,orr1)) / 2,nrr1,eps) == true;
    //@ real_sqrt_lemma(orr1 * orr1,orr1);   	    

    
    //@ assert rx >= 0;
    //@ assert orr1 > 0;
    //@ real_div_pos_lemma(rx,orr1);
    //@ assert real_div(rx,orr1) >= 0;
    //@ assert ordiv1 >= 0;
    //@ assert ordiv1 + orr1 > 0;
    //@ assert rsum >= ordiv1 + orr1 - (ordiv1 + orr1) * d_eps;
    //@ assert ordiv1 + orr1 > (ordiv1 + orr1) * d_eps;
    //@ assert ordiv1 + orr1 - (ordiv1 + orr1) * d_eps > 0;
    /*@ if (rsum == ordiv1 + orr1 - (ordiv1 + orr1) * d_eps){
    	    
    } else {

    }
    
    @*/ 
    //@ assert rsum > 0;
    /*@ if (rlr == rsum - rsum * d_eps){

    } else {

    }
    
    @*/ 
    //@ assert rlr > 0;
    /*@ if (nrr1 == rlr - rlr * d_eps){

    } else {

    }
    
    @*/ 
    //@ assert nrr1 > 0;
}

bool test(double r, double x)
    /*@ requires real_of_double(r) == some(?rr) &*& 
    real_of_double(x) == some(?rx) &*&
    rr > 0 &*&
    rx > 0;
    @*/
    //@ ensures result == true ? relative_error(real_sqrt(rx), rr, 0.00001) == true : rr > real_sqrt(rx) * 1.000001 || rr < real_sqrt(rx) * 0.999999;
    //@ terminates;
{
    double a = r * r;
    double ct1 = 1.00001;
    double ct2 = 0.99999;
    double u = ct1 * x;
    double l = ct2 * x;
    //@ assert real_of_double(a) == some(?ra);
    //@ assert real_of_double(u) == some(?ru);
    //@ assert real_of_double(l) == some(?rl);
    //@ assert real_of_double(ct1) == some(?rct1);
    //@ assert real_of_double(ct2) == some(?rct2);
    if (a <= u && a >= l) {
        return true;

    //@ stop_condition_lemma(ra,ru,rl,rct1,rct2,rr,rx);
    }
    //@ not_stop_condition_lemma(ra,ru,rl,rct1,rct2,rr,rx);
    return false;
}



double my_sqrt(double x)
    //@ requires real_of_double(x) == some(?rx) &*& 0 <= rx;
    //@ ensures real_of_double(result) == some(?rr) &*& rx == 0 ? rr == 0 : 0 < rr &*& relative_error(real_sqrt(rx),rr,0.00001) == true;
    //@ terminates;
{
    if (x == 0.0) return 0.0;
    //@ real_of_int_lemma(1,1);
    double result = 1;  
    //@ assert real_of_double(result) == some(?nrr0);
    if (test(result,x)) {
        return result;
    }
    //@ assert nrr0 > real_sqrt(rx) * 1.000001 || nrr0 < real_sqrt(rx) * 0.999999;
    
    double oldResult = result;
    result = next(oldResult,x);
    //@ assert real_of_double(oldResult) == some(?orr1);
    //@ assert real_of_double(result) == some(?nrr1);
    //@ real eps = (1 + ld_eps) * (1 + ld_eps) * (1 + ld_eps) * (1 + d_eps) - 1;
    //@ real_sqrt_lemma(orr1 * orr1,orr1);   	    
    //@ real sqrx = real_sqrt(rx);
    //@ real_sqrt_lemma2(rx,sqrx);
    //@ real_div_lemma2(rx,sqrx,sqrx);
    /*@ if (orr1 * orr1 >= rx) {
    	    sqrt_congruence_lemma(rx, orr1 * orr1);
    	    division_lemma(rx,sqrx,orr1);
    	    real_div_lemma(rx,orr1,real_div(rx,orr1));
     	    overestimation_lemma1(orr1,sqrx,rx, real_div(rx,orr1), eps);
    	    assert nrr1 >= sqrx;
    	} else {
    	    sqrt_congruence_lemma(orr1 * orr1, rx);
    	    assert orr1 <= 0.999999 * sqrx;
	    real_div_lemma(rx,orr1,real_div(rx,orr1));
    	    overestimation_lemma2(orr1,sqrx,rx,real_div(rx,orr1),eps);
    	}
    @*/
    if (test(result,x)) {
        return result;
    }
    
    oldResult = result;
    result = next(oldResult,x);
    //@ assert real_of_double(oldResult) == some(?orr2);
    //@ assert real_of_double(result) == some(?nrr2);
    //@ real_div_lemma(rx, orr2, real_div(rx,orr2));
    //@ overestimation_lemma1(orr2,sqrx,rx, real_div(rx,orr2), eps);
    //@ assert nrr2 >= sqrx;
    
    for (;;)
        /*@ invariant 
        real_of_double(result) == some(?rr) &*& 
        real_of_double(oldResult) == some(?orr) &*& 
        rr >= real_sqrt(rx) &*&
        rr - real_sqrt(rx) <= real_abs(real_sqrt(rx) - orr) &*&
        relative_error((orr + real_div(rx,orr))/2,rr, eps) == true;
        @*/
        //@ decreases real_ceiling(real_div(rr,sqrx)*1e14);
    {
    
    	if (test(result,x)) {
            break;
    	}
 	oldResult = result;
    	result = next(oldResult,x);
    	//@ assert real_of_double(oldResult) == some(?orr3);
    	//@ assert real_of_double(result) == some(?nrr3);
    	//@ real_div_lemma(rx, orr3, real_div(rx,orr3));
    	//@ overestimation_lemma1(orr3, sqrx, rx, real_div(rx,orr3), 1e-13);

        //@ lemma3(orr3,nrr3,sqrx);
    }
    return result;
}

