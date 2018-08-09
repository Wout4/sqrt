#include <exact_math.h>

/* 
double test(double x, double y)
    //@ requires real_of_double(x) == some(?rx) &*& 0 <= rx &*& real_of_double(y) == some(?ry);
    //@ ensures real_of_double(result) == some(?rr) &*& rr == (rx * rx + ry * ry) &*& rr >= 0 &*& rx == 0 && ry == 0 ? rr == 0 : 0 < rr; //&*& rr > 0.9 * (rx + ry);
    //@ terminates;
    {
    	//@strict_product_sign_lemma(rx,rx);
    	//@strict_product_sign_lemma(ry,ry);
    	return y * y + x * x;
    }
    
    
double som(double x, double y)
    //@ requires real_of_double(x) == some(?rx) &*& 0 <= rx &*& real_of_double(y) == some(?ry) &*& 0 <= ry;
    //@ ensures real_of_double(result) == some(?rr) &*& rr == (rx + ry) &*& rr >= 0;
    //@ terminates;
    {
    	return x + y;
    }
    
double product(double x, double y)
    //@ requires real_of_double(x) == some(?rx) &*& 0 >= rx &*& real_of_double(y) == some(?ry) &*& 0 >= ry;
    //@ ensures real_of_double(result) == some(?rr) &*& rr == (rx * ry) &*& rr >= 0;
    //@ terminates;
    {

    	return x * y;
    	//@product_sign_lemma(rx,ry);
    }
    
double power(double x)
    //@ requires real_of_double(x) == some(?rx) &*& 0 >= rx;
    //@ ensures real_of_double(result) == some(?rr) &*& rr == (rx * rx) &*& rr >= 0;
    //@ terminates;
    {

    	return x * x;
    	//@product_sign_lemma(rx,rx);
    }
    
int ceiling_test(double x)
    //@requires real_of_double(x) == some(?rx) &*& rx <= 1 && rx > 0 &*& real_of_int(1) == 1;
    //@ensures result == real_ceiling(rx);
    //@terminates;
    {
    	//@real_ceiling_lemma(rx,1);
   	return 1;
    }
*/
/*  
int ceiling_test2(double x)
    //@requires real_of_double(x) == some(?rx) &*& rx > 0 &*& real_of_int(0) == 0;
    //@ensures result == real_ceiling(rx);
    {
    	int result;
    	result = 0;
    	double r = x;
    	//@real_of_int_lemma(-1,-1.0); //nodig om in het begin te weten wat real_of_int(old_result) is
    	while (r > 0.0)
    	/*@ 
    	invariant
    	    real_of_double(r) == some(?rr) &*&
    	    some(real_of_int(result)) == some(?rres) &*&
    	    rr + rres == rx &*&
    	    rr > -1.0;
    	@*/
    	/* 
    	{
    	    double old_r = r;
    	    r = r - 1.0;
    	    int old_result = result;
    	    result = result + 1;
    	    //@real_of_int_lemma(1,1); //anders werkt int_add_lemma niet
       	    //@int_add_lemma(old_result, 1, result);
    	}
    	//rr_lemma(rr); //na de loop is -1 < r <= 0, verifast weet dit niet
    	//@real_ceiling_lemma(rx,result);
    	return result;
    }
*/   
/*     
double sqrt_lemma_test(double x)
    //@requires real_of_double(x) == some(?rx);
    //@ensures real_of_double(result) == some(?rr) &*& rx == 16 ? rr == real_sqrt(rx) : true;
    //@terminates;
    {
    	//@real_sqrt_lemma(16,4);
   	return 4.0;
    }
    
    
    
double neutral_element_test(double x)
    //@requires real_of_double(x) == some(?rx);
    //@ensures real_of_double(result) == some(?rr) &*& rr == rx;
    //@terminates;
    {
    	return x + 0.0;
    }
    
  */ 
double loop_test(double x)
    //@requires real_of_double(x) == some(?rx);
    //@ensures real_of_double(result) == some(?rr) &*& rr == 5;
    //@terminates;
{
    int i = 0;
    double result = 5.0;
    while (i < 7)
    //@ invariant real_of_double(result) == some(?rr) &*& rr == 5;
    //@ decreases 10-i;
    {
        i = i + 1;
        result = result + 0.0;
    }
    return result;
}
    
/*
double division_test(double x, double y)
    //@ requires real_of_double(x) == some(?rx) &*& rx > 0;
    //@ ensures true;
    {
    //@ real_of_int_lemma(1,1);
    //@ real_of_int_lemma(2,2);
    double result = 1;  
    double oldResult = result;
    long double div = (long double) x / result;

    long double sum = oldResult + div;
    long double longResult = (sum) / 2;
    result = (double) longResult;
    //@ assert real_of_double(oldResult) == some(?orr1);
    //@ assert real_of_long_double(div) == some(?ordiv1);
    //@ assert real_of_double(result) == some(?nrr1);
    //@ assert real_of_long_double(sum) == some(?rsum);
    //@ assert real_of_long_double(longResult) == some(?rlr);
    //@ real nrre1 = (orr1 + real_div(rx,orr1)) / 2;
    //@ assert relative_error(real_div(rx,orr1), ordiv1, long_double_eps) == true;
    //@ assert relative_error(orr1 + ordiv1, rsum, long_double_eps) == true;
    //@ real_div_lemma2(orr1 + ordiv1,2, (orr1 + ordiv1)/2);
    //@ assert (orr1 + ordiv1)/2 == real_div(orr1 + ordiv1,2);
    //@ assert relative_error(real_div(rsum,2), rlr, long_double_eps) == true;
    //@ assert relative_error(rlr,nrr1, double_eps) == true;
    
    //@ assert relative_error(real_div(rsum,2), nrr1, (1 + double_eps) * (1 + long_double_eps) - 1) == true;
    //@ real_div_lemma2(rsum,2,rsum/2);
    //@ real_div_pos_lemma(rx,orr1);
    //@ assert real_div(rx,orr1) >= 0;
    //@ assert ordiv1 >= 0;
    //@ assert rsum >= 0;
    //@ assert real_div(rsum,2) >= 0;
    
    //@ assert nrr1 <= real_div(rsum,2) * (1 + long_double_eps) * (1 + double_eps);
    //@ assert rsum <= (orr1 + ordiv1)*(1 + long_double_eps);
    //@ assert rsum / 2 <= (orr1 + ordiv1)*(1 + long_double_eps) / 2;
    //@ real_div_lemma2((orr1 + ordiv1)*(1 + long_double_eps),2,(orr1 + ordiv1)*(1 + long_double_eps)/2);    
    //@ assert real_div(rsum,2) <= real_div((orr1 + ordiv1)*(1 + long_double_eps),2);
    //@ assert nrr1 <= real_div(orr1 + ordiv1,2) * (1 + long_double_eps) * (1 + long_double_eps) * (1 + double_eps);
    //@ real_div_lemma2(orr1 + real_div(rx,orr1)*(1 + long_double_eps),2,(orr1 + real_div(rx,orr1)*(1 + long_double_eps))/2);
    //@ assert nrr1 <= real_div(orr1 + real_div(rx,orr1)*(1 + long_double_eps),2) * (1 + long_double_eps) * (1 + long_double_eps) * (1 + double_eps);
    //@ real_div_lemma2(orr1*(1 + long_double_eps) + real_div(rx,orr1)*(1 + long_double_eps),2,(orr1*(1 + long_double_eps) + real_div(rx,orr1)*(1 + long_double_eps))/2);    
    //@ assert nrr1 <= real_div(orr1*(1 + long_double_eps) + real_div(rx,orr1)*(1 + long_double_eps),2) * (1 + long_double_eps) * (1 + long_double_eps) * (1 + double_eps);
    //@ real_div_extraction_lemma((1 + long_double_eps), orr1 + real_div(rx,orr1),2);
    //@ assert nrr1 <= real_div(orr1 + real_div(rx,orr1),2) *(1 + long_double_eps) * (1 + long_double_eps) * (1 + long_double_eps) * (1 + double_eps);
    //@ assert nrr1 <= nrre1 *(1 + long_double_eps) * (1 + long_double_eps) * (1 + long_double_eps) * (1 + double_eps);
    
    

    
    //@ assert relative_error(real_div(orr1 + ordiv1,2),nrr1,(1 + double_eps) * (1 + long_double_eps) * (1 + long_double_eps) * (1 + long_double_eps) - 1) == true;
    
   
    //@ assert relative_error(nrre1,nrr1,1) == true;
    
    return x;
    }


/*
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
    @*/ /*
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
        @*/ /*
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

    */
    /*
double my_sqrt(double x)
    //@ requires real_of_double(x) == some(?rx) &*& 0 <= rx;
    //@ ensures true;
    //@ terminates;
{
    if (x == 0.0) return 0.0;
    //@ real_of_int_lemma(1,1);
    //@ real_of_int_lemma(2,2);
    double result = 1;  
    //@ assert real_of_double(result) == some(?nrr1);
    double a = result * result;
    double ct1 = 1.00001;
    double ct2 = 0.99999;
    double u = ct1 * x;
    double l = ct2 * x;
    if (a <= u && a >= l) {
        return result;
        //@ assert real_of_double(a) == some(?ra);
        //@ assert real_of_double(u) == some(?ru);
        //@ assert real_of_double(l) == some(?rl);
        //@ assert real_of_double(ct1) == some(?rct1);
        //@ assert real_of_double(ct2) == some(?rct2);
        //@ assert ra >= rl;
        //@ assert ra <= ru;
        //@ assert relative_error(rx * rct2, rl , d_eps) == true;
        //@ product_sign_lemma(rx,rct2);
        //@ assert rl >= rx * rct2 * (1 - d_eps);
        //@ assert rct2 >= 0.99999*(1-d_eps);
        //@ assert rx * (1 - d_eps) > 0;
        //@ leq_preservation_lemma(0.99999 * (1-d_eps), rct2, rx * (1 - d_eps));
        //@ assert rct2 * rx * (1-d_eps) >= 0.99999*(1-d_eps) * rx * (1 - d_eps);
        //@ assert rl >= rx * 0.99999 * (1 - d_eps) * (1 - d_eps);
    }
    return 0;
}
   */ 
    