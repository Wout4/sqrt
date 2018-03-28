#include <math.h>

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
    
   
double loop_test(double x)
    //@requires real_of_double(x) == some(?rx);
    //@ensures real_of_double(result) == some(?rr) &*& rr == 5;
    //@terminates;
    {
    	int i = 0;
    	double result = 5.0;
    	while (i < 7)
    	//@ invariant real_of_double(result) == some(?rr) &*& rr == 5 &*& i <= 9;
        //@ decreases 10-i;
        {
            i = i + 1;
            if (i >= 7) {
            	break;
            }
            result = result + 0.0;
        }
        return result;
    }
    

double substitution_test(double x)
    //@ requires real_of_double(x) == some(?rx);
    //@ ensures true;
    {
    	//@ real a;
    	//@ real b;
    	//@ real c;
    	//@ dummy_lemma(a,b,c);
    	//@ dummy_lemma2(rx, b - c);
    	
    	/*@
	if (rx > 1) {
	    assert real_abs(b - c) == b - c;
	    assert a - b <= b - c;
	    assert a - b <= real_abs(b - c);
	} else {}

    	@*/
/*    	return x + 1;
    }
*/
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
    //@ real_div_lemma2(rx,orr1,ordiv1);
    //@ real rr1 = (orr1 + ordiv1)/2;
    //@ real sqrx = real_sqrt(rx);
    //@ real_sqrt_lemma2(rx,sqrx);
    //@ real_div_lemma2(rx,sqrx,sqrx);
    /*@ if (orr1 * orr1 >= rx) {
    	    sqrt_congruence_lemma(rx, orr1 * orr1);
    	    real_sqrt_lemma(orr1 * orr1,orr1);   	    
    	    assert orr1 >= sqrx;
    	    division_lemma(rx,sqrx,orr1);
    	    assert real_div(rx,sqrx) >= real_div(rx,orr1);
    	    real_div_lemma2(rx,sqrx,sqrx);
    	    assert ordiv1 <= sqrx;
    	    
    	    real b = orr1 - sqrx;
    	    assert ordiv1 == real_div(rx,sqrx + b); // (1)
    	    real_div_sub_lemma(sqrx, b * sqrx, b + sqrx);
    	    assert ordiv1 == sqrx - real_div(b * sqrx, b + sqrx); // (3)
    	    real_div_sub_lemma(b, b * sqrx, b + sqrx);
    	    product_sign_lemma(b,b);
    	    real_div_pos_lemma(b * b, sqrx + b);
    	    assert b - real_div(b * sqrx, b + sqrx) >= 0; // (4)
    	    assert (rr1) >= sqrx;
    	} else {
    	    assert rx > orr1 * orr1;
    	    strict_sqrt_congruence_lemma(orr1 * orr1, rx);
	    real_sqrt_lemma(orr1 * orr1,orr1);  
    	    assert sqrx > orr1;
    	    real b = sqrx - orr1;
    	    assert ordiv1 == real_div(rx,sqrx - b); // (5)
    	    real_div_add_lemma(sqrx, b * sqrx, sqrx - b);
    	    assert ordiv1 == sqrx + real_div(b * sqrx, sqrx - b); // (7)
    	    real_div_sub_lemma(b, b * sqrx, b + sqrx);
    	    product_sign_lemma(b,b);
    	    real_div_pos_lemma(b * b, sqrx + b);
    	    assert b - real_div(b * sqrx, b + sqrx) >= 0; // (8)
    	    assert (rr1) >= sqrx;
    	    assert real_abs(sqrx - orr1) == sqrx - orr1;
    	    assert rr1 <= ordiv1;
    	    assert rr1 >= orr1;
    	}
    @*/
    oldResult = result;
    div = (long double) x / result;
    result = (oldResult + div) / 2;
    //@ assert real_of_double(oldResult) == some(?orr2);
    //@ assert real_of_long_double(div) == some(?ordiv2);
    //@ assert orr2 == rr1;
    //@ real_div_lemma2(rx,orr2,ordiv2);
    //@ real rr2 = (orr2 + ordiv2)/2;
    //@ real b1 = orr2 - sqrx;
    //@ assert ordiv2 == real_div(rx,sqrx + b1);
    //@ real_div_sub_lemma(sqrx, b1 * sqrx, b1 + sqrx);
    //@ assert ordiv2 == sqrx - real_div(b1 * sqrx, b1 + sqrx);
    //@ real_div_sub_lemma(b1, b1 * sqrx, b1 + sqrx);
    //@ product_sign_lemma(b1,b1);
    //@ real_div_pos_lemma(b1 * b1, sqrx + b1);
    //@ assert b1 - real_div(b1 * sqrx, b1 + sqrx) >= 0;
    //@ assert (rr2) >= sqrx;
    //@ product_sign_lemma(sqrx,b1);
    //@ assert sqrx * b1 >= 0;
    //@ real_div_pos_lemma(b1 * sqrx, b1 + sqrx);
    //@ assert real_div(b1 * sqrx, b1 + sqrx) >= 0;
    //@ assert ordiv2 <= sqrx;


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
        //@ real_of_int_lemma(2,2);
        div = (long double)x / result;
        result = (result + div) / 2;
    	//@ assert real_of_long_double(div) == some(?rdiv);
    	//@ assert real_of_double(result) == some(?nrr);
    	//@ real_div_lemma2(rx,rr,rdiv);
    	//@ assert nrr == (rr + rdiv)/2;
    	//@ real b2 = rr - sqrx;
    	//@ assert rdiv == real_div(rx,sqrx + b2);
    	//@ real_div_sub_lemma(sqrx, b2 * sqrx, b2 + sqrx);
    	//@ assert rdiv == sqrx - real_div(b2 * sqrx, b2 + sqrx);
    	//@ real_div_sub_lemma(b2, b2 * sqrx, b2 + sqrx);
    	//@ product_sign_lemma(b2,b2);
    	//@ real_div_pos_lemma(b2 * b2, sqrx + b2);
    	//@ assert b2 - real_div(b2 * sqrx, b2 + sqrx) >= 0;
    	//@ assert (nrr) >= sqrx;
    	//@ product_sign_lemma(sqrx,b2);
    	//@ assert sqrx * b2 >= 0;
    	//@ real_div_pos_lemma(b2 * sqrx, b2 + sqrx);
    	//@ assert real_div(b2 * sqrx, b2 + sqrx) >= 0;
    	//@ assert rdiv <= sqrx;
        
        //@ real nrre = (rr + rdiv) / 2;
        // substitution_lemma2(nrr, 1, rd, nrre); // nodig om te bewijzen dat nrr / nrre = 1 (rd = 1)
        // assert real_abs(real_div(nrr, nrre) - 1) < 0.0000001;
     
        
        double rDif = oldResult - result;
        if (rDif < 0.000004*result) {
            //@ assert real_abs(0.9999999 * nrre - rr)*0.9999999 < 0.000004*1.0000001*nrre + 0.0000001 * nrre;
            //@ assert real_abs(0.9999999 * nrre - rr)*0.9999999 < 0.000004*1.0000001*nrre*1.025;
            //@ assert real_abs(nrre - rr) < 0.000005*nrre;
            //@ assert sqrx <= rr;
            //@ assert nrre <= rr;
            //@ assert rr - nrre < 0.000005*nrre;
            //@ assert nrre - real_sqrt(rx) <= rr - nrre;
            //@ assert nrre - real_sqrt(rx) <= 0.0000075*real_sqrt(rx);
            //@ assert nrr - real_sqrt(rx) <= 0.00001*real_sqrt(rx);
            break;
        }
        //@ division_lemma2(nrr,rr,sqrx);
        //@ real c = rr - nrr;
        //@ assert c >= 0.000004*nrr; //zie if
        //@ equality_division_lemma(rr, nrr + c, sqrx);
        //@ real_div_sum_lemma(nrr,c,sqrx);
        //@ assert real_div(rr,sqrx) == real_div(nrr, sqrx) + real_div(c,sqrx);
        //@ real_div_geq1(nrr,sqrx);
        //@ assert real_div(nrr,sqrx) >= 1;
        
        //@ real_div_subs_lemma(0.000004*nrr,c,sqrx);
        //@ assert real_div(c,sqrx) >= real_div(0.000004*nrr,sqrx);
        //@ real_div_extraction_lemma(0.000004,nrr,sqrx);
        //@ assert real_div(c,sqrx) >= 0.000004*real_div(nrr,sqrx);
        //@ assert real_div(c,sqrx) >= 0.000004;
        
        //@ real c1 = real_div(rr,sqrx)*1000000 - real_div(nrr,sqrx)*1000000;
        //@ assert c1 >= 4;
        //@ real_ceiling_gt_lemma(real_div(rr,sqrx)*1000000,real_div(nrr,sqrx)*1000000);
        //@ assert real_ceiling(real_div(rr,sqrx)*1000000) > real_ceiling(real_div(nrr,sqrx)*1000000);
        
        //en positief:
        
        //@ assert real_div(nrr,sqrx) >= 0;
        //@ real_ceiling_pos_lemma(real_div(nrr,sqrx)*1000000);
        //@ assert real_ceiling(real_div(nrr,sqrx)*1000000) >= 0;
    }
    return result;
}

    
    
    