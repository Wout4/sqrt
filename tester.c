#include <math.h>
/*@


@*/
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
    
    
double my_sqrt(double x)
    //@ requires real_of_double(x) == some(?rx) &*& 0 <= rx;
    //@ ensures real_of_double(result) == some(?rr) &*& rx == 0 ? rr == 0 : 0 < rr &*& relative_error(real_sqrt(rx),rr,0.00001) == true;//rr < 1.00001 * real_sqrt(rx);
    //@ terminates;
{
    if (x == 0.0) return 0.0; // 0 ipv 0.0 geeft problemen (int >< real)
    double result = 1.0;
    double oldResult = result; // toegevoegd voor invariant
    long double div = (long double) x / result; // toegevoegd voor invariant 
    //@ real_of_int_lemma(2,2);
    result = (oldResult + div) / 2; // 1 iteratie buiten de lus om al aan invariant te kunnen voldoen
    //@ assert real_of_double(oldResult) == some(?orr);
    //@ assert real_of_long_double(div) == some(?ordiv);
    //@ real_div_lemma2(rx,orr,ordiv);
    //@ real orr2 = orr * orr;
    //@ real rr1 = (orr + ordiv)/2;
    //@ real rr2 = rr1 * rr1;
    /*@ if (orr * orr >= rx) {
    	    real orr2div = real_div(orr * orr, rx);
    	    real_div_lemma(orr2, rx, orr2div);
    	    assert ordiv * ordiv <= rx;
    	    sqrt_congruence_lemma(rx, orr2);
    	    real_sqrt_lemma(orr2,orr);
    	    sqrt_congruence_lemma(ordiv * ordiv, rx);
    	    real_sqrt_lemma(ordiv * ordiv,ordiv);
    	    assert real_sqrt(rx) <= orr;
    	    assert orr >= real_sqrt(rx);
    	    assert ordiv <= real_sqrt(rx);
    	    assert ordiv <= rr1;
    	    assert rr1 <= orr;
    	    rx > 1;   	// (1 + a)/2 < sqrt(a) <=> a > 1
    	    average_approximation_lemma(ordiv, orr, real_sqrt(rx));
    	    assert real_sqrt(rx) - ordiv  >= rr1 - real_sqrt(rx);
    	    assert real_abs(real_sqrt(rx) - rr1) <= real_abs(real_sqrt(rx) - orr);
    	    //assert rr1 * rr1 >= rx;
    	    
    	} else {
    	    strict_sqrt_congruence_lemma(rx,orr2);
    	    assert ordiv * ordiv > rx;
    	    assert ordiv <= real_sqrt(rx);
    	    assert orr < real_sqrt(rx) && ordiv > real_sqrt(rx);
    	    1 == 2;
    	}
    @*/
    //@ assert rr1 * rr1 >= rx;
    //@ assert (orr2 <= rx && ordiv*ordiv >= rx) || (orr2 > rx && ordiv*ordiv < rx);
    //@ real_sqrt_lemma2(rx,real_sqrt(rx)); // prep for next lemma
    //@ assert real_sqrt(rx) * real_sqrt(rx) == rx;

    
    for (;;)
        /*@ invariant real_of_double(result) == some(?rr) &*& 
        0 < rr &*& 
        rr >= real_sqrt(rx) &*&
        real_of_double(oldResult) == some(orr) &*& 
        rr - real_sqrt(rx) <= real_abs(real_sqrt(rx) - orr) &*&
        rr <= orr &*& // of rx < 1, zie else hierboven
        real_of_long_double(div) == some (ordiv) &*&
        //ordiv == real_div(rx,orr) &*&
        ordiv <= real_sqrt(rx) &*&
        rr == (orr + ordiv)/2;
        @*/ //toegevoegd: elke iteratie komt result dichter bij echte sqrt
        //@ decreases real_ceiling(real_abs(real_div(rr,real_sqrt(rx)) - 1)*100000); // *100000 ipv /0.00001, (/ verwacht double in de teller)
        
    {
        oldResult = result;
        //@ real_of_int_lemma(2,2);
        div = (long double)x / result;
        result = (result + div) / 2;
        //result = (result + (long double)x / result) / 2;
        
        // The (long double) cast above is probably not necessary. It is used here to keep the sum from "overflowing" in case of large x.
        // The sum can overflow if "overflowing" is defined as "the mathematical exact result is greater than the largest representable number".
        // However, it cannot overflow if "overflowing" is defined as "there is no representable number within the machine error range of the mathematical exact result."
        // (because if 1 <= rx then rr <= real_sqrt(rx), so if x == 2^1023 then result <= 2^511, so result + x/result <= result + x == x, roughly.
        // I would guess that, for correctness and portability, it is sufficient to avoid overflow in the second sense. But I'm not completely sure of that, so to be safe,
        // we avoid overflow in the first sense.
        //@ assert real_of_double(result) == some(?nrr);
        //@ assert real_abs(real_sqrt(rx) - rr) <= real_abs(real_sqrt(rx) - orr);
        //@ assert ordiv == real_div(rx,orr);
        //@ real_div_lemma2(rx,orr,real_div(rx,orr));
        //@ assert rr == (orr + ordiv) / 2;
        //@ assert real_of_long_double(div) == some(?rdiv);
        //@ real_div_lemma2(rx,rr,rdiv);
        //@ assert rdiv == real_div(rx,rr);
        //@ assert rx == rdiv * rr;
        // congruentie_lemma(nrr,rr,rdiv + rr); / nrr * rr == div * rr, maar nrr == div wordt niet afgeleid?? (result = (long double)x / result;)
        //@ assert 2 * nrr == rdiv + rr;
        //@ assert rdiv == 2 * nrr - rr;
        // substitution_lemma(rx, rdiv, 2 * nrr - rr, rr); // rx == rdiv * rr en rdiv == nrr - rr maar rx == (nrr -rr) *rr wordt niet afgeleid??
        //@ assert rx == (2 * nrr - rr) * rr;
     
        //@ real nrre = (rr + rdiv) / 2;
        //@ assert rx == (rr * (nrre*2 - rr));
        //@ assert rx == rr * (2 * nrr - rr);
        //assert rx == (rr * (nrr * 2 - rr));
        //@ assert nrr == nrre; //zonder afrondingsfouten
        //@ real rd = real_div(nrr, nrre);
        //@ real_div_lemma(nrr,nrre,rd);
        //@ assert nrr * 1 == nrre * rd;
        //@ substitution_lemma2(nrr, 1, rd, nrre); // nodig om te bewijzen dat nrr / nrre = 1 (rd = 1)
        //@ assert real_div(nrr, nrre) == 1;
        //@ assert real_abs(real_div(nrr, nrre) - 1) < 0.0000001; //error is 0 met exacte berekeningen
        //loop invariant:
        //@ assert rr >= real_sqrt(rx);
        //@ division_lemma(rx,real_sqrt(rx),rr);
        //@ assert real_div(rx,rr) <= real_div(rx,real_sqrt(rx));
        //@ real_div_lemma2(rx, real_sqrt(rx), real_sqrt(rx));
        //@ assert rdiv <= real_sqrt(rx);
        //@ real_div_lemma2(rr*rr, rr, rr);
        //@ assert nrr >= real_sqrt(rx);
        
       
        double rDif = fabs(result - oldResult);
        if (rDif < 0.000004*result) {
            //@ assert (0.999996 * nrr < rr && rr <= nrr) || (rr < 1.000004 * nrr && rr > nrr);
            //@ assert real_abs(0.9999999 * nrre - rr)*0.9999999 < 0.000004*1.0000001*nrre + 0.0000001 * nrre;
            //@ assert real_abs(0.9999999 * nrre - rr)*0.9999999 < 0.000004*1.0000001*nrre*1.025;
            // assert real_abs(0.9999999 * nrre - rr)*0.9999999 < 0.000004*1.0000001*nrre*1.0000001; klopt niet denk ik, zie hierboven
            //@ assert real_abs(nrre - rr) < 0.000005*nrre;
            //@ assert rx<= rr * rr;
            /*@
            if (real_sqrt(rx) <= rr) {
            	real_sqrt_lemma2(rx, real_sqrt(rx)); //mss niet nodig
            	assert rx <= rr * rr;
            	assert orr >= rr;
            	assert ordiv <= real_sqrt(rx);
            	assert ordiv <= rdiv;
            	assert rr >= real_sqrt(rx);
            	//division_lemma(rx,real_sqrt(rx),rr);
            	//assert real_div(rx,rr) <= real_div(rx,real_sqrt(rx));
            	//real_div_lemma2(rx, real_sqrt(rx), real_sqrt(rx));
            	assert rdiv <= real_sqrt(rx);
                assert nrre <= rr;
                assert rr - nrre < 0.000005*nrre;
                assert nrre - real_sqrt(rx) <= rr - nrre;
                assert nrre - real_sqrt(rx) <= 0.0000075*real_sqrt(rx);
                assert nrr - real_sqrt(rx) <= 0.00001*real_sqrt(rx);
            } else {
            	assert 10 < 11; //kijken of we hier komen
                assert rr < nrre;
                assert nrre - rr < 0.000005*nrre;
                assert real_sqrt(rx) - nrre <= nrre - rr;
                assert real_sqrt(rx) - nrre <= 0.0000075*real_sqrt(rx);
                assert real_sqrt(rx) - nrr <= 0.00001*real_sqrt(rx);
            }
            @*/
            break;
        }
        // assert rr >= real_sqrt(rx);
        // assert rx == real_sqrt(rx) * real_sqrt(rx);
        // assert rr * rr >= real_sqrt(rx) * real_sqrt(rx);
        // real_div_lemma2(rr*rr, rr, rr);
        // assert real_div(rr*rr, rr) == rr;
        // assert (real_div(rr * rr, rr) + rr) / 2 >= (real_div(rx,rr) + rr) / 2;
        // assert nrr >= real_sqrt(rx);
        // assert nrr >= real_sqrt(rx); //WEG
    }
    return result;
}

    
    
    