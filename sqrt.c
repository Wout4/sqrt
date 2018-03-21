#include <math.h>


//TODO: issue verifast github, deling verwacht double in teller.
float vector_size(float x, float y)
    //@ requires real_of_float(x) == some(?rx) &*& real_of_float(y) == some(?ry);
    //@ ensures real_of_float(result) == some(?rr) &*& rx == 0 && ry == 0 ? rr == 0 : 0 < rr &*& relative_error(real_vector_size(rx,ry),rr,0.00001) == true;
{
    //@ strict_product_sign_lemma(rx,rx);
    //@ strict_product_sign_lemma(ry,ry);
    //double temp = (double)x * x + (double)y * y; //for Z3 bug
    double sqrt = my_sqrt((double)x * x + (double)y * y);
    return (float) sqrt;
    // assert real_of_double(sqrt) == some(?rsqrt);
    // assert real_of_double(temp) == some(?rtemp);
    // assert rtemp == rx * rx + ry * ry;
    /* if (rtemp != 0) {
        assert relative_error(real_sqrt(rtemp),rsqrt,0.00001) == true;
        assert real_vector_size(rx,ry) == real_sqrt(rx * rx + ry * ry);
        assert relative_error(real_vector_size(rx,ry),rsqrt,0.00001) == true;
    } @*/
}


double my_sqrt(double x)
    //@ requires real_of_double(x) == some(?rx) &*& 0 <= rx;
    //@ ensures real_of_double(result) == some(?rr) &*& rx == 0 ? rr == 0 : 0 < rr &*& relative_error(real_sqrt(rx),rr,0.00001) == true;
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
    /*@ if (orr * orr > rx) {
    	    assert orr * orr > rx;
    	    real orr2div = real_div(orr * orr, rx);
    	    real_div_lemma(orr2, rx, orr2div);
    	    assert real_div(orr2, rx) > 1;
    	    assert real_div(rx, orr2) < 1;
    	    assert ordiv * ordiv < rx;
    	} else {
    	    assert ordiv * ordiv > rx;
    	}
    @*/
    //@ assert real_abs(rx - rr2) < real_abs(rx - orr2);
    //@ assert real_abs(real_sqrt(rx) - rr) < real_abs(real_sqrt(rx) - orr);
    
    for (;;)
        /*@ invariant real_of_double(result) == some(?rr) &*& 
        0 < rr &*& 
        real_of_double(oldResult) == some(orr) &*& 
        real_abs(real_sqrt(rx) - rr) < real_abs(real_sqrt(rx) - orr) &*&
        real_of_long_double(div) == some (ordiv) &*&
        ordiv == real_div(rx,orr) &*&
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
        //@ substitution_lemma(rx, rdiv, 2 * nrr - rr, rr); // rx == rdiv * rr en rdiv == nrr - rr maar rx == (nrr -rr) *rr wordt niet afgeleid??
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
        double rDif = fabs(result - oldResult);
        if (rDif < 0.000004*result) {
            //@ assert (0.999996 * nrr < rr && rr <= nrr) || (rr < 1.000004 * nrr && rr > nrr);
            //@ assert real_abs(0.9999999 * nrre - rr)*0.9999999 < 0.000004*1.0000001*nrre + 0.0000001 * nrre;
            //@ assert real_abs(0.9999999 * nrre - rr)*0.9999999 < 0.000004*1.0000001*nrre*1.025;
            // assert real_abs(0.9999999 * nrre - rr)*0.9999999 < 0.000004*1.0000001*nrre*1.0000001; klopt niet denk ik, zie hierboven
            //@ assert real_abs(nrre - rr) < 0.000005*nrre;
            /*@
            if (real_sqrt(rx) <= rr) {
            	real_sqrt_lemma2(rx, real_sqrt(rx)); //mss niet nodig
                assert nrre < rr;
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
    }
    return result;
}



// fixpoint real real_vector_size(real x, real y) { return real_sqrt(x * x + y * y); }

/*

float vector_size(float x, float y)
    //@ requires real_of_float(x) == some(?rx) &*& real_of_float(y) == some(?ry);
    //@ ensures real_of_float(result) == some(?rr) &*& rx == 0 && ry == 0 ? rr == 0 : 0 < rr &*& real_abs(rr/real_vector_size(rx, ry) - 1) < 0.00001;
{
    double sqrt = my_sqrt((double)x * x + (double)y * y);
    return (float) sqrt;
}
*/