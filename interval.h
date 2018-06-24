#ifndef INTERVAL_H
#define INTERVAL_H
#include "stdlib.h"
#include "interval_math.h"



struct interval {
    double a;
    double b;
};
// predicate interval(pointer, x)
/*@

lemma void pos_inf_interval_lemma(struct interval *x, real x1)
    requires x->a |-> ?xa &*& x->b |-> ?xb &*& fp_of_double(xa) == pos_inf &*& between(fp_of_double(xa),fp_of_double(xb),x1) == true;
    ensures fp_of_double(xb) == pos_inf &*& x->a |-> xa &*& x->b |-> xb;
{   
    assert between(fp_of_double(xa),fp_of_double(xb),x1) == true;
    assert leq_double_real(pos_inf,x1) == true;
    assert leq_real_double(x1,fp_of_double(xb)) == true;
    if (fp_of_double(xb) != pos_inf){
        assert fp_of_double(xb) == real_double(?rxb);
        real_double_lemma(xb);
    } else {}
}

fixpoint bool is_real_inf(real x);

lemma void real_inf_mult_lemma(real x, real a);
    requires is_real_inf(x) == true &*& a > 0;
    ensures x * a > max_dbl;

fixpoint bool leq_double_real(fp_double a, real x){
    switch (a) {
    	case real_double(ra): return ra <= x;
    	case pos_inf: return x > max_dbl * 2 && is_real_inf(x);
    	case neg_inf: return true;
    	case NaN: return false;
    }
}

fixpoint bool leq_real_double(real x, fp_double b){
    switch (b) {
    	case real_double(rb): return x <= rb;
    	case pos_inf: return true;
    	case neg_inf: return x < min_dbl * 2;
    	case NaN: return false;
    }
}

fixpoint bool between(fp_double a, fp_double b, real x){
    return leq_double_real(a,x) && leq_real_double(x,b);
}

predicate pos_double(double a) =
    real_of_double(a) == some(?ra) &*&
    ra >= 0 ||
    is_pos_infinity(a);


predicate interval_pred(struct interval *interval, real x) =
    interval->a |-> ?a &*&
    interval->b |-> ?b &*&
    between(fp_of_double(a),fp_of_double(b),x) == true;
@*/
/*
struct interval *double_add(struct interval *first, struct interval *second)
    /*@ requires interval_pred(first,?x1) &*&
    	interval_pred(second,?x2);@*/
/*    /*@ ensures interval_pred(first,x1) &*&
        interval_pred(second,x2) &*&
        interval_pred(result,x1 + x2) &*&
    	malloc_block_interval(result); @*/
/*    {
    //@ open interval_pred(first, x1);
    //@ open interval_pred(second, x2);
    //@ assert first->a |-> ?fa;
    //@ assert second->a |-> ?sa;
    //@ assert first->b |-> ?fb;
    //@ assert second->b |-> ?sb;
    struct interval *result = malloc(sizeof(struct interval));
    if (result == 0) { abort(); }
    if ((first->a == -INFINITY && second->a == INFINITY) || 
    	(first->a == INFINITY && second->a == -INFINITY)){
    	result->a = -INFINITY;
    	//@ assert result->a |-> ?ra;
    	//@ assert fp_of_double(ra) == neg_inf;
    	//@ assert leq_double_real(fp_of_double(ra), x1 + x2) == true;
     } else {
    	double l = first->a + second->a;
    	result->a = nextafter(l,-INFINITY);
    	//@ assert result->a |-> ?ra;
    	/*@
    	if (is_real_double(fa) == true) {
    	    assert fp_of_double(fa) == real_double(?rfa);
    	    if (is_real_double(sa) == true) {
    	        assert fp_of_double(sa) == real_double(?rsa);
    	        if (is_real_double(l)) {
    	            assert fp_of_double(l) == real_double(?rl);
    	    	    assert rl <= round_up_double(rfa + rsa) || rfa + rsa > max_dbl;
    	    	    if (is_real_double(ra)) {
    	    	        if (rl <= round_up_double(rfa + rsa)){
    	    	            assert fp_of_double(ra) == real_double(?rra);
    	    	            assert rra == prev_double(rl);
    	    	            prev_double_transitivity_lemma(rl,round_up_double(rfa + rsa));
    	    	            assert rra <= prev_double(round_up_double(rfa + rsa));
    	    	            prev_round_up_lemma(rfa + rsa, prev_double(round_up_double(rfa + rsa)));
    	    	            assert leq_double_real(fp_of_double(ra), x1 + x2) == true;
    	    	        } else {
    	    	            assert rfa + rsa > max_dbl;
    	    	            assert rfa + rsa <= max_dbl / md_eps;
    	    	            assert fp_of_double(ra) == real_double(?rra);
    	    	            assert rl >= round_down_double(rfa + rsa);
    	    	            round_down_max_dbl_lemma(rfa + rsa);
    	    	            assert rl >= max_dbl;
    	    	            real_double_lemma(l);
    	    	            assert rl == max_dbl;
    	    	            assert rra == prev_double(rl);
    	    	            prev_double_lemma(rl, rra);
    	    	            assert leq_double_real(fp_of_double(ra), x1 + x2) == true;
    	    	        }
    	    	    }
    	    	    assert x1 + x2 >= rfa + rsa;
    	    	} else {}
    	    	assert leq_double_real(fp_of_double(ra), x1 + x2) == true;
    	    } else if (fp_of_double(sa) == pos_inf){
    	    	
    		real_double_lemma(fa);
    	    } else if (fp_of_double(sa) == neg_inf){
    	
    	    } else {
    	
    	    }
    	} else if (fp_of_double(fa) == pos_inf){
    	    if (is_real_double(sa) == true) {
    	        assert fp_of_double(sa) == real_double(?rsa);
    	    	real_double_lemma(sa);
    	    } else if (fp_of_double(sa) == pos_inf){
    	
    	    } else if (fp_of_double(sa) == neg_inf){
    	
    	    } else {
    	
    	    }
    	} else if (fp_of_double(fa) == neg_inf){
    	    if (is_real_double(sa) == true) {
    	    	assert fp_of_double(sa) == real_double(?rsa);
    	        assert fp_of_double(l) == neg_inf; //wordt niet bewezen zonder lijn hierboven.
    	    } else if (fp_of_double(sa) == pos_inf){
    	
    	    } else if (fp_of_double(sa) == neg_inf){
    	
    	    } else {
    	
    	    }
    	} else {
    	    assert 1 == 2;
    	}
    	@*/
/*    	//@ assert leq_double_real(fp_of_double(ra), x1 + x2) == true;
    }
    if ((first->b == -INFINITY && second->b == INFINITY) ||
    	(first->b == INFINITY && second->b == -INFINITY)){
    	result->b = INFINITY;
    	//@ assert result->b |-> ?rb;
    	//@ assert fp_of_double(rb) == pos_inf;
    	//@ assert leq_real_double(x1 + x2, fp_of_double(rb)) == true;
     } else {
    	double u = first->b + second->b;
    	result->b = nextafter(u,INFINITY);
    	//@ assert result->b |-> ?rb;
    	/*@
    	if (is_real_double(fb) == true) {
    	    assert fp_of_double(fb) == real_double(?rfb);
    	    real_double_lemma(fb);
    	    if (is_real_double(sb) == true) {
    	    	assert fp_of_double(sb) == real_double(?rsb);
    	    	if (!is_real_double(u)) {
    	    	} else {
    	    	    assert fp_of_double(u) == real_double(?ru);
    	    	    assert x1 <= rfb;
    	    	    assert x2 <= rsb;
    	    	    assert x1 + x2 <= rfb + rsb;
    	    	    assert ru >= round_down_double(rfb + rsb) || rfb + rsb < min_dbl;
    	    	    if (is_real_double(rb)) {
    	    	        if (ru >= round_down_double(rfb + rsb)) {
    	    	        
    	    	            assert fp_of_double(rb) == real_double(?rrb);
    	    	            assert rrb == next_double(ru);
    	    	            next_double_transitivity_lemma(round_down_double(rfb + rsb), ru);
    	    	            assert next_double(ru) >= next_double(round_down_double(rfb + rsb));
    	    	            assert rrb == next_double(ru);
    	    	            leq_transitivity_lemma(next_double(round_down_double(rfb + rsb)), next_double(ru), rrb);
    	    	            assert rrb  >= next_double(round_down_double(rfb + rsb));
    	    	            next_round_down_lemma(rfb + rsb, next_double(round_down_double(rfb + rsb)));
    	    	            assert x1 + x2 <= rrb;
    	    	            assert leq_real_double(x1 + x2, fp_of_double(rb)) == true;
    	    	        } else { 
    	    	            assert rfb + rsb < min_dbl;
    	    	            assert rfb + rsb >= min_dbl / md_eps;
    	    	            assert fp_of_double(rb) == real_double(?rrb);
    	    	            assert ru <= round_up_double(rfb + rsb);
    	    	            round_up_min_dbl_lemma(rfb + rsb);
    	    	            assert ru <= min_dbl;
    	    	            real_double_lemma(u);
    	    	            assert ru == min_dbl;
    	    	            assert rrb == next_double(ru);
    	    	            next_double_lemma(ru, rrb);
    	    	            assert x1 + x2 <= rrb;
    	    	            assert leq_real_double(x1 + x2, fp_of_double(rb)) == true;
    	    	        }
    	    	    } else {
    	    	        assert fp_of_double(rb) == pos_inf;
    	    	        assert leq_real_double(x1 + x2, fp_of_double(rb)) == true;
    	    	    }
    	    	    assert x1 + x2 <= rfb + rsb;
    	    	    assert leq_real_double(x1 + x2, fp_of_double(rb)) == true;
    	    	}
    	    } else if (fp_of_double(sb) == pos_inf){
    	    } else if (fp_of_double(sb) == neg_inf){
    	    } else {}
    	} else if (fp_of_double(fb) == pos_inf){
    	    if (is_real_double(sb) == true) {
    	        assert fp_of_double(sb) == real_double(?rsb);
    	    } else if (fp_of_double(sb) == pos_inf){
    	    } else if (fp_of_double(sb) == neg_inf){
    	    } else {}
    	} else if (fp_of_double(fb) == neg_inf){
    	    if (is_real_double(sb) == true) {
    	        assert fp_of_double(sb) == real_double(?rsb);
    	        //assert x1 < 2 * min_dbl;
    	        assert x2 <= rsb;
    	        //assert x1 + x2 < 2 * min_dbl + rsb;
    	        real_double_lemma(sb);
    	        assert rsb >= min_dbl;
    	        assert rsb <= max_dbl;
    	        //assert x1 + x2 < 2 * min_dbl + max_dbl;
    	        assert min_dbl + max_dbl == 0;
    	        //assert x1 + x2 < min_dbl;
    	        assert fp_of_double(u) == neg_inf;
    	        assert fp_of_double(rb) == real_double(min_dbl);
    	        assert leq_real_double(x1 + x2, fp_of_double(rb)) == true;   
    	    } else if (fp_of_double(sb) == pos_inf){
    	    } else if (fp_of_double(sb) == neg_inf){   	
    	    } else {}
    	} else {
    	}
    	@*/
    	
/*    	//@ assert leq_real_double(x1 + x2, fp_of_double(rb)) == true;
    }

    return result;
    //between(fp_of_double(a),fp_of_double(b),x) == true;
    //@ close(interval_pred(result,x1 + x2));
    //@ close(interval_pred(first,x1));
    //@ close(interval_pred(second,x2));
}

*/
/*
struct interval *double_sub(struct interval *first, struct interval *second)
    /*@ requires interval_pred(first,?x1) &*&
    	interval_pred(second,?x2); @*/
/*    /*@ ensures interval_pred(first,x1) &*&
    	interval_pred(second,x2) &*&
    	interval_pred(result,x1 - x2) &*&
    	malloc_block_interval(result); @*/
/*    {
    //@ open interval_pred(first, x1);
    //@ open interval_pred(second, x2);
    //@ assert first->a |-> ?fa;
    //@ assert second->a |-> ?sa;
    //@ assert first->b |-> ?fb;
    //@ assert second->b |-> ?sb;
    struct interval *result = malloc(sizeof(struct interval));
    if (result == 0) { abort(); }
    
    if ((first->a == INFINITY && second->b == INFINITY) ||
    	(first->a == -INFINITY && second->b == -INFINITY)){
    	result->a = -INFINITY;
    } else {
    	double l = first->a - second->b;
    	result->a = nextafter(l,-INFINITY);
    	//@ assert result->a |-> ?ra;
    	/*@
    	if (is_real_double(fa) == true) {
    	    assert fp_of_double(fa) == real_double(?rfa);
    	    if (is_real_double(sb) == true) {
    	        assert fp_of_double(sb) == real_double(?rsb);
    	        if (is_real_double(l)) {
    	            assert fp_of_double(l) == real_double(?rl);
    	    	    assert rl <= round_up_double(rfa - rsb) || rfa - rsb > max_dbl;
    	    	    if (is_real_double(ra)) {
    	    	        if (rl <= round_up_double(rfa - rsb)){
    	    	            assert fp_of_double(ra) == real_double(?rra);
    	    	            assert rra == prev_double(rl);
    	    	            prev_double_transitivity_lemma(rl,round_up_double(rfa - rsb));
    	    	            assert rra <= prev_double(round_up_double(rfa - rsb));
    	    	            prev_round_up_lemma(rfa - rsb, prev_double(round_up_double(rfa - rsb)));
    	    	            assert leq_double_real(fp_of_double(ra), x1 - x2) == true;
    	    	        } else {
    	    	            assert rfa - rsb > max_dbl;
    	    	            assert rfa - rsb <= max_dbl / md_eps;
    	    	            assert fp_of_double(ra) == real_double(?rra);
    	    	            assert rl >= round_down_double(rfa - rsb);
    	    	            round_down_max_dbl_lemma(rfa - rsb);
    	    	            assert rl >= max_dbl;
    	    	            real_double_lemma(l);
    	    	            assert rl == max_dbl;
    	    	            assert rra == prev_double(rl);
    	    	            prev_double_lemma(rl, rra);
    	    	            assert leq_double_real(fp_of_double(ra), x1 - x2) == true;
    	    	        }
    	    	    }
    	    	} else {}
    	        
    	    } else if (fp_of_double(sb) == pos_inf){
    	    	
    	    } else if (fp_of_double(sb) == neg_inf){
    		real_double_lemma(fa);
    	    } else {
    	
    	    }
    	} else if (fp_of_double(fa) == pos_inf){
    	    if (is_real_double(sb) == true) {
    	    	real_double_lemma(sb);

    	    } else if (fp_of_double(sb) == pos_inf){
    	
    	    } else if (fp_of_double(sb) == neg_inf){
    	
    	    } else {
    	
    	    }
    	} else if (fp_of_double(fa) == neg_inf){
    	    if (is_real_double(sb) == true) {
    	        real_double_lemma(sb);
    	    } else if (fp_of_double(sb) == pos_inf){
    	
    	    } else if (fp_of_double(sb) == neg_inf){
    	
    	    } else {
    	
    	    }
    	} else {

    	}
    	@*/
/*        //@ assert leq_double_real(fp_of_double(ra), x1 - x2) == true;
    }
    if ((first->b == INFINITY && second->a == INFINITY) ||
    	(first->b == -INFINITY && second->a == -INFINITY)){
    	result->b = INFINITY;
    } else {
    	double u = first->b - second->a;
    	result->b = nextafter(u,INFINITY);
    	//@ assert result->b |-> ?rb;
    	/*@
    	if (is_real_double(fb) == true) {
    	    assert fp_of_double(fb) == real_double(?rfb);
    	    real_double_lemma(fb);
    	    if (is_real_double(sa) == true) {
    	    	assert fp_of_double(sa) == real_double(?rsa);
    	    	if (is_real_double(u)) {
    	    	    assert fp_of_double(u) == real_double(?ru);
    	    	    assert ru >= round_down_double(rfb - rsa) || rfb - rsa < min_dbl;
    	    	    if (is_real_double(rb)) {
    	    	    	if (ru >= round_down_double(rfb - rsa)) {
    	    	            assert fp_of_double(rb) == real_double(?rrb);
    	    	            assert rrb == next_double(ru);
    	    	            next_double_transitivity_lemma(round_down_double(rfb - rsa), ru);
    	    	            assert next_double(ru) >= next_double(round_down_double(rfb - rsa));
    	    	            assert rrb == next_double(ru);
    	    	            leq_transitivity_lemma(next_double(round_down_double(rfb - rsa)), next_double(ru), rrb);
    	    	            assert rrb  >= next_double(round_down_double(rfb - rsa));
    	    	            next_round_down_lemma(rfb - rsa, next_double(round_down_double(rfb - rsa)));
    	    	            assert x1 - x2 <= rrb;
    	    	            assert leq_real_double(x1 - x2, fp_of_double(rb)) == true;
    	    	        } else { 
    	    	            assert rfb - rsa < min_dbl;
    	    	            assert rfb - rsa >= min_dbl / md_eps;
    	    	            assert fp_of_double(rb) == real_double(?rrb);
    	    	            assert ru <= round_up_double(rfb  - rsa);
    	    	            round_up_min_dbl_lemma(rfb - rsa);
    	    	            assert ru <= min_dbl;
    	    	            real_double_lemma(u);
    	    	            assert ru == min_dbl;
    	    	            assert rrb == next_double(ru);
    	    	            next_double_lemma(ru, rrb);
    	    	            assert leq_real_double(x1 - x2, fp_of_double(rb)) == true;
    	    	        }
    	    	        assert leq_real_double(x1 - x2, fp_of_double(rb)) == true;
    	    	    } else {
    	    	    
    	    	    }
    	    	} else {
    	    	
    	    	}
    	    	assert leq_real_double(x1 - x2, fp_of_double(rb)) == true;
    	    } else if (fp_of_double(sa) == pos_inf){
    	    } else if (fp_of_double(sa) == neg_inf){
    	    } else {}
    	} else if (fp_of_double(fb) == pos_inf){
    	    if (is_real_double(sa) == true) {
    	    	real_double_lemma(sa);
    	    } else if (fp_of_double(sa) == pos_inf){
    	    } else if (fp_of_double(sa) == neg_inf){
    	    } else {}
    	} else if (fp_of_double(fb) == neg_inf){
    	    if (is_real_double(sa) == true) { 
    	    	real_double_lemma(sa);
    	    } else if (fp_of_double(sa) == pos_inf){
    	    } else if (fp_of_double(sa) == neg_inf){   	
    	    } else {}
    	} else {
    	}

    	@*/
/*    	//@ assert leq_real_double(x1 - x2, fp_of_double(rb)) == true;
    }
    //@ close(interval_pred(result,x1 - x2));
    //@ close(interval_pred(first,x1));
    //@ close(interval_pred(second,x2));
    return result;
}
*/

struct interval *double_mult(struct interval *first, struct interval *second)
    /*@ requires interval_pred(first,?x1) &*&
    	interval_pred(second,?x2);@*/
    /*@ ensures interval_pred(first,x1) &*&
    	interval_pred(second,x2) &*&
    	interval_pred(result, x1 * x2) &*&
    	malloc_block_interval(result); @*/
    {
    //@ open interval_pred(first,x1);
    //@ open interval_pred(second,x2);
    struct interval *result = malloc(sizeof(struct interval));
    if (result == 0) { abort(); }
    
    double x = first->a * second->a;
    double y = first->a * second->b;
    double z = first->b * second->a;
    double w = first->b * second->b;
    if (isnan(x)){x = 0;}
    if (isnan(z)){z = 0;}
    if (isnan(y)){y = 0;}
    if (isnan(w)){w = 0;}
    //@ real_of_int_lemma_UNSAFE(0,0);
    //@ assert first->a |-> ?fa;
    //@ assert first->b |-> ?fb;
    //@ assert second->a |-> ?sa;
    //@ assert second->b |-> ?sb;
    
    double temp1 = fmin(x,y);
    double temp2 = fmin(z,w);
    double l = fmin(temp1,temp2);
    if (l == 0) {
        result->a = 0;
    } else {
        result->a = nextafter(l,-INFINITY);
    }
    //@ assert result->a |-> ?ra;
    //@ fmin_lemma(temp2,z,w);
    //@ fmin_lemma(temp1,x,y);
    //@ fmin_lemma(l,temp1,temp2);
    /*@
    if (fp_of_double(l) == fp_of_double(x)){
        if (is_real_double(fa)) {
            assert fp_of_double(fa) == real_double(?rfa);
            if(is_real_double(sa)) {
                assert fp_of_double(sa) == real_double(?rsa);
                if (fp_of_double(l) == pos_inf){
                    assert rfa * rsa >= max_dbl;
                    assert fp_of_double(ra) == real_double(max_dbl);
                    assert x1 >= rfa;
                    assert x2 >= rsa;
                    assert fp_of_double(temp1) == pos_inf;
                    assert double_fmin(fp_of_double(temp1),fp_of_double(temp2)) == pos_inf;
                    assert fp_of_double(temp2) != NaN;
                    assert fp_of_double(temp2) != neg_inf;
                    if (is_real_double(temp2)){
                        assert fp_of_double(temp2) == real_double(?rtemp2);
                        assert double_fmin(pos_inf,real_double(rtemp2)) == real_double(rtemp2);
                        assert fp_of_double(temp1) == pos_inf;
                        assert double_fmin(fp_of_double(temp1),real_double(rtemp2)) == real_double(rtemp2);
                        assert false;
                    }
                    assert fp_of_double(temp2) != neg_inf && fp_of_double(temp2) != NaN && !is_real_double(temp2); // nodig voor volgende assert
                    assert fp_of_double(temp2) == pos_inf;
                    fmin_inf_lemma(temp2,z,w);
                    fmin_inf_lemma(temp1,x,y);
                    assert fp_of_double(y) == pos_inf;
                    assert fp_of_double(w) == pos_inf;
                    assert fp_of_double(z) == pos_inf;
                    switch (fp_of_double(fb)){
                        case real_double(rfb):
                            switch (fp_of_double(sb)){
                                case real_double(rsb): 
                                    assert rfb * rsb > max_dbl;
                                    if (rfb < 0){
                                        assert rsb < 0;
                                        assert x1 <= rfb;
                                        assert x2 <= rsb;
                                        assert x1 * x2 >= rfb * rsb;
                                        assert rfb * rsb >= max_dbl;
                                        leq_transitivity_lemma(max_dbl,rfb*rsb,x1*x2); // zelfs met z3
                                        assert x1 * x2 >= max_dbl;
                                    } else {
                                        assert rfb > 0;
                                        assert rsb > 0;
                                        assert fp_of_double(y) == pos_inf;
                                        assert rfa * rsb > max_dbl;
                                        assert rfa !=0;
                                        if (rfa < 0){ // nodig om te bewijzen dat dit nooit gebeurt
                                            //assert rfa * rsb < 0; 
                                            assert false;
                                        }
                                        assert rfa > 0;
                                        assert rsa > 0;
                                        assert x1 >= rfa;
                                        assert x2 >= rsa;
                                        lt_transitivity_lemma(0,rfa,x1);
                                        assert x1 > 0;
                                        assert x2 > 0;
                                        assert x1 * x2 >= rfa * rsa;
                                        assert rfa * rsa >= max_dbl;
                                        leq_transitivity_lemma(max_dbl,rfa*rsa,x1*x2);
                                        assert x1 * x2 >= max_dbl;
                                    }
                                case pos_inf: 
                                    assert rfb > 0;
                                    assert rfa > 0;
                                    assert rsa > 0;
                                    assert x1 > 0;
                                        assert x2 > 0;
                                    lt_transitivity_lemma(0,rfa,x1);
                                    leq_transitivity_lemma(max_dbl,rfa*rsa,x1*x2);
                                case neg_inf: assert true;
                            }
                        case pos_inf:
                        case neg_inf:
                        
                    }
                    assert x1 * x2 >= max_dbl;
                    assert leq_double_real(fp_of_double(ra), x1 * x2) == true;
 
                } else if (fp_of_double(l) == neg_inf){
                
                } else {
                    assert fp_of_double(l) == real_double(?rl);
                }
                    
            } else if (fp_of_double(sa) == pos_inf) {
                if (rfa == 0) {
                    assert fp_of_double(x) == real_double(0);
                    assert fp_of_double(l) == real_double(0);
                    assert fp_of_double(ra) == real_double(0);
                    assert x2 >= 2 * max_dbl;
                    assert x1 >= 0;
                    product_sign_lemma(x1,x2);
                    assert x1 * x2 >= 0;
                    assert leq_double_real(fp_of_double(ra), x1 * x2) == true;
                } else if (rfa > 0){
                    assert fp_of_double(ra) == real_double(?rra);
                    assert rra == max_dbl;
                    assert x1 > 0;
                    assert x2 >= 2*max_dbl;
                    real_inf_mult_lemma(x2,x1); // LEMMA GEBRUIKT
                } else {
                    assert fp_of_double(ra) == neg_inf;
                }
            } else if (fp_of_double(sa) == neg_inf) {
                if (rfa == 0) {
                    assert fp_of_double(ra) == real_double(0);
                    assert fp_of_double(fb) == real_double(?rfb); // zonder deze lijn wordt x1 == 0 niet bewezen.
                    assert x1 == 0;
                    multiply_zero_lemma(x1,x2);
                    assert x1 * x2 == 0;
                } else if (rfa > 0){
                    assert fp_of_double(ra) == neg_inf;
                } else {
                    assert double_fmin(fp_of_double(x),fp_of_double(y)) == fp_of_double(x);
                    assert fp_of_double(l) == fp_of_double(x);
                    assert fp_of_double(fb) == real_double(?rfb);
                    //assert rfb < 0;
                    //assert x1 < 0;
                    //assert x2 <= 2*min_dbl;
                    //real_inf_mult_lemma(x2,x1);
                    assert leq_double_real(fp_of_double(ra), x1 * x2) == true;
                }
                
            
            } else {}
        } else if (fp_of_double(fa) == pos_inf){
            if(is_real_double(sa)) {
                assert fp_of_double(sa) == real_double(?rsa);
                if (rsa == 0) {
                    product_sign_lemma(x1,x2);
                } else if (rsa > 0){
                    real_inf_mult_lemma(x1,x2);
                } else {
                }
            } else if (fp_of_double(sa) == pos_inf) {
            
            } else if (fp_of_double(sa) == neg_inf) {
            
            } else {}
        } else if (fp_of_double(fa) == neg_inf) {
            if(is_real_double(sa)) {
                assert fp_of_double(sa) == real_double(?rsa);
                if (rsa == 0) {
                    assert fp_of_double(sb) == real_double(?rsb);
                    assert rsb == 0;
                    multiply_zero_lemma(x1,x2);
                } else if (rsa < 0) {
                    assert double_fmin(fp_of_double(x),fp_of_double(y)) == fp_of_double(x);
                    assert fp_of_double(l) == fp_of_double(x);
                    assert fp_of_double(fb) == real_double(?rsb);  // nodig
                } else {
                }
            } else if (fp_of_double(sa) == pos_inf) {
            
            } else if (fp_of_double(sa) == neg_inf) {
                assert double_fmin(fp_of_double(x),fp_of_double(y)) == fp_of_double(x);
                assert fp_of_double(l) == fp_of_double(x);
                switch (fp_of_double(fb)){
                    case neg_inf:
                    case real_double(rfb):
                    case pos_inf: assert false;
                    case NaN: assert false;
                }
                assert is_real_double(fb) || fp_of_double(fb) == neg_inf;
                assert is_real_double(sb) || fp_of_double(sb) == neg_inf;
            } else {}
        } else {}
    } else if (fp_of_double(l) == fp_of_double(y)) {
        if (is_real_double(fa)) {
            assert fp_of_double(fa) == real_double(?rfa);
            if(is_real_double(sb)) {
                assert fp_of_double(sb) == real_double(?rsb);
            } else if (fp_of_double(sb) == pos_inf) {
            
            } else if (fp_of_double(sb) == neg_inf) {
            
            } else {}
        } else if (fp_of_double(fa) == pos_inf){
            if(is_real_double(sb)) {
                assert fp_of_double(sb) == real_double(?rsb);
            } else if (fp_of_double(sb) == pos_inf) {
            
            } else if (fp_of_double(sb) == neg_inf) {
            
            } else {}
        } else if (fp_of_double(fa) == neg_inf) {
            if(is_real_double(sb)) {
                assert fp_of_double(sb) == real_double(?rsb);
            } else if (fp_of_double(sb) == pos_inf) {
            
            } else if (fp_of_double(sb) == neg_inf) {
            
            } else {}
        } else {}
    } else if (fp_of_double(l) == fp_of_double(w)) {
        if (is_real_double(fb)) {
            assert fp_of_double(fb) == real_double(?rfb);
            if(is_real_double(sb)) {
                assert fp_of_double(sb) == real_double(?rsb);
            } else if (fp_of_double(sb) == pos_inf) {
            
            } else if (fp_of_double(sb) == neg_inf) {
            
            } else {}
        } else if (fp_of_double(fb) == pos_inf){
            if(is_real_double(sb)) {
                assert fp_of_double(sb) == real_double(?rsb);
            } else if (fp_of_double(sb) == pos_inf) {
            
            } else if (fp_of_double(sb) == neg_inf) {
            
            } else {}
        } else if (fp_of_double(fb) == neg_inf) {
            if(is_real_double(sb)) {
                assert fp_of_double(sb) == real_double(?rsb);
            } else if (fp_of_double(sb) == pos_inf) {
            
            } else if (fp_of_double(sb) == neg_inf) {
            
            } else {}
        } else {}
    } else {
        assert fp_of_double(l) == fp_of_double(z);
        if (is_real_double(fb)) {
            assert fp_of_double(fb) == real_double(?rfb);
            if(is_real_double(sa)) {
                assert fp_of_double(sa) == real_double(?rsa);
            } else if (fp_of_double(sa) == pos_inf) {
            
            } else if (fp_of_double(sa) == neg_inf) {
            
            } else {}
        } else if (fp_of_double(fb) == pos_inf){
            if(is_real_double(sa)) {
                assert fp_of_double(sa) == real_double(?rsa);
            } else if (fp_of_double(sa) == pos_inf) {
            
            } else if (fp_of_double(sa) == neg_inf) {
            
            } else {}
        } else if (fp_of_double(fb) == neg_inf) {
            if(is_real_double(sa)) {
                assert fp_of_double(sa) == real_double(?rsa);
            } else if (fp_of_double(sa) == pos_inf) {
            
            } else if (fp_of_double(sa) == neg_inf) {
            
            } else {}
        } else {}
    }
    @*/
    //@ assert leq_double_real(fp_of_double(ra), x1 * x2) == true;
    temp1 = fmax(x, y);
    temp2 = fmax(z, w);
    double u = fmax(temp1,temp2);
    if (u == 0) {
        result->b = 0;
    } else {
        result->b = nextafter(u,INFINITY);
    }
    //@ assert result->b |-> ?rb; 
    //@ fmax_lemma(temp1, x, y);
    //@ fmax_lemma(u,temp1,temp2);
    //@ fmax_lemma(temp2, z, w);
    /*@
    if (fp_of_double(u) == fp_of_double(x)){
        if (is_real_double(fa)) {
            assert fp_of_double(fa) == real_double(?rfa);
            if(is_real_double(sa)) {
                assert fp_of_double(sa) == real_double(?rsa);
                if (is_real_double(u)) {
                    assert fp_of_double(u) == real_double(?ru);
                    assert rsa * rfa < min_dbl || ru >= round_down(rsa * rfa);
                } else if (fp_of_double(u) == pos_inf) {
                
                } else {
                    assert is_real_double(fb) || is_real_double(sb);
                    if (is_real_double(fb)) {
                        assert fp_of_double(fb) == real_double(?rfb);
                        if (rfb == rfa) {
                        
                        } else {
                            //assert fp_of_double(sb) == real_double(?rsb);
                            //assert rsb == rsa;
                        }
                    } else {
                        assert fp_of_double(sb) == real_double(?rsb);
                        assert rsb == rsa;
                        assert x2 == rsa;
                        if (is_real_double(rb)) {
                            assert fp_of_double(rb) == real_double(?rrb);
                            assert rrb == next_double(ru);
                        }
                    }
                    assert false;
                }
            } else if (fp_of_double(sa) == pos_inf) {
                if (rfa == 0) {
                    switch (fp_of_double(fb)) {
                        case real_double(rfb): 
                            assert x1 <= rfb;
                            assert rfb == 0;
                            assert x1 == 0;
                            assert rfa <= rfb;
                            switch (fp_of_double(sb)){
                                case real_double(rsb):
                                    assert x2 <= rsb;
                                case pos_inf: assert true;
                                    assert x1 == 0;
                                    multiply_zero_lemma(x1,x2);
                                    assert x1 * x2 == 0;
                                case neg_inf:
                                case NaN:
                            };
                        case pos_inf: assert true;
                        case neg_inf: assert true;
                        case NaN: assert true;
                    };
                    assert leq_real_double(x1 * x2, fp_of_double(rb)) == true;
                } else if (rfa < 0) {
                    assert fp_of_double(u) == neg_inf;
                    assert x2 >= 2*max_dbl;
		    assert fp_of_double(fb) == real_double(?rfb);
		    if (rfb == 0) {
		        assert fp_of_double(w) == real_double(?rw);
		        assert rw == 0;
		    } else {
                    	assert x1 < 0;
                    	assert x1 * x2 <= neg_inf;
                    }
                } else {
                    assert fp_of_double(u) == pos_inf;
                }
            } else if (fp_of_double(sa) == neg_inf) {
                if(rfa == 0) {
                    assert fp_of_double(fb) == real_double(?rfb);
                    assert rfb == 0;
                } else if (rfa < 0){
                    assert fp_of_double(u) == pos_inf;
                } else {
                    assert fp_of_double(u) == neg_inf;
                    assert x1 > 0;
                    assert leq_double_real(neg_inf,x2) == true;
                    if (fp_of_double(fb) == pos_inf) {
                        
                    } else {
                        assert fp_of_double(fb) == real_double(?rfb);
                        assert fp_of_double(sb) == neg_inf;
                    }
                    assert x1 * x2 <= 2 * min_dbl;
                }
            
            } else {}
        } else if (fp_of_double(fa) == pos_inf){
            if(is_real_double(sa)) {
                assert fp_of_double(sa) == real_double(?rsa);
                if (rsa == 0) {
                    if (fp_of_double(fb) == pos_inf) {
                        assert fp_of_double(sb) == real_double(?rsb);
                        assert rsb == 0;
                        assert x2 == 0;
                        multiply_zero_lemma(x1,x2);
                    } else {
                        assert fp_of_double(fb) == real_double(?rfb);
                        
                    }
                } else if (rsa < 0){
                    assert fp_of_double(u) == neg_inf;
                    real_double_lemma(sa);
                    assert fp_of_double(sb) == real_double(?rsb);
                    if (fp_of_double(fb) != pos_inf){
                        assert fp_of_double(fb) == real_double(?rfb);
                    } else {
                        assert fp_of_double(fb) == pos_inf;
                    }
                    
                } else {
                    assert fp_of_double(u) == pos_inf;
                }
            } else if (fp_of_double(sa) == pos_inf) {
            
            } else if (fp_of_double(sa) == neg_inf) {
                assert fp_of_double(u) == neg_inf;
                if(fp_of_double(fb) != pos_inf) {
                    assert fp_of_double(fb) == real_double(?rfb);
                }
            
            } else {}
        } else if (fp_of_double(fa) == neg_inf) {
            if(is_real_double(sa)) {
                assert fp_of_double(sa) == real_double(?rsa);
                if (rsa == 0) {
                    if (is_real_double(sb)) {
                        assert fp_of_double(sb) == real_double(?rsb);
                    }
                    if (is_real_double(fb)) {
                        assert fp_of_double(fb) == real_double(?rfb);
                        assert x1 >= 0;
                    }
                } else if (rsa < 0) {
                    assert fp_of_double(u) == pos_inf;
                } else {
                    assert fp_of_double(u) == neg_inf;
                    if (fp_of_double(fb) == neg_inf) {
                        
                    } else {
                        assert fp_of_double(fb) == real_double(?rfb);
                        
                    }

                }
            } else if (fp_of_double(sa) == pos_inf) {
                assert fp_of_double(u) == neg_inf;
                pos_inf_interval_lemma(second,x2);
                assert fp_of_double(sb) == pos_inf;
            } else if (fp_of_double(sa) == neg_inf) {
            
            } else {}
        } else {}
    } else if (fp_of_double(u) == fp_of_double(y)) {
        if (is_real_double(fa)) {
            assert fp_of_double(fa) == real_double(?rfa);
            if(is_real_double(sb)) {
                assert fp_of_double(sb) == real_double(?rsb);
            } else if (fp_of_double(sb) == pos_inf) {
                if (rfa == 0) {
                    assert fp_of_double(fb) == real_double(?rfb);
                } else {}
            
            } else if (fp_of_double(sb) == neg_inf) {
                if (rfa == 0) {
                    
                } else {}
            
            } else {}
        } else if (fp_of_double(fa) == pos_inf){
            if(is_real_double(sb)) {
                assert fp_of_double(sb) == real_double(?rsb);
                if (rsb == 0){
                    //assert fp_of_double(sa) == real_double(?rsa);
                    assert x2 <= 0;
                    assert x1 >= 0;
                    negative_product_lemma(x2,x1);
                    assert x1 * x2 <= 0;
                    
                } else {}
            } else if (fp_of_double(sb) == pos_inf) {
            
            } else if (fp_of_double(sb) == neg_inf) {
            
            } else {}
        } else if (fp_of_double(fa) == neg_inf) {
            if(is_real_double(sb)) {
                assert fp_of_double(sb) == real_double(?rsb);
            } else if (fp_of_double(sb) == pos_inf) {
            
            } else if (fp_of_double(sb) == neg_inf) {
            
            } else {}
        } else {}
    } else if (fp_of_double(u) == fp_of_double(w)) {
        if (is_real_double(fb)) {
            assert fp_of_double(fb) == real_double(?rfb);
            if(is_real_double(sb)) {
                assert fp_of_double(sb) == real_double(?rsb);
            } else if (fp_of_double(sb) == pos_inf) {
                if (rfb == 0){
                    assert x1 <= 0;
                    assert x2 >= 0;
                    negative_product_lemma(x1,x2);
                    assert x1 * x2 <= 0;
                }
            } else if (fp_of_double(sb) == neg_inf) {
            
            } else {}
        } else if (fp_of_double(fb) == pos_inf){
            if(is_real_double(sb)) {
                assert fp_of_double(sb) == real_double(?rsb);
                if (rsb == 0){
                    assert fp_of_double(sa) == real_double(?rsa);
                }
            } else if (fp_of_double(sb) == pos_inf) {
            
            } else if (fp_of_double(sb) == neg_inf) {
            
            } else {}
        } else if (fp_of_double(fb) == neg_inf) {
            if(is_real_double(sb)) {
                assert fp_of_double(sb) == real_double(?rsb);
                if (rsb == 0) {
                    assert fp_of_double(sa) == real_double(?rsa);
                }
            } else if (fp_of_double(sb) == pos_inf) {
            
            } else if (fp_of_double(sb) == neg_inf) {
            
            } else {}
        } else {}
    } else {
        assert fp_of_double(u) == fp_of_double(z);
        if (is_real_double(fb)) {
            assert fp_of_double(fb) == real_double(?rfb);
            if(is_real_double(sa)) {
                assert fp_of_double(sa) == real_double(?rsa);
            } else if (fp_of_double(sa) == pos_inf) {
                if (rfb == 0) {
                    assert x1 <= 0;
                    assert x2 >= 2*max_dbl;
                    negative_product_lemma(x1,x2);
                    assert x1 * x2 <= 0;
                }
            } else if (fp_of_double(sa) == neg_inf) {
            
            } else {}
        } else if (fp_of_double(fb) == pos_inf){
            if(is_real_double(sa)) {
                assert fp_of_double(sa) == real_double(?rsa);
                if (rsa == 0) {
                    assert fp_of_double(sb) == real_double(?rsb);
                }
            } else if (fp_of_double(sa) == pos_inf) {
            
            } else if (fp_of_double(sa) == neg_inf) {
            
            } else {}
        } else if (fp_of_double(fb) == neg_inf) {
            if(is_real_double(sa)) {
                assert fp_of_double(sa) == real_double(?rsa);
                if (rsa == 0) {
                
                }
            } else if (fp_of_double(sa) == pos_inf) {
            
            } else if (fp_of_double(sa) == neg_inf) {
            
            } else {}
        } else {}
    }
    @*/
    //@ assert leq_real_double(x1 * x2, fp_of_double(rb)) == true;
    //@ close(interval_pred(result,x1 * x2));
    //@ close(interval_pred(first,x1));
    //@ close(interval_pred(second,x2));
    return result;
}

/*
struct interval *double_div(struct interval *first, struct interval *second)
    /*@ requires interval_a(first,?fa) &*&
    	real_of_double(fa) == some(?rfa) &*&
    	interval_b(first,?fb) &*&
    	real_of_double(fb) == some(?rfb) &*&
    	interval_a(second,?sa) &*&
    	real_of_double(sa) == some(?rsa) &*&
    	interval_b(second,?sb) &*&
    	real_of_double(sb) == some(?rsb) &*&
    	rfa >= 0 &*&
    	rsa > 0 &*&
    	rfb >= 0 &*&
    	rsb > 0;@*/
 /*   /*@ ensures interval_a(first,fa) &*&
    	interval_b(first,fb) &*&
    	interval_a(second,sa) &*&
    	interval_b(second,sb) &*&
    	interval_a(result,?ra) &*&
    	real_of_double(ra) == some(?rra) &*&
    	interval_b(result,?rb) &*&
    	real_of_double(rb) == some(?rrb) &*&
    	malloc_block_interval(result) &*&
    	rra <= real_div(rfa, rsb) &*&
    	rrb >= real_div(rfb, rsa) &*&
    	rra >= real_div(rfa, rsb) * (1 - d_eps) * (1 - d_eps) &*&
    	rrb <= real_div(rfb, rsa) * (1 + d_eps) * (1 + d_eps); @*/
 /*   	{
    if (first->a < 0) { abort(); }
    if (first->b < 0) { abort(); }
    struct interval *result = malloc(sizeof(struct interval));
    if (result == 0) { abort(); }
    double l = first->a / second->b;
    //@ assert real_of_double(l) == some(?rl);
    result->a = nextafter(l, -INFINITY);
    //@ assert result->a |-> ?ra1;
    //@ assert real_of_double(ra1) == some(?rra1);
    //@ prev_lemma(rl, prev(rl));
    //@ prev_lemma(real_div(rfa, rsb), prev(real_div(rfa, rsb)));
    //@ real_div_pos_lemma(rfa, rsb);
    //@ real_div_pos_lemma(rfb,rsa);
    //@ assert rra1 == prev(rl);
    /*@ if (rl == real_div(rfa, rsb)){
    	assert rra1 == prev(real_div(rfa, rsb));
    	assert rra1 >= real_div(rfa, rsb) * (1 - d_eps) ;
    } else if (rl == next(real_div(rfa, rsb))){
    	assert rra1 == prev(next(real_div(rfa, rsb)));
    	prev_next_lemma(real_div(rfa, rsb), rra1);
    	assert rra1 >= real_div(rfa, rsb) * (1 - d_eps) * (1 - d_eps);
    } else {
        assert rra1 == prev(prev(real_div(rfa, rsb)));
        prev_lemma(real_div(rfa, rsb), rl);
        assert rra1 >= real_div(rfa, rsb) * (1 - d_eps) * (1 - d_eps);
    }
    @*/
/*    double u = first->b / second->a;
    //@ assert real_of_double(u) == some(?ru);
    result->b = nextafter(u, INFINITY);
    //@ assert result->b |-> ?rb1;
    //@ assert real_of_double(rb1) == some(?rrb1);
    //@ next_lemma(ru,next(ru));
    //@ next_lemma(real_div(rfb, rsa), next(real_div(rfb, rsa)));
    //@ next_prev_lemma(real_div(rfb, rsa), next(prev(real_div(rfb, rsa))));
    return result;
}

/*
struct interval *double_sqrt(struct interval *x){
    if (x->a < 0) { abort(); }

    struct interval *result = malloc(sizeof(struct interval));
    if (x->a == 0.0) { result->a = 0.0 }

    
    
}*/


/*@
lemma void fmax_lemma(double temp2, double w, double z)
    requires fp_of_double(temp2) == double_fmax(fp_of_double(w),fp_of_double(z));
    ensures fp_of_double(temp2) == fp_of_double(w) || fp_of_double(temp2) == fp_of_double(z);
{
    if (is_real_double(temp2)) {
        assert fp_of_double(temp2) == real_double(?rmax);
 	assert is_real_double(z) || is_real_double(w);
 	if (is_real_double(z)) {
 	    assert fp_of_double(z) == real_double(?rz);
 	    if (rz == rmax) {
 	        assert fp_of_double(temp2) == fp_of_double(z);
 	    } else {
 	        assert fp_of_double(w) == real_double(?rw1);
 	        assert rw1 == rmax;
 	    }
 	} else {
 	    assert fp_of_double(w) == real_double(?rw);
 	}
    } else if (fp_of_double(temp2) == pos_inf) {
        if (is_real_double(z)) {
            if (is_real_double(w)) {
                assert fp_of_double(w) == real_double(?rw);
                assert fp_of_double(z) == real_double(?rz);
                assert double_fmax(real_double(rw),real_double(rz)) == real_double(?rm);
            } else if (fp_of_double(w) == pos_inf) {
            
            } else if (fp_of_double(w) == NaN) {
            
            } else {}
        } else if (fp_of_double(z) == pos_inf) {
        
        } else if (fp_of_double(z) == NaN) {
        
        } else {}
    
    } else if (fp_of_double(temp2) == neg_inf) {
        assert fp_of_double(temp2) == double_fmax(fp_of_double(z),fp_of_double(w));
        if (is_real_double(z)) {
            if (is_real_double(w)) {
                assert fp_of_double(w) == real_double(?rw);
                assert fp_of_double(z) == real_double(?rz);
                assert double_fmax(real_double(rw),real_double(rz)) == real_double(?rm);
            } else if (fp_of_double(w) == pos_inf) {
            
            } else if (fp_of_double(w) == NaN) {
            
            } else {}
        } else if (fp_of_double(z) == pos_inf) {
        
        } else if (fp_of_double(z) == NaN) {
        
        } else {}
    } else { 
    	assert fp_of_double(temp2) == NaN ;
    	if (is_real_double(z)) {
            if (is_real_double(w)) {
                assert fp_of_double(w) == real_double(?rw);
                assert fp_of_double(z) == real_double(?rz);
                assert double_fmax(real_double(rw),real_double(rz)) == real_double(?rm);
            } else if (fp_of_double(w) == pos_inf) {
            
            } else if (fp_of_double(w) == NaN) {
            
            } else {}
        } else if (fp_of_double(z) == pos_inf) {
        
        } else if (fp_of_double(z) == NaN) {
        
        } else {}
    	
    }
}

lemma void fmin_inf_lemma(double min, double x, double y)
    requires fp_of_double(min) == double_fmin(fp_of_double(x), fp_of_double(y)) &*& 
        fp_of_double(min) == pos_inf;
    ensures fp_of_double(x) == pos_inf &*& fp_of_double(y) == pos_inf;
{}

lemma void fmin_lemma(double temp, double x, double y)
    requires fp_of_double(temp) == double_fmin(fp_of_double(x),fp_of_double(y));
    ensures fp_of_double(temp) == fp_of_double(x) || fp_of_double(temp) == fp_of_double(x);
{}
    @*/

#endif
