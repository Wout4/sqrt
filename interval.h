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


fixpoint bool leq_double_real(fp_double a, real x){
    switch (a) {
    	case real_double(ra): return ra <= x;
    	case pos_inf: return x > max_dbl * 2;
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
    
    double temp1 = fmin(x,y);
    double temp2 = fmin(z,w);
    double l = fmin(temp1,temp2);
    result->a = nextafter(l,-INFINITY);
    //@ assert result->a |-> ?ra1;
    temp1 = fmax(x, y);
    temp2 = fmax(z, w);
    double u = fmax(temp1,temp2);
    result->b = nextafter(u,INFINITY);
    //@ assert result->b |-> ?rb1; 
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


#endif
