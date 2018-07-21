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

lemma void neg_inf_interval_lemma(struct interval *x, real x1)
    requires x->a |-> ?xa &*& x->b |-> ?xb &*& fp_of_double(xb) == neg_inf &*& between(fp_of_double(xa),fp_of_double(xb),x1) == true;
    ensures fp_of_double(xa) == neg_inf &*& x->a |-> xa &*& x->b |-> xb;
{   
    assert between(fp_of_double(xa),fp_of_double(xb),x1) == true;
    assert leq_real_double(x1,neg_inf) == true;
    assert leq_double_real(fp_of_double(xa),x1) == true;
    if (fp_of_double(xa) != neg_inf){
        assert fp_of_double(xa) == real_double(?rxa);
        real_double_lemma(xa);
    } else {}
}


fixpoint bool leq_double_real(fp_double a, real x){
    switch (a) {
    	case real_double(ra): return ra <= x;
    	case pos_inf: return x > max_dbl / min_pos_dbl;
    	case neg_inf: return true;
    	case NaN: return false;
    }
}

fixpoint bool leq_real_double(real x, fp_double b){
    switch (b) {
    	case real_double(rb): return x <= rb;
    	case pos_inf: return true;
    	case neg_inf: return x < min_dbl / min_pos_dbl;
    	case NaN: return false;
    }
}

fixpoint bool between(fp_double a, fp_double b, real x){
    return leq_double_real(a,x) && leq_real_double(x,b);
}

fixpoint bool is_pos_double(fp_double a){
    switch (a){
        case real_double(ra): return ra >= 0;
        case pos_inf: return true;
        case neg_inf: return false;
        case NaN: return false;
    }
}
    
predicate pos_interval_pred(struct interval *interval, real x) =
    interval->a |-> ?a &*&
    interval->b |-> ?b &*&
    is_pos_double(fp_of_double(a)) == true &*&
    between(fp_of_double(a),fp_of_double(b),x) == true;


predicate interval_pred(struct interval *interval, real x) =
    interval->a |-> ?a &*&
    interval->b |-> ?b &*&
    between(fp_of_double(a),fp_of_double(b),x) == true;
    
lemma void between_lemma(fp_double a, real x, fp_double b)
    requires leq_double_real(a,x) == true &*& leq_real_double(x,b) == true;
    ensures between(a,b,x) == true;
{}
    
  /*  
lemma void lower_bound_lemma(double ra, double sa, double fa, double l, real x1, real x2)
    requires (fp_of_double(l) == pos_inf ? real_mult_gt(rfa,rsa,max_dbl) == true : true);
    ensures leq_double_real(fp_of_double(ra), x1 * x2) == true;
    
{
        switch (fp_of_double(fa)){
        case real_double(rfa):
            switch (fp_of_double(sa)){
                case real_double(rsa):
                    if (fp_of_double(l) == pos_inf){
                        assert real_mult_gt(rfa,rsa,max_dbl) == true;
                        real_mult_gt_lemma(rfa,rsa,max_dbl);
                        assert rfa * rsa > max_dbl;
                        assert x1 >= rfa;
                        assert x2 >= rsa;
                        assert rfa >= 0;
                        assert rsa >= 0;
                        assert x1 * x2 >= rfa * rsa;
                        leq_transitivity_lemma(max_dbl,rfa * rsa, x1 * x2);
                        assert x1 * x2 >= max_dbl;
                        assert fp_of_double(ra) == real_double(?rra);
                        assert fp_of_double(ra) == double_nextafter(fp_of_double(l),neg_inf);
                        assert rra == max_dbl;
                    } else {
                        assert fp_of_double(l) == real_double(?rl);
                        assert fp_of_double(ra) == real_double(?rra);
                        if (rra == 0){
                            assert x1 >= 0;
                            assert x2 >= 0;
                            assert x1 * x2 >= 0;
                            assert leq_double_real(fp_of_double(ra), x1 * x2) == true;
                        } else {
                            assert rra = prev_double(rl);
                            assert rl <= next_double(rfa * rsa);
                            prev_double_transitivity_lemma(rl,next_double(rfa * rsa));
                            prev_next_double_lemma(rfa * rsa, prev_double(next_double(rfa * rsa)));
                        }
                        
                    }
                case pos_inf:
                    if (rfa == 0){
                        assert fp_of_double(l) == real_double(?rl);
                        assert fp_of_double(ra) == real_double(?rra);
                        assert rl == 0;
                        assert rra == 0;
                    } else {
                        min_pos_double_lemma(fa);
                    }
                case neg_inf: assert false;
                case NaN: assert false;
            }
        case pos_inf:
            switch (fp_of_double(sa)){
                case real_double(rsa):
                    if (rsa == 0){
                    
                    } else {
                    
                        min_pos_double_lemma(sa);
                    }
                case pos_inf:
                    assert fp_of_double(ra) == real_double(?rra);
                    assert rra == max_dbl;
                    assert x1 >= max_dbl / min_pos_dbl;
                    assert x2 >= max_dbl / min_pos_dbl;
                    assert x1 * x2 >= max_dbl;
                case neg_inf: assert false;
                case NaN: assert false;
            }
        case neg_inf: assert false;
        case NaN: assert false;
    
    }
*/
@*/



struct interval *double_mult(struct interval *first, struct interval *second)
    /*@ requires pos_interval_pred(first,?x1) &*&
    	pos_interval_pred(second,?x2);@*/
    /*@ ensures pos_interval_pred(first,x1) &*&
    	pos_interval_pred(second,x2) &*&
    	pos_interval_pred(result, x1 * x2) &*&
    	malloc_block_interval(result); @*/
    {
    //@ open pos_interval_pred(first,x1);
    //@ open pos_interval_pred(second,x2);
    struct interval *result = malloc(sizeof(struct interval));
    if (result == 0) { abort(); }
    //@ real_of_int_lemma_UNSAFE(0,0);
    //@ assert first->a |-> ?fa;
    //@ assert first->b |-> ?fb;
    //@ assert second->a |-> ?sa;
    //@ assert second->b |-> ?sb;
    
    
    
    double l = first->a * second->a;
    if (isnan(l)){l = 0;}
    if (l == 0) {
        result->a = 0;
    } else {
        result->a = nextafter(l,-INFINITY);
    }
    //@ assert result->a |-> ?ra;
    //@ assert is_real_double(fa) || fp_of_double(fa) == pos_inf;
    /*@

    switch (fp_of_double(fa)){
        case real_double(rfa):
            switch (fp_of_double(sa)){
                case real_double(rsa):
                    if (fp_of_double(l) == pos_inf){
                        assert real_mult_gt(rfa,rsa,max_dbl) == true;
                        real_mult_gt_lemma(rfa,rsa,max_dbl);
                        assert rfa * rsa > max_dbl;
                        assert x1 >= rfa;
                        assert x2 >= rsa;
                        assert rfa >= 0;
                        assert rsa >= 0;
                        assert x1 * x2 >= rfa * rsa;
                        leq_transitivity_lemma(max_dbl,rfa * rsa, x1 * x2);
                        assert x1 * x2 >= max_dbl;
                        assert fp_of_double(ra) == real_double(?rra);
                        assert fp_of_double(ra) == double_nextafter(fp_of_double(l),neg_inf);
                        assert rra == max_dbl;
                    } else {
                        assert fp_of_double(l) == real_double(?rl);
                        assert fp_of_double(ra) == real_double(?rra);
                        if (rra == 0){
                            assert x1 >= 0;
                            assert x2 >= 0;
                            product_sign_lemma(x1,x2);
                            assert x1 * x2 >= 0;
                            assert leq_double_real(fp_of_double(ra), x1 * x2) == true;
                        } else {
                            assert rra == prev_double(rl);
                            assert real_mult_round_up(rfa,rsa,rl) == true;
                            real_mult_round_up_lemma(rfa,rsa,rl);
                            assert rl <= round_up_double(rfa * rsa) || rfa * rsa > max_dbl;
                            if (rfa * rsa > max_dbl){
                                real_mult_round_down_lemma(rfa,rsa,rl);
                                assert rl >= round_down_double(rfa * rsa);
                                round_down_max_dbl_lemma(rfa * rsa);
                                real_double_lemma(l);
                                assert rl == max_dbl;
                                assert rra == prev_double(rl);
                                prev_double_lemma(rl,rra);
                                assert rra < max_dbl;
                                assert x1 * x2 >= rfa * rsa;
                                leq_transitivity_lemma(max_dbl, rfa * rsa, x1* x2);
                                assert x1 * x2 >= max_dbl;
                                
                            } else {
                                prev_double_transitivity_lemma(rl,round_up_double(rfa * rsa));
                                prev_round_up_lemma(rfa * rsa, prev_double(round_up_double(rfa * rsa)));
                                assert rra <= rfa * rsa;
                                assert rfa * rsa > 0;
                                if (rl == 0){
                                    assert rra == 0;
                                } else {
                                    assert rl > 0;
                                    prev_double_zero_lemma(rl);
                                    assert rra >= 0;
                                }
                            }
                        }
                        
                    }
                case pos_inf:
                    if (rfa == 0){
                        assert fp_of_double(l) == real_double(?rl);
                        assert fp_of_double(ra) == real_double(?rra);
                        assert rl == 0;
                        assert rra == 0;
                    } else {
                        min_pos_double_lemma(fa);
                    }
                case neg_inf: assert false;
                case NaN: assert false;
            }
        case pos_inf:
            switch (fp_of_double(sa)){
                case real_double(rsa):
                    if (rsa == 0){
                    
                    } else {
                    
                        min_pos_double_lemma(sa);
                    }
                case pos_inf:
                    assert fp_of_double(ra) == real_double(?rra);
                    assert rra == max_dbl;
                    assert x1 >= max_dbl / min_pos_dbl;
                    assert x2 >= max_dbl / min_pos_dbl;
                    assert x1 * x2 >= max_dbl;
                case neg_inf: assert false;
                case NaN: assert false;
            }
        case neg_inf: assert false;
        case NaN: assert false;
    
    }
    @*/
    //@ assert is_pos_double(fp_of_double(ra)) == true;
    //@ assert leq_double_real(fp_of_double(ra), x1 * x2) == true;
    double u = first->b * second->b;
    if (isnan(u)){
        result->b = 0;
    } else {
        result->b = nextafter(u,INFINITY);
    }
    //@ assert result->b |-> ?rb;
    /*@

    switch (fp_of_double(fb)){
        case real_double(rfb):
            switch (fp_of_double(sb)){
                case real_double(rsb):
                    if (fp_of_double(u) == pos_inf){
                        assert real_mult_gt(rfb,rsb,max_dbl) == true;
                        real_mult_gt_lemma(rfb,rsb,max_dbl);
                       
                        assert rfb * rsb > max_dbl;
                    } else {
                        assert fp_of_double(u) == real_double(?ru);
                        assert x1 <= rfb;
                        assert x2 <= rsb;
                        assert x1 >= 0;
                        assert x2 >= 0;
                        mult_leq_substitution(x1,x2,rfb,rsb);
                        assert x1 * x2 <= rfb * rsb;
                        if (fp_of_double(rb) == pos_inf){
                            assert ru == max_dbl;
                        } else {
                            assert fp_of_double(rb) == real_double(?rrb);
                            assert rrb == next_double(ru);
                            assert real_mult_round_down(rfb,rsb,ru) == true;
                            real_mult_round_down_lemma(rfb,rsb,ru);
                            assert ru >= round_down_double(rfb * rsb);
                            next_double_transitivity_lemma(round_down_double(rfb * rsb), ru);
                            assert rfb >= 0;
                            assert rsb >= 0;
                            next_round_down_lemma(rfb * rsb, next_double(round_down_double(rfb * rsb)));
                            assert rrb >= rfb * rsb;
                        }
                    }
                case pos_inf:
                case neg_inf: assert false;
                case NaN: assert false;
            }
        case pos_inf:
            switch (fp_of_double(sb)){
                case real_double(rsb):
                case pos_inf:
                    assert leq_double_real(fp_of_double(ra), x1 * x2) == true;
                case neg_inf: assert false;
                case NaN: assert false;
            }
        case neg_inf: assert false;
        case NaN: assert false;
    
    }
    @*/
    /*@

    switch (fp_of_double(fa)){
        case real_double(rfa):
            switch (fp_of_double(sa)){
                case real_double(rsa):
                    if (fp_of_double(l) == pos_inf){
                        assert real_mult_gt(rfa,rsa,max_dbl) == true;
                        real_mult_gt_lemma(rfa,rsa,max_dbl);
                        assert rfa * rsa > max_dbl;
                        assert x1 >= rfa;
                        assert x2 >= rsa;
                        assert rfa >= 0;
                        assert rsa >= 0;
                        mult_leq_substitution(rfa,rsa,x1,x2);
                        assert x1 * x2 >= rfa * rsa;
                        leq_transitivity_lemma(max_dbl,rfa * rsa, x1 * x2);
                        assert x1 * x2 >= max_dbl;
                        assert fp_of_double(ra) == real_double(?rra);
                        assert fp_of_double(ra) == double_nextafter(fp_of_double(l),neg_inf);
                        assert rra == max_dbl;
                    } else {
                        assert fp_of_double(l) == real_double(?rl);
                        assert fp_of_double(ra) == real_double(?rra);
                        if (rra == 0){
                            assert x1 >= 0;
                            assert x2 >= 0;
                            product_sign_lemma(x1,x2);
                            assert x1 * x2 >= 0;
                            assert leq_double_real(fp_of_double(ra), x1 * x2) == true;
                        } else {
                            assert rra == prev_double(rl);
                            assert real_mult_round_up(rfa,rsa,rl) == true;
                            real_mult_round_up_lemma(rfa,rsa,rl);
                            assert rl <= round_up_double(rfa * rsa) || rfa * rsa > max_dbl;
                            if (rfa * rsa > max_dbl){
                                real_mult_round_down_lemma(rfa,rsa,rl);
                                assert rl >= round_down_double(rfa * rsa);
                                round_down_max_dbl_lemma(rfa * rsa);
                                real_double_lemma(l);
                                assert rl == max_dbl;
                                assert rra == prev_double(rl);
                                prev_double_lemma(rl,rra);
                                assert rra < max_dbl;
                                mult_leq_substitution(rfa,rsa,x1,x2);
                                assert x1 * x2 >= rfa * rsa;
                                leq_transitivity_lemma(max_dbl, rfa * rsa, x1* x2);
                                assert x1 * x2 >= max_dbl;
                                
                            } else {
                                prev_double_transitivity_lemma(rl,round_up_double(rfa * rsa));
                                prev_round_up_lemma(rfa * rsa, prev_double(round_up_double(rfa * rsa)));
                                assert rra <= rfa * rsa;
                                assert rfa * rsa > 0;
                                assert x1 * x2 >= rfa * rsa;
                                assert x1 * x2 >= rra;
                                assert rra <= x1 * x2;
				assert leq_double_real(fp_of_double(ra), x1 * x2) == true;
                                if (rl == 0){
                                    assert rra == 0;
                                } else {
                                    assert rl > 0;
                                    prev_double_zero_lemma(rl);
                                    assert rra >= 0;
                                    assert x1 * x2 >= rfa * rsa;
                                    assert x1 * x2 >= rra;
                                    assert rra <= x1 * x2;
                                    assert leq_double_real(fp_of_double(ra), x1 * x2) == true;
                                }
                            }
                        }
                        
                    }
                case pos_inf:
                    if (rfa == 0){
                        assert fp_of_double(l) == real_double(?rl);
                        assert fp_of_double(ra) == real_double(?rra);
                        assert rl == 0;
                        assert rra == 0;
                    } else {
                        min_pos_double_lemma(fa);
                    }
                case neg_inf: assert false;
                case NaN: assert false;
            }
        case pos_inf:
            switch (fp_of_double(sa)){
                case real_double(rsa):
                    if (rsa == 0){
                    
                    } else {
                    
                        min_pos_double_lemma(sa);
                    }
                case pos_inf:
                    assert fp_of_double(ra) == real_double(?rra);
                    assert rra == max_dbl;
                    assert x1 >= max_dbl / min_pos_dbl;
                    assert x2 >= max_dbl / min_pos_dbl;
                    assert x1 * x2 >= max_dbl;
                case neg_inf: assert false;
                case NaN: assert false;
            }
        case neg_inf: assert false;
        case NaN: assert false;
    
    }
    @*/

    //@ assert leq_double_real(fp_of_double(ra), x1 * x2) == true;
    //@ assert leq_real_double(x1 * x2, fp_of_double(rb)) == true;
    //@ assert leq_double_real(fp_of_double(ra), x1 * x2) == true;
    //@ between_lemma(fp_of_double(ra),x1 * x2, fp_of_double(rb));
    //@ assert is_pos_double(fp_of_double(ra)) == true;

    //@ close(pos_interval_pred(result,x1 * x2));
    //@ close(pos_interval_pred(first,x1));
    //@ close(pos_interval_pred(second,x2));
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
lemma void fmax_lemma(double temp2, double w, double z);
    requires fp_of_double(temp2) == double_fmax(fp_of_double(w),fp_of_double(z));
    ensures fp_of_double(temp2) == fp_of_double(w) || fp_of_double(temp2) == fp_of_double(z);

lemma void fmin_inf_lemma(double min, double x, double y);
    requires fp_of_double(min) == double_fmin(fp_of_double(x), fp_of_double(y)) &*& 
        fp_of_double(min) == pos_inf;
    ensures fp_of_double(x) == pos_inf &*& fp_of_double(y) == pos_inf;

lemma void fmin_lemma(double temp, double x, double y);
    requires fp_of_double(temp) == double_fmin(fp_of_double(x),fp_of_double(y));
    ensures fp_of_double(temp) == fp_of_double(x) || fp_of_double(temp) == fp_of_double(x);
    
    @*/

#endif
