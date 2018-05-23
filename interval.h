#ifndef INTERVAL_H
#define INTERVAL_H
#include "stdlib.h"
#include "math.h"



struct interval {
    double a;
    double b;
};

struct interval *double_add(struct interval *first, struct interval *second)
    /*@ requires interval_a(first,?fa) &*&
    	real_of_double(fa) == some(?rfa) &*&
    	interval_b(first,?fb) &*&
    	real_of_double(fb) == some(?rfb) &*&
    	interval_a(second,?sa) &*&
    	real_of_double(sa) == some(?rsa) &*&
    	interval_b(second,?sb) &*&
    	real_of_double(sb) == some(?rsb) &*&
    	rfa >= 0 &*&
    	rsa >= 0 &*&
    	rfb >= 0 &*&
    	rsb >= 0;@*/
    /*@ ensures interval_a(first,fa) &*&
    	interval_b(first,fb) &*&
    	interval_a(second,sa) &*&
    	interval_b(second,sb) &*&
    	interval_a(result,?ra) &*&
    	real_of_double(ra) == some(?rra) &*&
    	interval_b(result,?rb) &*&
    	real_of_double(rb) == some(?rrb) &*&
    	malloc_block_interval(result) &*&
    	rra <= rfa + rsa &*&
    	rrb >= rfb + rsb &*&
    	rra >= (rfa + rsa) * (1 - d_eps) * (1 - d_eps) &*&
    	rrb <= (rfb + rsb) * (1 + d_eps) * (1 + d_eps); @*/
    {
    struct interval *result = malloc(sizeof(struct interval));
    if (result == 0) { abort(); }
    double l = first->a + second->a;
    //@ assert real_of_double(l) == some(?rl);
    //@ assert relative_error(rfa + rsa,rl,d_eps) == true;
    //@ assert rl <= rfa + rsa + real_abs((rfa + rsa) * d_eps);
    result->a = nextafter(l,-INFINITY);
    //@ assert result->a |-> ?ra1;
    //@ assert real_of_double(ra1) == some(?rra1);
    //@ prev_lemma(rl, prev(rl));
    /*@ if (rl == rfa + rsa) {
    
    } else if (rl == next(rfa + rsa)) {
    	assert rra1 == prev(next(rfa + rsa));
    	prev_next_lemma(rfa + rsa, rra1);
    	assert rra1 <= rfa + rsa;
    } else {
    	assert rl == prev(rfa + rsa);
    	assert rra1 == prev(rl);
    	prev_lemma(rfa + rsa, rl);
    	assert rl < rfa + rsa;
    	assert rra1 < rl;
    	assert rra1 <= rfa + rsa;
    }
    @*/
    //@ assert rra1 <= rl;
    double u = first->b + second->b;
    //@ assert real_of_double(u) == some(?ru);
    //@ assert ru == rfb + rsb || ru == next(rfb + rsb) || ru == prev(rfb + rsb);
    //@ assert relative_error(rfb + rsb,ru,d_eps) == true;
    //@ assert ru >= (rfb + rsb) - real_abs((rfb + rsb) * d_eps);
    result->b = nextafter(u,INFINITY);
    //@ assert result->b |-> ?rb1; 
    //@ assert real_of_double(rb1) == some(?rrb1);
    //@ next_lemma(ru, next(ru));
    //@ next_lemma(rfb + rsb, next(rfb + rsb));
    /*@ if (ru == rfb + rsb) {
    	assert rrb1 == next(ru);
    	assert rrb1 == next(rfb + rsb);
    	assert rrb1 >= rfb + rsb;
    	assert rrb1 <= (rfb + rsb) * (1 + d_eps);
    } else if (ru == next(rfb + rsb)) {
    	assert rrb1 == next(ru);
    	assert rrb1 == next(next(rfb + rsb));
    	assert ru <= (rfb + rsb) * (1 + d_eps);
    	assert rrb1 <= ru * (1 + d_eps);
    	assert rrb1 <= (rfb + rsb) * (1 + d_eps) * (1 + d_eps);
    } else {
    	assert ru == prev(rfb + rsb);
    	assert rrb1 == next(ru);
    	assert rrb1 == next(prev(rfb + rsb));
    	next_prev_lemma(rfb + rsb,rrb1);
    	assert rrb1 >= rfb + rsb;
    }
    @*/

    
    return result;
}



struct interval *double_sub(struct interval *first, struct interval *second)
    /*@ requires interval_a(first,?fa) &*&
    	real_of_double(fa) == some(?rfa) &*&
    	interval_b(first,?fb) &*&
    	real_of_double(fb) == some(?rfb) &*&
    	interval_a(second,?sa) &*&
    	real_of_double(sa) == some(?rsa) &*&
    	interval_b(second,?sb) &*&
    	real_of_double(sb) == some(?rsb) &*&
    	rfa >= 0 &*&
    	rsa >= 0 &*&
    	rfb >= 0 &*&
    	rsb >= 0 &*&
    	rfa >= rsb &*&
    	rfb >= rsa;@*/
    /*@ ensures interval_a(first,fa) &*&
    	interval_b(first,fb) &*&
    	interval_a(second,sa) &*&
    	interval_b(second,sb) &*&
    	interval_a(result,?ra) &*&
    	real_of_double(ra) == some(?rra) &*&
    	interval_b(result,?rb) &*&
    	real_of_double(rb) == some(?rrb) &*&
    	malloc_block_interval(result) &*&
    	rra <= rfa - rsb &*&
    	rrb >= rfb - rsa &*&
    	rra >= (rfa - rsb) * (1 - d_eps) * (1 - d_eps) &*&
    	rrb <= (rfb - rsa) * (1 + d_eps) * (1 + d_eps); @*/
    {
    struct interval *result = malloc(sizeof(struct interval));
    if (result == 0) { abort(); }
    double l = first->a - second->b;
    //@ real_of_double_lemma(second->b);
    //@ assert real_of_double(l) == some(?rl);
    result->a = nextafter(l,-INFINITY);
    //@ assert result->a |-> ?ra1;
    //@ assert real_of_double(ra1) == some(?rra1);
    //@ prev_lemma(rl, prev(rl));
    //@ prev_lemma(rfa - rsb, prev(rfa - rsb));
    //@ assert rra1 == prev(rl);
    /*@ if (rl == rfa - rsb){
    	assert rra1 == prev(rfa - rsb);
    	assert rra1 >= (rfa - rsb) * (1 - d_eps) ;
    } else if (rl == next(rfa - rsb)){
    	assert rra1 == prev(next(rfa - rsb));
    	prev_next_lemma(rfa - rsb, rra1);
    	assert rra1 >= (rfa - rsb) * (1 - d_eps) * (1 - d_eps);
    } else {
        assert rra1 == prev(prev(rfa - rsb));
        prev_lemma(rfa - rsb, rl);
        assert rra1 >= (rfa - rsb) * (1 - d_eps) * (1 - d_eps);
    }
    @*/
    double u = first->b - second->a;
    //@ real_of_double_lemma(second->a);
    //@ assert real_of_double(u) == some(?ru);
    
    result->b = nextafter(u,INFINITY);
    //@ assert result->b |-> ?rb1;
    //@ assert real_of_double(rb1) == some(?rrb1);
    //@ next_lemma(ru,next(ru));
    //@ next_lemma(rfb - rsa, next(rfb - rsa));
    //@ next_prev_lemma(rfb - rsa, next(prev(rfb - rsa)));
    return result;
}

struct interval *double_mult(struct interval *first, struct interval *second)
    /*@ requires interval_a(first,?fa) &*&
    	real_of_double(fa) == some(?rfa) &*&
    	interval_b(first,?fb) &*&
    	real_of_double(fb) == some(?rfb) &*&
    	interval_a(second,?sa) &*&
    	real_of_double(sa) == some(?rsa) &*&
    	interval_b(second,?sb) &*&
    	real_of_double(sb) == some(?rsb) &*&
    	rfa >= 0 &*&
    	rsa >= 0 &*&
    	rfb >= 0 &*&
    	rsb >= 0;@*/
    /*@ ensures interval_a(first,fa) &*&
    	interval_b(first,fb) &*&
    	interval_a(second,sa) &*&
    	interval_b(second,sb) &*&
    	interval_a(result,?ra) &*&
    	real_of_double(ra) == some(?rra) &*&
    	interval_b(result,?rb) &*&
    	real_of_double(rb) == some(?rrb) &*&
    	malloc_block_interval(result) &*&
    	rra <= rfa * rsa &*&
    	rrb >= rfb * rsb &*&
    	rra >= (rfa * rsa) * (1 - d_eps) * (1 - d_eps) &*&
    	rrb <= (rfb * rsb) * (1 + d_eps) * (1 + d_eps); @*/
    {
    struct interval *result = malloc(sizeof(struct interval));
    if (result == 0) { abort(); }
    double l = first->a * second->a;
    //@ assert real_of_double(l) == some(?rl);
    result->a = nextafter(l,-INFINITY);
    //@ assert result->a |-> ?ra1;
    //@ assert real_of_double(ra1) == some(?rra1);
    //@ prev_lemma(rl, prev(rl));
    //@ product_sign_lemma(rfa, rsa);
    /*@ if (rl == rfa * rsa) {
    } else if (rl == next(rfa * rsa)) {
    	assert rra1 == prev(next(rfa * rsa));
    	prev_next_lemma(rfa * rsa, rra1);
    	assert rra1 <= rfa * rsa;
    } else {
    	assert rl == prev(rfa * rsa);
    	assert rra1 == prev(rl);
    	prev_lemma(rfa * rsa, rl);
    	assert rl < rfa * rsa;
    	assert rra1 < rl;
    	assert rra1 <= rfa * rsa;
    }
    @*/
    double u = first->b * second->b;
    //@ assert real_of_double(u) == some(?ru);
    result->b = nextafter(u,INFINITY);
    //@ assert result->b |-> ?rb1; 
    //@ assert real_of_double(rb1) == some(?rrb1);
    //@ next_lemma(ru, next(ru));
    //@ next_lemma(rfb * rsb, next(rfb * rsb));
    //@ product_sign_lemma(rfb,rsb);
    /*@ if (ru == rfb * rsb) {
    	assert rrb1 == next(ru);
    	assert rrb1 == next(rfb * rsb);
    	assert rrb1 >= rfb * rsb;
    	assert rrb1 <= (rfb * rsb) * (1 + d_eps);
    } else if (ru == next(rfb * rsb)) {
    	assert rrb1 == next(ru);
    	assert rrb1 == next(next(rfb * rsb));
    	assert ru <= (rfb * rsb) * (1 + d_eps);
    	assert rrb1 <= ru * (1 + d_eps);
    	assert rrb1 <= (rfb * rsb) * (1 + d_eps) * (1 + d_eps);
    } else {
    	assert ru == prev(rfb * rsb);
    	assert rrb1 == next(ru);
    	assert rrb1 == next(prev(rfb * rsb));
    	next_prev_lemma(rfb * rsb,rrb1);
    	assert rrb1 >= rfb * rsb;
    }
    @*/

    return result;
}

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
    /*@ ensures interval_a(first,fa) &*&
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
    	{
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
    double u = first->b / second->a;
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
