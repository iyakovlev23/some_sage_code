from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.rational_field import QQ
from sage.rings.power_series_ring import PowerSeriesRing
from sage.functions.log import exp, ln
from sage.functions.trig import sin
from sage.functions.other import factorial
from sage.combinat.partition import Partitions
from sage.misc.functional import symbolic_prod as product
from sage.arith.misc import bernoulli, multinomial

def cyl_contrib_min_stratum_series(gmax):
    '''
    Return the series (up to the term t^(2*gmax) included)
            C(t,u) = 1 + sum_{g>=1} (sum_{n=1}^g a_{g,n}*u^n)*(2g-1)*t^(2g)
    where
            a_{g,n} = Vol_n(2g-2) / ( 2*(2*pi)^(2g) / (2g-1)! ) 
    is the normalized contribution of n-cylinder square-tiled surfaces 
    to the Masur-Veech volume of the minimal stratum H(2g-2)
    
    EXAMPLES:
    sage: cyl_contrib_min_stratum_series(3)
    1 + 1/24*u*t^2 + (1/384*u^2 + 1/480*u)*t^4 + (55/82944*u^3 + 1/768*u^2 + 1/1512*u)*t^6 + O(t^8)
    
    '''
    
    P=PolynomialRing(QQ,'u')
    u=P.gen()
    R=PowerSeriesRing(P,'t',default_prec=2*gmax+2)
    t=R.gen()
    S=exp(u*ln((t/2)/sin(t/2)))
    Q=t*exp(sum(factorial(k-1)*S[k]*t**k for k in range(1,2*gmax+1)))
    C=t/Q.reverse()
    return(C)

def cyl_contrib_min_stratum_list(gmax):
    '''
    Return the list of lists of a_{g,n} for 1<=g<=gmax, 1<=n<=g,
    where
            a_{g,n} = Vol_n(2g-2) / ( 2*(2*pi)^(2g) / (2g-1)! ) 
    is the normalized contribution of n-cylinder square-tiled surfaces 
    to the Masur-Veech volume of the minimal stratum H(2g-2)
    
    EXAMPLES:
    sage: cyl_contrib_min_stratum_list(3)
    [[1/24], [1/1440, 1/1152], [1/7560, 1/3840, 11/82944]]
    
    '''
    
    series=cyl_contrib_min_stratum_series(gmax)
    return [[series[2*g][n]/(2*g-1) for n in range(1,g+1)] for g in range(1,gmax+1)]

def tree_coefficients_series(smax):
    '''
    Returns the series (up to the term t^(smax) included)
            T(t,t_2,t_3,...) = 1 + sum_{s>=1, 1<=n<=s} (s-1)*t^s * 1/n! * 
                               sum_{s_1+...+s_n=s} p_{s_1,...,s_n}*t_{s_1}*...*t_{s_n}
                               
    EXAMPLES:
    sage: tree_coefficients_series(5)
    1 + t2*t^2 + 2*t3*t^3 + (3/2*t2^2 + 6*t4)*t^4 + (16*t2*t3 + 24*t5)*t^5 + O(t^6)
    
    '''
    
    P=PolynomialRing(QQ,'t',smax+1)
    ti=P.gens()
    R=PowerSeriesRing(P,'t',default_prec=smax+1)
    t=R.gen()
    S=exp(sum(ti[i]*t**i for i in range(2,smax+1)))
    Q=t*exp(sum(factorial(k-1)*S[k]*t**k for k in range(1,smax+1)))
    T=t/Q.reverse()
    return T

def tree_coefficients_dict(smax):
    '''
    Return the dictionary whose keys are partitions 
        (s_1,...,s_n) with s_i>=2 and s_1+...+s_n<=smax, 
    and values are the corresponding tree coefficients 
        p_{s_1,...,s_n}.
    
    EXAMPLES:
    sage: tree_coefficients_dict(5)
    {[2]: 1, [3]: 1, [4]: 2, [2, 2]: 1, [5]: 6, [3, 2]: 4}
    
    '''
    
    series=tree_coefficients_series(smax)
    res={}
    P=PolynomialRing(QQ,'t',smax+1)
    ti=P.gens()
    for s in range(2,smax+1):
        for p in Partitions(s,min_part=2):
            res[p]=series[s].monomial_coefficient(product(ti[i] for i in p))*product(factorial(i) for i in p.to_exp())/(s-1)
    return res

def cyl_contrib_min_stratum_spin_diff_series(gmax):
    '''
    Return the series (up to the term t^(2*gmax) included)
            D(t,u) = 1 + sum_{g>=1} (sum_{n=1}^g d_{g,n}*u^n)*(2g-1)*t^(2g)
    where
            d_{g,n} = Vol^{diff}_n(2g-2) / ( 2*(2*pi)^(2g) / (2g-1)! ) 
    is the difference of the normalized contributions of n-cylinder 
    square-tiled surfaces to the Masur-Veech volume of even and odd subspaces 
    of the minimal stratum H(2g-2)
    
    EXAMPLES:
    sage: cyl_contrib_min_stratum_spin_diff_series(3)
    1 + 1/24*u*t^2 + (-1/384*u^2 - 1/480*u)*t^4 + (25/82944*u^3 + 1/2304*u^2 + 1/2016*u)*t^6 + O(t^8)
    
    '''
    
    P=PolynomialRing(QQ,'u')
    u=P.gen()
    R=PowerSeriesRing(P,'t',default_prec=2*gmax+2)
    t=R.gen()
    Q = t*exp(u*sum( bernoulli(2*k)/k/2**(k+1) * t**(2*k) for k in range(1,gmax+2)))
    D = (Q.reverse()/t).inverse()
    return D

def cyl_contrib_min_stratum_spin_diff_list(gmax):
    '''
    Return the list of lists of d_{g,n} for 1<=g<=gmax, 1<=n<=g,
    where
            d_{g,n} = Vol^{diff}_n(2g-2) / ( 2*(2*pi)^(2g) / (2g-1)! ) 
    is the difference of the normalized contributions of n-cylinder 
    square-tiled surfaces to the Masur-Veech volume of even and odd subspaces 
    of the minimal stratum H(2g-2)
    
    EXAMPLES:
    sage: cyl_contrib_min_stratum_spin_diff_list(3)
    [[1/24], [-1/1440, -1/1152], [1/10080, 1/11520, 5/82944]]
    
    '''
    
    series=cyl_contrib_min_stratum_spin_diff_series(gmax)
    return [[series[2*g][n]/(2*g-1) for n in range(1,g+1)] for g in range(1,gmax+1)]

def tree_coefficients_delta_series(smax):
    '''
    Returns the series (up to the term t^(smax) included)
            T^{delta}(t,t_2,t_3,...) = 1 + sum_{s>=1, 1<=n<=s} (2s-1)*t^{2s} * 1/n! * 
                               sum_{s_1+...+s_n=s} p^{delta}_{s_1,...,s_n}*t_{s_1}*...*t_{s_n}
                               
    EXAMPLES:
    sage: tree_coefficients_delta_series(3)
    1 - t1*t^2 + (-3/2*t1^2 - 1/2*t2)*t^4 + (-25/6*t1^3 - 5/2*t1*t2 - 1/4*t3)*t^6 + O(t^8)
    
    '''
    
    Pti = PolynomialRing(QQ,'t',smax+1) #t[0] not used
    St = PowerSeriesRing(Pti,'t',default_prec=2*smax+2)
    t = (St.gen(),)+Pti.gens()[1:]
    Q = t[0]*exp(-sum(t[k]/2**(k-1) * t[0]**(2*k) for k in range(1,smax+1)))
    T_delta = (Q.reverse()/t[0]).inverse()
    return T_delta

def tree_coefficients_delta_dict(smax):
    '''
    Return the dictionary whose keys are partitions 
        (s_1,...,s_n) with s_i>=1 and s_1+...+s_n<=smax, 
    and values are the corresponding tree delta coefficients 
        p^{delta}_{s_1,...,s_n}.
    
    EXAMPLES:
    sage: tree_coefficients_delta_dict(3)
    {[1]: -1, [2]: -1/6, [1, 1]: -1, [3]: -1/20, [2, 1]: -1/2, [1, 1, 1]: -5}
    
    '''
    
    series=tree_coefficients_delta_series(smax)
    res={}
    P=PolynomialRing(QQ,'t',smax+1)
    ti=P.gens()
    for s in range(1,smax+1):
        for p in Partitions(s):
            degs=[0]*(smax+1)
            for pi in p:
                degs[pi]+=1
            res[p] = series[2*s][degs]*factorial(len(p))/(2*s-1)/multinomial(degs)
    return res