#!/usr/bin/env python3
"""Exact max-plus query for the prefix representative attack.
A resource limit or failure of this guard is explicitly unresolved.
"""
from functools import lru_cache
import argparse
import json
from verify import SEVEN, need, numerator_words, physical

class BudgetExceeded(Exception):pass

def solver(budget):
    visits=0
    @lru_cache(None)
    def maximum(k,g,r):
        nonlocal visits
        visits+=1
        if visits>budget:raise BudgetExceeded
        if not (0<=g<=k and 0<=r<9*3**g):return None
        if k==0:return 0 if (g,r)==(0,0) else None
        h=SEVEN[(2+k-1)%7];d=1<<(k-1);M=9*3**g;values=[]
        if g<k:
            q=maximum(k-1,g,(r-d*(1-h))%M)
            if q is not None:values.append(q+d*(1-h))
        if g>0 and (r-d*h)%3==0:
            q=maximum(k-1,g-1,((r-d*h)//3)%(M//3))
            if q is not None:values.append(3*q+d*h)
        return max(values) if values else None
    return maximum,lambda:visits

def query(t,cap=None,budget=250000):
    need(type(t) is int and t>=1 and type(budget) is int and budget>=1,'invalid selector input')
    # Guarantee positivity of every possible witness by respecting k<=floor(log2 t).
    need(cap is None or type(cap) is int and cap>=0,'invalid depth cap')
    limit=min(t.bit_length()-1,400) if cap is None else min(cap,t.bit_length()-1,400)
    # The 400-depth safety cap also bounds Python recursion depth.
    mx,count=solver(budget);g=N=0;z=9*t
    for j in range(limit):
        bit=z%2;m=3 if bit==SEVEN[(2+j)%7] else 1;g+=m==3
        N=m*N+(1<<j)*bit;z=(m*z+bit)//2;k=j+1;mod=9*3**g
        try:best=mx(k,g,N%mod)
        except BudgetExceeded:return dict(status='unresolved_resource_cap',t=str(t),completed_depth=k-1,queried_nodes=count())
        need(best is not None and best>=N,'actual source omitted from maximum query')
        d,rem=divmod(best-N,mod);need(rem==0 and 0<=d<t,'not a positive partner')
        if d:
            # Entire source ray t+2^k*v and partner ray t-d+2^k*v, not a seed-only test.
            M=1<<k;L=physical(SEVEN,6*M,6*t,1,k+1)
            need(L==physical(SEVEN,6*M,6*(t-d),1,k+1),'independent partner replay')
            return dict(status='smaller_partner',t=str(t),partner=str(t-d),drop=str(d),both_clocks=k+1,
                        whole_ray_stride=str(M),common_normalized_affine=list(L),queried_nodes=count())
    return dict(status='unresolved_through_depth',t=str(t),completed_depth=limit,queried_nodes=count())

def check():
    checked=0
    for k in range(1,13):
        groups={}
        for g,N in numerator_words(k):
            key=(g,N%(9*3**g));groups[key]=max(N,groups.get(key,-1))
        mx,_=solver(1000000)
        for (g,r),N in groups.items():need(mx(k,g,r)==N,'max-plus group mismatch');checked+=1
    examples=[]
    for t in (148753,231441,234257,247825,2**128+19,2**128+17,2**256+19,2**256+17,2**128+12345):
        out=query(t,cap=96,budget=250000);examples.append(out)
    need(examples[0]['status']=='smaller_partner' and examples[0]['drop']=='1' and examples[0]['both_clocks']==18,'hard progression witness changed')
    need(query(148753,budget=1)['status']=='unresolved_resource_cap','resource failure not explicit')
    return dict(status='PASS',scope='exact reverse maximum recurrence; finite queries and independent physical witness replay; not a total progress proof',
        enumerated_group_maxima_matched=checked,examples=examples,all_seed_capture_proved=False)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--t',type=int);p.add_argument('--cap',type=int);p.add_argument('--budget',type=int,default=250000);a=p.parse_args()
    print(json.dumps(check() if a.t is None else query(a.t,a.cap,a.budget),indent=2,sort_keys=True))
