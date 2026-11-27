#!/usr/bin/env python3
"""Exhaustive short-partner selector with arbitrary bounded source clock.
Groups all B1 partner parity words by their ternary numerator residue.
Every returned affine witness is independently replayed in the signed model.
"""
from bisect import bisect_right
from collections import defaultdict
from functools import lru_cache
import argparse,json
from selector import H,need,tick,physical,inverse,point

@lru_cache(None)
def table(l):
    need(l>=1,'positive partner clock')
    # After mandatory first U: z=9u at phase two.
    words=[(0,0)]
    for j in range(l-1):
        h=H[(2+j)%7];d=1<<j
        words=[w for g,N in words for w in ((g,N+d*(1-h)),(g+1,3*N+d*h))]
    groups=defaultdict(list)
    for g,N in words:groups[g,N%(9*3**g)].append(N)
    for vals in groups.values():vals.sort()
    need(sum(map(len,groups.values()))==2**(l-1),'incomplete table')
    return groups

def min_ancestor(z,p,l,g):
    """Minimum positive B1 parameter at exact clock l and total grows g."""
    if l==0:return z//6 if p==1 and z%6==0 and g==0 else None
    if (1+l)%7!=p or not 1<=g<=l:return None
    M=9*3**(g-1);N=(1<<(l-1))*z
    vals=table(l).get((g-1,N%M),())
    i=bisect_right(vals,N-M)-1
    if i<0:return None
    u,r=divmod(N-vals[i],M);need(r==0 and u>0,'invalid inverse formula')
    return u

def witness(t,u,k,l,g,gu):
    A=2**k*3**max(gu-g,0);B=2**l*3**max(g-gu,0)
    if A<B or u>=t or u<=0:return None
    s=physical(t,A,k);v=physical(u,B,l)
    need(s[:3]==v[:3] and s[3]==g and v[3]==gu,'signed affine replay mismatch')
    # Backshift to the earliest positive source and partner on this ray.
    q=min((t-1)//A,(u-1)//B)
    t0,u0=t-q*A,u-q*B
    # For A>B, decreasing the base may destroy strictness; keep the first
    # nonnegative lift where the original rank inequality holds.
    if t0<=u0:
        if A==B:raise ValueError('lost strict rank')
        j=(u0-t0)//(A-B)+1;t0+=j*A;u0+=j*B
    need(0<u0<t0 and t>=t0 and (t-t0)%A==0,'bad ray boundary')
    e=physical(t0,A,k);need(e==s[:1]+(s[1]-(t-t0)//A*s[0],s[2],s[3]),'source affine shift')
    ee=physical(u0,B,l);need(e[:3]==ee[:3],'base replay mismatch')
    return dict(status='smaller_partner',t=str(t),u=str(u),source_clock=k,partner_clock=l,source_grows=g,partner_grows=gu,source=[str(A),str(t0)],partner=[str(B),str(u0)],endpoint=[str(e[0]),str(e[1]),e[2]])

def query(t,source_cap=112,partner_cap=14):
    need(t>=1 and 1<=source_cap and 1<=partner_cap<=18,'invalid caps')
    z,p,g=6*t,1,0
    for k in range(1,source_cap+1):
        z,p,h=tick(z,p);g+=h
        # All partner clocks in the allowed congruence class. No beam/pruning.
        for l in range((p-1)%7,partner_cap+1,7):
            if l==0:
                u=min_ancestor(z,p,0,0)
                if u:
                    w=witness(t,u,k,0,g,0)
                    if w:return w
                continue
            for gu in range(l,0,-1):
                if 2**l*3**g>2**k*3**gu:break
                u=min_ancestor(z,p,l,gu)
                if u:
                    w=witness(t,u,k,l,g,gu)
                    if w:return w
    return dict(status='unresolved_through_caps',t=str(t),source_cap=source_cap,partner_cap=partner_cap)

def check():
    n=0
    # Exhaustively compare minimum-positive ancestor queries to literal signed
    # backward branches, including boundaries with zero/negative affine u.
    for p in range(7):
        for z in range(1,161):
            nodes={(z,0)};q=p
            for l in range(0,15):
                if q==1:
                    truth={}
                    for y,g in nodes:
                        if y%6==0:truth[g]=min(truth.get(g,y//6),y//6)
                    for g in range(l+1):
                        need(min_ancestor(z,p,l,g)==truth.get(g),'minimum ancestor mismatch');n+=1
                if l<14:
                    nodes={(y,c+d) for x,c in nodes for y,d in inverse(x,q)};q=(q-1)%7
    ts=[2**b+r for b in (128,256,512) for r in (17,19)]
    examples=[query(t) for t in ts]
    hard=[]
    for h in (4,8,16,32,64,128,256,512):
        M=2**(7*h-1);t=(-70*pow(2059,-1,M))%M+M
        need(point(t,7*h)[2]==7*h,'all-grow prefix mismatch')
        w=query(t,source_cap=100*h+2000,partner_cap=14)
        need(w['status']=='smaller_partner','selected all-grow example unresolved')
        hard.append(dict(h=h,bits=t.bit_length(),**w))
    return dict(status='PASS',scope='complete bounded clock comparison with nonexpanding affine partner stride; positive boundary checked; no universal completeness',minimum_queries_compared=n,examples=examples,all_grow_examples=hard)

if __name__=='__main__':
    a=argparse.ArgumentParser();a.add_argument('--t',type=int);a.add_argument('--source-cap',type=int,default=112);a.add_argument('--partner-cap',type=int,default=14);b=a.parse_args()
    print(json.dumps(check() if b.t is None else query(b.t,b.source_cap,b.partner_cap),indent=2,sort_keys=True))
