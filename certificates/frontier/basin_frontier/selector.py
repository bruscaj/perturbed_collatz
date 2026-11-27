#!/usr/bin/env python3
"""Bounded unequal-clock inverse beam selector. A miss never implies noncapture."""
from collections import defaultdict
import argparse,json
H=(0,0,0,1,0,0,1)
D=(0,0,1,-1,0,1,-1)

def need(x,msg):
    if not x: raise ValueError(msg)

def tick(z,p):
    s=z%2; g=int(s==H[p]);return ((1+2*g)*z+s)//2,(p+1)%7,g

def point(t,k):
    z,p,g=6*t,1,0
    for _ in range(k):
        z,p,h=tick(z,p);g+=h
    return z,p,g

def physical(t,A,k):
    a,n,p,g=6*A,6*t-1,1,0
    for _ in range(k):
        need(a%2==0 and n>=H[p],'invalid whole ray')
        m=3 if n%2 else 1
        g+=m==3
        a,n=m*a//2,(m*n+n%2)//2+D[p];p=(p+1)%7
        need(n>=H[p],'invalid endpoint')
    return a,n+1-H[p],p,g

def inverse(z,p):
    h=H[(p-1)%7]
    a=2*z-(1-h)
    if a>0:yield a,0
    a,r=divmod(2*z-h,3)
    if r==0 and a>0:yield a,1

def beam(z,p,k,g,t,maxdepth,width):
    # At a fixed inverse depth the phase is determined; a state may have
    # only one deterministic forward path to the given endpoint.
    nodes={z:0};total=1
    for l in range(1,maxdepth+1):
        nxt={}
        for x,c in nodes.items():
            for y,b in inverse(x,p):
                if y in nxt:need(nxt[y]==c+b,'ambiguous inverse growth count')
                nxt[y]=c+b
        p=(p-1)%7
        if p==1:
            for y in sorted(nxt):
                if y>=6*t:break
                if y%6:continue
                u=y//6; gu=nxt[y]
                A=2**k*3**max(gu-g,0);B=2**l*3**max(g-gu,0)
                if A<B:continue
                s=physical(t,A,k);v=physical(u,B,l)
                need(s[:3]==v[:3] and s[3]==g and v[3]==gu,'affine replay failed')
                need(A>=B and t>u and u>0,'no strict source rank gap')
                return dict(t=str(t),u=str(u),source_stride=str(A),partner_stride=str(B),source_clock=k,partner_clock=l,source_grows=g,partner_grows=gu,endpoint=[str(s[0]),str(s[1]),s[2]],expanded_nodes=total+len(nxt))
        # Positive ordered heights; losing nodes is deliberate, not a rejection proof.
        nodes=dict(sorted(nxt.items())[:width]);total+=len(nxt)
    return None

def query(t,maxsource=56,maxdepth=112,width=128):
    need(t>=1 and maxsource>=1 and maxdepth>=1 and width>=1,'invalid input')
    z,p,g=6*t,1,0
    for k in range(1,maxsource+1):
        z,p,h=tick(z,p);g+=h
        # At source depth 0 smaller-ancestor-only would not be a viable universal method.
        r=beam(z,p,k,g,t,maxdepth,width)
        if r:return dict(status='smaller_partner',**r)
    return dict(status='unresolved',t=str(t),source_cap=maxsource,inverse_cap=maxdepth,width=width)

def check():
    # Exact parity/branch audit on independent signed physical rays.
    for p in range(7):
        for z in range(1,500):
            y,q,g=tick(z,p)
            need((z,g) in list(inverse(y,q)),'missing inverse')
            for a,b in inverse(y,q):need(tick(a,p)==(y,q,b),'incorrect inverse')
    ts=[2**128+17,2**256+17,2**512+17,2**128+19,2**256+19,2**512+19,2**128+12345]
    # Arbitrarily long all-growing B1 prefixes, using the least positive representative
    # plus one full modulus to remove small-boundary artifacts.
    for h in [1,2,4,8,16,32,64]:
        M=2**(7*h-1);t=(-70*pow(2059,-1,M))%M+M
        need(point(t,7*h)[2]==7*h,'all-growing ray identity')
        ts.append(t)
    results=[query(t) for t in ts]
    return dict(status='PASS',scope='bounded heuristic search; accepted whole-ray identities independently checked; no universal completeness',inverse_point_checks=7*499,examples=results)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--t',type=int);p.add_argument('--maxsource',type=int,default=56);p.add_argument('--maxdepth',type=int,default=112);p.add_argument('--width',type=int,default=128);args=p.parse_args()
    print(json.dumps(check() if args.t is None else query(args.t,args.maxsource,args.maxdepth,args.width),indent=2,sort_keys=True))
