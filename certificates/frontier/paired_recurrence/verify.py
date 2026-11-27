#!/usr/bin/env python3
"""Exact finite checks accompanying the written countable-pair proof.
No finite check stands in for recurrence, asymptotic estimates, or global capture.
All checks survive python -O. Standard library only.
"""
from collections import Counter, deque
from fractions import Fraction as Q
from functools import lru_cache
from heapq import nlargest
import hashlib
import json
from pathlib import Path

SEVEN=(0,0,0,1,0,0,1)
THREE=(0,1,1)
ORDINARY=(1,)
SCHEDULES=(SEVEN,THREE,ORDINARY)
TERMINALS={
 SEVEN: (('110','10010','10110','11110','11110'),
         ('0010','1110','0100010','1110','0001110'),
         ('110','110','000110','100010','100110'),
         ('10','00010','11010','01110','0100110'),
         ('0010','1110','100110','1110','110100'),
         ('110','110','11110','10110','0111110'),
         ('10','0110','010110','010010','010110')),
 THREE: (('1010','1010110','1110','1010','11011'),
         ('010110','010','00000001','001010','0011'),
         ('10','01010','01110','01010110','01110')),
 ORDINARY: (('001','0001','010001','00001','00001'),)
}

def need(ok,msg):
    if not ok: raise ValueError(msg)

def v2(x):
    need(x!=0,'valuation of zero');x=abs(x);return (x&-x).bit_length()-1

def canon(p,A,B,C,F):
    if (C,F)<(A,B): A,B,C,F=C,F,A,B
    a,r=divmod(C,A);need(A>0 and r==0,'nonintegral slope ratio')
    e=0
    while a>1:
        a,r=divmod(a,3);need(r==0,'nonternary slope ratio');e+=1
    return (p,e,F-3**e*B),A,B

@lru_cache(maxsize=180000)
def tr(H,state,s):
    p,e,b=state;a=3**e;r=(s+b)%2
    m=3 if s==H[p] else 1;n=3 if r==H[p] else 1
    return canon((p+1)%len(H),m,(m*s+s)//2,n*a,(n*(a*s+b)+r)//2)

def physical(H,A,B,p,k):
    # Normalized affine z=A*v+B. Independently use signed physical map.
    for _ in range(k):
        n=B-1+H[p];q=(p+1)%len(H);d=H[q]-H[p]
        need(A>0 and A%2==0 and n>=H[p],'nonuniform/unsafe physical ray')
        if n%2:A,n=3*A//2,(3*n+1)//2+d
        else:A,n=A//2,n//2+d
        p=q;B=n+1-H[p];need(B>0,'unsafe endpoint')
    return A,B,p

def lift(H,state,word):
    modulus,residue,A,B=1,0,1,0
    for ch in word:
        s=int(ch);need(s in (0,1) and A%2==1,'bad parity')
        j=(s-B)%2;residue+=modulus*j;modulus*=2;B+=A*j
        state,C,D=tr(H,state,s);A,B=C*A,C*((B-s)//2)+D
    return state,modulus,residue,A,B

def check_pair_ray(H,state,word):
    dest,M,r,A,B=lift(H,state,word);p,e,b=state
    # Choose a positive common ray, including for negative offsets.
    shift=max(1,1+(-b)//(3**e*M))
    x=M*shift+r
    need(x>0 and 3**e*x+b>0,'bad positive lift')
    L=physical(H,M,x,p,len(word));R=physical(H,M*3**e,3**e*x+b,p,len(word))
    need(L[2]==R[2]==dest[0],'wrong endpoint phase')
    got=canon(dest[0],L[0],L[1],R[0],R[1]);need(got==(dest,A,B+A*shift),'wrong whole affine lift')
    return dest

def transition_audit():
    n=0
    for H in SCHEDULES:
        for p in range(len(H)):
            for e in range(9):
                for b in range(0 if e==0 else -32,33):
                    for s in (0,1):
                        state=(p,e,b);dst,A,B=tr(H,state,s)
                        need(check_pair_ray(H,state,str(s))==dst,'physical transition')
                        if b%2==0:
                            need(dst[1]==e,'even offset changed exponent')
                            if e>0:
                                m=3 if s==H[p] else 1
                                need(2*dst[2]==m*b+s*(1-3**e),'same-exponent formula')
                        else:need(dst[1] in {abs(e-1),e+1},'odd offset exponent')
                        n+=1
    return n

def reach_word(H,state):
    """Construct a merger word from any canonical type by controlling parity.
    This constructs a residue cylinder, not a word chosen by a fixed integer.
    """
    word=[]
    def step(s):
        nonlocal state
        word.append(str(s));state=tr(H,state,s)[0]
    # At a positive level, force an odd offset, then a downward level step.
    while state[1]>0:
        p,e,b=state;L=v2(3**e-1)
        if b%2==0:
            old=v2(b) if b else None
            step(1 if old is None or old>L else 0)
            need(state[1]==e and (state[2]!=0 and (v2(state[2])<L if old is None or old>=L else v2(state[2])==old-1)), 'clock descent')
        else:
            step(H[p]);need(state[1]==e-1,'downward level step')
    while state[2]>5:
        p,e,b=state;old=b
        if b%2==0:step(1-H[p])
        else:
            step(0);need(state[1]==1 and abs(state[2])<=Q(3*b+3,2),'offset departure bound')
            while state[2]%2==0:
                p,_,b1=state
                if abs(b1)>=4:
                    step(1-H[p]);need(abs(state[2])<abs(b1),'even offset not shrinking')
                else:
                    step(0 if b1 else 1);need(state[2]%2==1 and abs(state[2])<=3,'small odd offset exit')
            step(H[state[0]]);need(state[1]==0 and state[2]<=Q(3*old+5,4),'return bound')
        need(state[1]==0 and state[2]<old,'equal-slope descent failed')
    if state[2]:
        for ch in TERMINALS[H][state[0]][state[2]-1]:step(int(ch))
    need(state[1:]==(0,0),'word did not merge')
    return ''.join(word)

def terminal_audit():
    small=large=max_clock=0
    for H in SCHEDULES:
        for p,row in enumerate(TERMINALS[H]):
            for b,w in enumerate(row,1):
                need(check_pair_ray(H,(p,0,b),w)[1:]==(0,0),'small terminal')
                small+=1
            # Large offsets and positive exponent initializations, full affine replays.
            for e,b in [(0,6),(0,7),(0,129),(0,2**60-1),(0,2**60),
                        (1,-2),(1,0),(1,2),(8,-2**25),(16,0),(6,3**6+1)]:
                w=reach_word(H,(p,e,b))
                need(check_pair_ray(H,(p,e,b),w)[1:]==(0,0),'constructive path')
                max_clock=max(max_clock,len(w));large+=1
    return dict(small_whole_ray_terminals=small,constructive_whole_ray_examples=large,max_example_clock=max_clock)

def rational_audit():
    rho=Q(97,100)
    need(Q(15,16)<rho*rho,'square-root drift bound') # sqrt(3)<7/4
    need(3<Q(7,4)**2,'sqrt3 bound')
    need(rho*Q(257,256)**3<1,'weighted Lyapunov contraction')
    need(Q(32,3)**2*Q(5,4)**3<256,'strict drift margin')
    need(100*61<=2**29 and Q(62,61)**2<2,'compact logarithm bound')
    need(Q(1,50)*2**29/256**3-Q(1,32)>Q(1,2),'compact drift margin')
    need(rho**16*Q(3,2)<1,'prefix burn-in contraction')
    for e in range(1,129):
        L=v2(3**e-1);need(L==(1 if e%2 else 2+v2(e)) and L<=e+1,'LTE sanity')
    need(3**28<2**45,'stopped-prefix inverse slope')
    R=Q(6,5)**12/Q(7,5)**7
    need(8*R**16<1,'stopped-prefix Chernoff bound')
    R=Q(14,11)**28/Q(17,11)**17
    need(2**28*R**30<1 and 3**510<2**812,'fixed-prefix Chernoff and representative exponent')
    return dict(square_root_drift_rho='97/100',compact_offset_exclusive_bound=str(2**60),
                embedded_drift_at_large_positive_level='<= -1/(32*(e+257)^(3/2))',
                finite_rational_checks=True,small_exponent_LTE_examples=128,
                fixed_prefix_candidate_exponent='29/30',stopped_prefix_tail_exponent='1/64')

def numerator_words(k):
    arr=[(0,0)]
    for i in range(k):
        h=SEVEN[(2+i)%7];arr=[(g+(s==h),(3 if s==h else 1)*N+(1<<i)*s) for g,N in arr for s in (0,1)]
    return arr

def representatives(k):
    arr=numerator_words(k);M=1<<k
    need(len(arr)==M,'word count')
    pow3=[3**g for g in range(k+1)];inv=[pow(9*a,-1,M) for a in pow3]
    groups={};seen=set()
    for g,N in arr:
        r=-N*inv[g]%M;need(r not in seen,'residue bijection failed');seen.add(r)
        key=g,N%(9*pow3[g]);groups[key]=max(N,groups.get(key,-1))
        need(0<=N<pow3[g]*M,'numerator bound')
    no_smaller={(-N*inv[g])%M for (g,_),N in groups.items()}
    need(len(no_smaller)==len(groups),'maximum representative collision')
    return arr,groups,no_smaller,pow3,inv

def prefix_audit():
    out=[];old_survivors=None;old_k=0
    for k in (7,10,14,18,20):
        arr,groups,survivors,p3,inv=representatives(k);M=1<<k
        if old_survivors is not None:need(all(r%(1<<old_k) in old_survivors for r in survivors),'not prefix closed')
        old_survivors=survivors;old_k=k
        # Independently replay every source ray and every claimed partner through k=14.
        verified=0
        if k<=14:
            for g,N in arr:
                r=(-N*inv[g])%M;t=M+r
                y=physical(SEVEN,6*M,6*t,1,k+1)
                need(y==(9*p3[g],(9*p3[g]*t+N)//M,(2+k)%7),'B1 word endpoint mismatch')
                d,rem=divmod(groups[g,N%(9*p3[g])]-N,9*p3[g]);need(rem==0 and 0<=d<t,'invalid smaller B1 partner')
                if d:need(y==physical(SEVEN,6*M,6*(t-d),1,k+1),'smaller B1 partner mismatch')
                verified+=1
        row=dict(after_initial_ticks=k,source_rays=M,maximum_representatives=len(survivors),smaller_partner_rays=M-len(survivors),
                 fraction_smaller_partner=str(Q(M-len(survivors),M)),independent_physical_source_rays=verified)
        for label,mod,res in [('19_mod128',128,19),('17_mod256',256,17)]:
            if M>=mod:
                left=sum(r%mod==res for r in survivors);row[label]=dict(total=M//mod,unresolved_maxima=left,accepted=M//mod-left)
        out.append(row)
    return out

def finite_merger_lower_bound(H,state,cap=12000,horizon=128):
    """Exact integer masses, deterministic pruning. Discarded mass never counted.
    Lower bounds are not claimed to be exact full-horizon fractions after pruning.
    """
    live={state:1};merged=discarded=0;out=[]
    for k in range(1,horizon+1):
        nxt=Counter();merged*=2;discarded*=2
        for s,c in live.items():
            for bit in (0,1):
                dst=tr(H,s,bit)[0]
                if dst[1:]==(0,0):merged+=c
                else:nxt[dst]+=c
        if len(nxt)>cap:
            keep=nlargest(cap,nxt.items(),key=lambda a:(a[1],a[0]));discarded+=sum(nxt.values())-sum(c for _,c in keep);live=dict(keep)
        else:live=dict(nxt)
        need(merged+discarded+sum(live.values())==2**k,'mass conservation')
        if k in (14,32,64,128):out.append(dict(ticks=k,lower_bound=str(Q(merged,2**k)),discarded_mass=str(Q(discarded,2**k)),retained_states=len(live)))
    return out

def all_grow_audit():
    # Arbitrarily long all-grow physical histories; these examples test the universal formula.
    checks=[]
    for h in (1,2,3,8,20):
        k=7*h;M=2**(k-1);r=-70*pow(2059,-1,M)%M;t=r if r else M
        end=physical(SEVEN,6*M,6*t,1,k)
        # Normalized affine all-grow period has numerator 2187*z+420.
        z=6*t;p=1
        for _ in range(k):
            need(z%2==SEVEN[p],'all-grow guard');z=(3*z+SEVEN[p])//2;p=(p+1)%7
        need(end==(3*3**k,z,1),'all-grow affine endpoint')
        checks.append(dict(laps=h,t_residue=str(r),t_modulus=str(M),whole_ray_checked=True))
    return checks

def cycles_audit():
    D=(1,0,-1)
    C=(((0,0),(1,1),(2,2)),((1,0),(3,1),(5,2),(7,0),(12,1),(6,2),(2,0),(2,1),(1,2)))
    for cycle in C:
        for i,(n,p) in enumerate(cycle):
            y=(n//2 if n%2==0 else (3*n+1)//2)+D[p]
            need((y,(p+1)%3)==cycle[(i+1)%len(cycle)],'invalid negative-control cycle')
            need(n>=THREE[p],'unsafe cycle')
    need(not(set(C[0])&set(C[1])),'negative control cycles overlap')
    return [list(c) for c in C]

def main():
    report=dict(status='PASS',scope='finite arithmetic and physical replay only; written probability proof is separate',
      exact_transition_rays=transition_audit(),terminals=terminal_audit(),rational_inequalities=rational_audit(),
      prefix_representatives=prefix_audit(),all_growing_prefixes=all_grow_audit(),two_cycle_negative_control=cycles_audit(),
      finite_merger_bounds={name:finite_merger_lower_bound(SEVEN,s) for name,s in [('B1_neighbor',(2,0,9)),('B1_19_mod128',(2,0,3)),('A3',(2,0,2))]},
      all_seed_capture_proved=False,pointwise_pair_merger_proved=False,lean_run=False)
    print(json.dumps(report,indent=2,sort_keys=True))

if __name__=='__main__':main()
