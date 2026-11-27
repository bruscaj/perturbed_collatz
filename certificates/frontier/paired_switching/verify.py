#!/usr/bin/env python3
"""Exact paired-state renewal and terminating repayment certificates.
No external dependencies. All checks survive python -O.
"""
from collections import Counter
from fractions import Fraction as Q
from functools import lru_cache
import json

H=(0,0,0,1,0,0,1)
D=(0,0,1,-1,0,1,-1)
SHARED=((2,0,2),(3,0,3),(4,1,5),(5,2,3),(6,1,2),(0,1,2),(1,1,3))
INTERNAL=(0,0,1,0,1,0,0)
OFFSETS=(468,702,351,118,177,208,312)
EXITS=((3,0,1),(4,1,-4),(5,0,3),(6,3,-9),(0,1,1))
ROOT=SHARED[0]
CORE=tuple(sorted(set(SHARED+EXITS+tuple((p,e,0) for p in range(7) for e in (1,2))+((2,0,9),(2,0,3)))))
L=14
# Each type is (phase, exponent, offset); pair (x,3**exponent*x+offset).
# Canonical orientation orders affine slopes then intercepts, not point values.

def need(ok,msg):
    if not ok: raise ValueError(msg)

def canon(p,A,B,C,F):
    swap=(C,F)<(A,B)
    if swap: A,B,C,F=C,F,A,B
    ratio,rem=divmod(C,A)
    need(A>0 and rem==0,'nonintegral slope ratio')
    e=0
    while ratio>1:
        need(ratio%3==0,'slope ratio not a power of three')
        ratio//=3; e+=1
    return (p,e,F-3**e*B),A,B,swap

def transition(s,bit):
    p,e,b=s; a=3**e; bit2=(a*bit+b)%2
    m=3 if bit==H[p] else 1
    n=3 if bit2==H[p] else 1
    return canon((p+1)%7,m,(m*bit+bit)//2,n*a,(n*(a*bit+b)+bit2)//2)

def tick(a,b,p):
    # Independent literal signed physical recurrence on z=a*v+b, v>=0.
    n=b-1+H[p]
    need(a>0 and a%2==0 and n>=H[p],'unsafe or nonuniform physical ray')
    if n%2: a,n=3*a//2,(3*n+1)//2+D[p]
    else: a,n=a//2,n//2+D[p]
    q=(p+1)%7
    need(n>=H[q],'unsafe physical endpoint')
    return a,n+1-H[q]

def replay(a,b,p,k):
    for _ in range(k):
        a,b=tick(a,b,p);p=(p+1)%7
    return a,b,p

def physical_pair(a,b,s,k):
    p,e,c=s
    A,B,q=replay(a,b,p,k)
    C,F,q2=replay(3**e*a,3**e*b+c,p,k)
    need(q==q2,'phase mismatch')
    return canon(q,A,B,C,F)

def classify(s):
    if s[1:]==(0,0): return 'merge'
    if s in CORE: return s
    return None

@lru_cache(None)
def stop(s,k):
    dest=classify(s)
    if dest is not None: return {dest:2**k}
    if k==0: return {'unresolved':1}
    out=Counter()
    for bit in (0,1): out.update(stop(transition(s,bit)[0],k-1))
    return dict(out)

def row(s):
    out=Counter()
    for bit in (0,1): out.update(stop(transition(s,bit)[0],L-1))
    need(sum(out.values())==2**L,'nonexhaustive row')
    return dict(out)

def independent_row(s):
    out=Counter(); M=2**L;p,e,b=s
    for r in range(M):
        A,B=M,M+r;C,F=3**e*A,3**e*B+b;phase=p
        for _ in range(L):
            A,B=tick(A,B,phase);C,F=tick(C,F,phase);phase=(phase+1)%7
            typ,*_=canon(phase,A,B,C,F)
            dest=classify(typ)
            if dest is not None: break
        else: dest='unresolved'
        out[dest]+=1
    return dict(out)

def solve(rows):
    n=len(CORE); idx={s:i for i,s in enumerate(CORE)};M=2**L
    a=[[Q(M if i==j else 0) for j in range(n)]+[Q(rows[s].get('merge',0))] for i,s in enumerate(CORE)]
    for i,s in enumerate(CORE):
        for t,c in rows[s].items():
            if t in idx:a[i][idx[t]]-=c
    for j in range(n):
        piv=next((i for i in range(j,n) if a[i][j]),None)
        need(piv is not None,'singular renewal equations')
        a[j],a[piv]=a[piv],a[j]; d=a[j][j]; a[j]=[v/d for v in a[j]]
        for i in range(n):
            if i!=j and a[i][j]:
                d=a[i][j];a[i]=[v-d*w for v,w in zip(a[i],a[j])]
    sol={s:a[i][-1] for i,s in enumerate(CORE)}
    for s in CORE:
        need(0<=sol[s]<=1 and M*sol[s]==rows[s].get('merge',0)+sum(c*sol[t] for t,c in rows[s].items() if t in sol),'bad probability solution')
    return sol

def survival(rows):
    M=2**L; v={s:Q(1) for s in CORE}
    for _ in range(2):v={s:sum((Q(c,M)*v[t] for t,c in rows[s].items() if t in v),Q(0)) for s in CORE}
    d=max(v.values());need(d==Q(26837,32768)<1,'two-visit tail certificate changed')
    return d

# Exact lift of any finite canonical parity word; each additional bit fixes
# one new input binary digit and leaves an odd endpoint coefficient.
def path_ray(s,word):
    M,r,a,b,sw=1,0,1,0,False
    for ch in word:
        bit=int(ch);need(bit in (0,1) and a%2==1,'invalid parity word')
        j=(bit-b)%2;r+=M*j;M*=2;b+=a*j
        s,A,B,flipped=transition(s,bit)
        a,b=A*a,A*((b-bit)//2)+B;sw^=flipped
    return s,M,r,a,b,sw

WORDS={'E':'0010100','K':'1000110','A':'10100001100000','B':'10010101101000','T':'110'}
MACROS={'E':(128,36,243,72,False),'K':(128,111,81,72,False),
        'A':(16384,15227,2187,2034,True),'B':(16384,10695,729,477,True),
        'T':(8,5,3,3,False)}

def packet_primitives():
    for name,(M,r,A,B,sw) in MACROS.items():
        dst=(5,0,0) if name=='T' else ROOT
        out=path_ray(ROOT,WORDS[name]);need(out[:5]==(dst,M,r,A,B),'macro parity/endpoint mismatch')
        physical=physical_pair(M,r,ROOT,len(WORDS[name]))
        need(physical[:3]==(dst,A,B),'macro literal physical mismatch')
        if name!='T':need(physical[3]==sw and out[-1]==sw,'orientation mismatch')
    for name in ('A','B'):
        M,r,A,B,_=MACROS[name]
        need(M>7*A and 115*r+468>7*(115*B+468),'contractive envelope failed')
    M,r,A,B,_=MACROS['K'];need(A<M and B<r,'K is not contracting')
    need(Q(243,128)**3<7,'repayment inequality failed')
    need(128*(115*72+468)==243*(115*36+468),'counter offset mismatch')
    for i,(M,r,*_) in enumerate(MACROS.values()):
        for N,s,*_ in list(MACROS.values())[:i]:need((r-s)%min(M,N)!=0,'overlapping macro guards')

def macro(x):
    for name,(M,r,A,B,_) in MACROS.items():
        if x%M==r:return name,A*(x//M)+B
    return None,x

def packet_decode(x):
    need(type(x) is int and x>0,'positive integer x required')
    clock=0
    while True:
        anchor=x;h=0;name,y=macro(x)
        while name=='E':
            need((115*x+468)%128==0 and 128*(115*y+468)==243*(115*x+468),'invalid E counter')
            x=y;h+=1;clock+=7;name,y=macro(x)
        if h==0:
            if name=='T':return 'merge',clock+3
            if name not in ('K','A','B'):return 'unresolved',clock
            x=y;clock+=len(WORDS[name])
        else:
            for _ in range((h+2)//3):
                name,y=macro(x)
                if name=='T':return 'merge',clock+3
                if name not in ('A','B'):return 'unresolved',clock
                x=y;clock+=14
        need(x<anchor,'packet failed to repay original coordinate')

def packet_density():
    e=k=Q(1,128);c=Q(2,16384);m=Q(1,8)
    restart=(e+e**2+e**3)*c/(1-e**3*c)
    direct=m+m*(e/(1-e)-restart)/(1-c)
    return direct/(1-k-c-restart)

def initializations():
    need(replay(768,108,1,8)==(243,35,2),'B1 lower initializer')
    need(replay(768,114,1,8)==(243,38,2),'B1 upper initializer')
    need(physical_pair(128,111,(2,0,3),7)[:3]==(ROOT,81,72),'neighbor to D2 adapter')
    need(replay(6*16384,6*530,1,15)==(19683,639,2),'adapted lower initializer')
    need(replay(6*16384,6*531,1,15)==(19683,641,2),'adapted upper initializer')
    need(replay(192,57,3,6)==(243,74,2) and replay(144,42,5,4)==(243,72,2),'A3 initializer')
    need(replay(12288,3486,5,12)==(19683,5586,3) and replay(4608,1308,1,9)==(19683,5589,3),'N03 initializer')
    need(replay(6,6,1,1)==(9,9,2) and replay(6,12,1,1)==(9,18,2),'B1 adjacent initializer')

def examples():
    out=[]
    for seq in ('T','EEEAEEEEEEBAEBT','KAEBA T'.replace(' ','')):
        word=''.join(WORDS[c] for c in seq)
        dst,M,r,A,B,_=path_ray(ROOT,word)
        need(dst[1:]==(0,0),'example not a terminal path')
        w=(r-639)*pow(19683,-1,M)%M;t=16384*w+531
        k=15+len(word);a=6*16384*M
        need(replay(a,6*t,1,k)==replay(a,6*(t-1),1,k),'whole-ray source merger failed')
        x=19683*w+639
        need(packet_decode(x)==('merge',len(word)),'packet decoder rejected constructed word')
        out.append({'word':seq,'t0':str(t),'stride':str(16384*M),'both_clocks':k})
    return out

def shared_exits(sol):
    # Short whole-ray terminals starting on the exit (complementary parity).
    terms=((8,5,3),(32,27,5),(64,46,6),(128,97,7),(16,14,4),(8,5,3),(128,117,7))
    exit_probs=[];endpoints=[]
    for i,(s,bit,c) in enumerate(zip(SHARED,INTERNAL,OFFSETS)):
        nxt,A,B,_=transition(s,bit);need(nxt==SHARED[(i+1)%7],'bad shared edge')
        # x=2v+bit, 2*C_next=A*C_source
        need(2*(115*B+OFFSETS[(i+1)%7])==A*(115*bit+c),'shared counter identity')
        dst=transition(s,1-bit)[0];need(dst in sol,'exit not a core type')
        exit_probs.append(sol[dst]);M,r,k=terms[i]
        result=physical_pair(M,r,s,k);need(result[0][1:]==(0,0) and r%2==1-bit,'bad exit terminal')
        endpoints.append({'mode':i,'modulus':M,'residue':r,'clock':k,'endpoint':[result[1],result[2],result[0][0]],'continuation_density':str(sol[dst])})
    for i,s in enumerate(SHARED):
        d=sum((Q(1,2**(j+1))*exit_probs[(i+j)%7] for j in range(7)),Q(0))/(1-Q(1,128))
        need(d==sol[s],'shared arbitrary-depth geometric identity')
    return endpoints

def main():
    initializations();packet_primitives();ex=examples()
    rows={s:row(s) for s in CORE}
    for s in CORE:need(rows[s]==independent_row(s),'independent whole-ray row differs: '+str(s))
    tail=survival(rows);sol=solve(rows);exits=shared_exits(sol)
    labels={'B1_ratio3_W':(2,1,0),'A3_difference2_u':ROOT,'N03_difference3_v':(3,0,3),
            'B1_neighbor_t':(2,0,9),'B1_neighbor_19_mod128_v':(2,0,3)}
    result={'status':'PASS','horizon':L,'core_count':len(CORE),'whole_affine_rows':len(CORE)*2**L,
        'two_macro_survival_max':str(tail),'densities':{name:str(sol[s]) for name,s in labels.items()},
        'all_core_densities':{str(s):str(sol[s]) for s in CORE},
        'matrix_counts':{str(s):{str(t):c for t,c in rows[s].items()} for s in CORE},
        'all_seven_exits':exits,'packet_density':str(packet_density()),'packet_examples':ex,
        'pointwise_total_packet_decoder':True,'unrestricted_renewal_termination_proved':False,'all_seed_capture_proved':False}
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=='__main__':main()
