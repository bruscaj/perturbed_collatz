#!/usr/bin/env python3
"""Exact arithmetic checks for structural B1 obstructions.
The unbounded arguments are in README.md, not extrapolated from these checks.
"""
from math import comb
from collections import defaultdict
from fractions import Fraction as Q
import json
from selector import H,D,need,physical,tick,point

DEN=3**7-2**7
C=[sum(3**(6-j)*2**j*H[j] for j in range(7))]
for p in range(6):
    a=3*C[-1]-DEN*H[p];need(a%2==0,'noninteger center');C.append(a//2)
OFF=tuple(2*C[p]+DEN*(1-2*H[p]) for p in range(7))

def v3(x):
    need(x!=0,'valuation of zero')
    q=0
    while x%3==0:x//=3;q+=1
    return q

def centered_check():
    need(DEN==2059 and C[1:3]==[420,630] and OFF==(2619,2899,3319,-169,2835,3223,-313),'center mismatch')
    for p in range(7):
        need(2*C[(p+1)%7]==3*C[p]-DEN*H[p] and C[p]%2==H[p] and OFF[p]%2,'phase identity')
        for z in range(1,201):
            n=z-1+H[p];p2=(p+1)%7;n2=((3*n+1)//2 if n%2 else n//2)+D[p];z2=n2+1-H[p2]
            w=DEN*z+C[p];w2=DEN*z2+C[p2]
            need(2*w2==(3*w if w%2==0 else w+OFF[p]),'signed center replay')
    return 1400

def one_shrink_check():
    need(max(map(v3,OFF))==4,'offset valuation')
    for d in range(1,5):
        for p in range(7):need(v3(3**d*OFF[p]-2**d*OFF[(p+d)%7])<=4,'one-shrink cancellation bound')
    for j,j2 in ((0,1),(0,2),(1,2)):
        d=j2-j;need(v3(3**d*OFF[(2+j)%7]-2**d*OFF[(2+j2)%7])<j2+2,'early collision')
    # For j>=5, v3(Q)<=4 rules out the all-grow partner. At j=0..4
    # impose integer W0, W0' of the form 9D*t+C2.
    possible=[]
    for j in range(5):
        v=Q(2**j*OFF[(2+j)%7],3**j)
        if v.denominator==1 and (int(v)-2*C[2])%(9*DEN)==0:
            possible.append(j);need(v==2*C[2],'unexpected shift')
    need(possible==[2],'all-grow partner classification')
    # Existing ratio-three case, whole affine signed replay.
    need(physical(18,24,4)[:3]==physical(6,8,4)[:3],'one-shrink ratio-three exception')
    return {'all_grow_partner_shrink_positions':possible,'exception':'t=24v+18, u=8v+6, both clock 4'}

def word_ray(shrinks,k):
    g=N=0
    for j in range(k):
        h=H[(2+j)%7];grow=j not in shrinks;s=h if grow else 1-h
        g+=grow;N=(3 if grow else 1)*N+(1<<j)*s
    M=1<<k;t=(-N*pow(9*3**g,-1,M))%M+M
    # Signed affine replay of the whole source ray.
    e=physical(t,M,k+1);need(e==(9*3**g,(9*3**g*t+N)//M,(2+k)%7,g+1),'sparse word replay')
    return t,g,N

def sparse_check():
    out=[]
    for r in range(1,9):
        c0=3*r+8;B=2*r*c0;Cbound=3**r*2**(r-1)*max(map(abs,OFF))
        need(2*r*Cbound<3**c0,'coefficient envelope')
        # Source shrink positions j_i = (B+1)*i + (i-1), i=1..r.
        J=tuple((B+1)*i+i-1 for i in range(1,r+1));k=J[-1]+1+B
        need(all(j-(i)>=B+1 for i,j in enumerate(J)),'first gap')
        need(all(J[i]-J[i-1]-1>B for i in range(1,r)),'separated shrink guards')
        t,g,N=word_ray(set(J),k);need(g==k-r and t>=2**k,'growth count or height budget')
        # Centered offset from the word. Does not enumerate all competitors.
        A=sum(2**j*3**(g-j+i)*OFF[(2+j)%7] for i,j in enumerate(J))
        need(A==DEN*N+2**k*C[(2+k)%7]-3**g*C[2],'centered numerator identity')
        out.append({'shrinks':r,'minimum_grow_gap':B+1,'post_initial_ticks':k,'source_bits':t.bit_length()})
    # Exhaustive comparisons of all zero/one-shrink groups at small depths.
    n=0
    for k in range(1,21):
        groups=set()
        for j in range(k):
            t,g,N=word_ray({j},k);key=N%(9*3**g)
            need(key not in groups,'one-shrink group collision');groups.add(key);n+=1
    return {'constructed_sparse_rays':out,'one_shrink_words_checked':n}

def uniform_embeddings():
    need(point(1,21)==(1,1,8),'B1 baseline growth index')
    for h in range(121):
        S=109*(128**h-1)//127
        need(S%9==0 if h%6==0 else S%9!=0,'shrink suffix integer criterion')
    out=[]
    for j in range(1,4):
        A=2**(42*j);b=-109*(A-1)//1143
        need(1143*b==-109*(A-1),'noninteger embedding')
        need(physical(A+b,A,42*j+1)[:3]==physical(1,1,1)[:3],'universal affine embedding')
        out.append({'j':j,'partner_clock':42*j+1,'source_clock':1})
    return out

def inverse_ceiling():
    total=Q(0);r=Q(49,50)
    for m in range(1,81):
        l=7*m;g0=next(g for g in range(1,l+1) if 3**g>2**l)
        total+=sum((Q(comb(l-1,g-1),3**g) for g in range(g0,l+1)),Q(0))
    need(3**5<2**8 and Q(8,3)**8/5**5<r**8,'tail bound')
    tail=Q(5,8)*r**(7*81)/(1-r**7)
    need(total<Q(251437,1000000) and tail<Q(51,1000000) and total+tail<Q(63,250),'finite bank ceiling')
    # Explicit ternary guard union for short clocks; exact eventually-valid
    # expanding return domains, not a complete inverse-only search.
    regs=defaultdict(set);counts=[];replays=0
    for l in (7,14,21):
        k=l-1;gmin=next(g for g in range(1,l+1) if 3**g>2**l)-1
        powers={g:3**(g+1) for g in range(gmin,k+1)}
        inv={g:pow(2**l,-1,M) for g,M in powers.items()}
        nword=0;nlegal=0
        def visit(j,g,N):
            nonlocal nword,nlegal,replays
            if g+k-j<gmin:return
            if j==k:
                nword+=1
                if N%3:return
                nlegal+=1;M=powers[g];t=(N//3*inv[g])%M
                regs[g+1].add(t)
                if l<=14:
                    q=max(1,((N//3-2**l*t)//(2**l*M))+1);t0=t+q*M
                    u=(2**l*t0-N//3)//M
                    need(0<u<t0 and physical(u,2**l,l)[:3]==(6*M,6*t0,1),'inverse guard replay');replays+=1
                return
            h=H[(2+j)%7];d=1<<j
            visit(j+1,g,N+d*(1-h));visit(j+1,g+1,3*N+d*h)
        visit(0,0,0)
        need(nword==sum(comb(k,g) for g in range(gmin,k+1)),'expanding word enumeration')
        counts.append({'clock':l,'expanding_words':nword,'B1_target_compatible_words':nlegal})
    accepted={};mass=Q(0)
    for g,rs in sorted(regs.items()):
        good={r for r in rs if all(r%3**h not in ss for h,ss in accepted.items())}
        accepted[g]=good;mass+=Q(len(good),3**g)
    return {'partial_sum_upper_millionths':251437,'tail_upper_millionths':51,'all_finite_bank_upper':'63/250','short_clock_counts':counts,'short_clock_union_density':str(mass),'whole_ray_replays_through_14':replays}

if __name__=='__main__':
    print(json.dumps(dict(status='PASS',scope='exact supporting arithmetic for written obstruction proofs, not kernel verification or global capture',center_checks=centered_check(),one_shrink=one_shrink_check(),sparse=sparse_check(),uniform_embeddings=uniform_embeddings(),inverse_ceiling=inverse_ceiling()),indent=2,sort_keys=True))
