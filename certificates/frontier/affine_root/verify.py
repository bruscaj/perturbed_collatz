#!/usr/bin/env python3
"""Exact whole-ray verifier for the odd-pair/block conditional theorem.
No bounded seed census is used for the universal affine clauses. Python -O safe.
Generator uses normalized U/T; acceptance replays the signed physical map.
"""
import json
from functools import lru_cache

WORD='UUUTUUT'
H=(0,0,0,1,0,0,1)
D=(0,0,1,-1,0,1,-1)
CYCLE=(0,0,0,1,1,2,2)
DIRECT=(5,13,21,27,29,37,43,45,53,61,69,77,85,93,101,107,109,117,125)
# r, common alternate slope, ordered alternate offsets, original/alternate clocks
LINKS=(
 (9,16384,1297,1299,7,14),(25,16384,3345,3347,7,14),
 (41,16384,5393,5395,7,14),(55,16384,7443,7441,7,14),
 (57,128,57,55,7,7),(73,16384,9489,9491,7,14),
 (89,16384,11537,11539,7,14),(97,16384,12561,12563,7,14),
 (105,16384,13585,13587,7,14),(119,16384,15635,15633,7,14),
 (121,128,121,119,7,7))
# key=(block lower offset, upper offset, parameter parity).
# Value=(representative offset, steps [(inverse clock, slope, antecedent offset,
# same-block neighbor offset, forward clock)]). All are full affine identities.
BRIDGES={
 (13,15,1):(15,[(14,32768,18229,18233,14),(7,20736,11537,11539,7)]),
 (21,23,0):(23,[(14,32768,3465,3467,14),(14,32768,3419,3417,14),(7,256,25,27,7)]),
 (49,49,0):(49,[(14,32768,6163,6161,14),(14,32768,6155,6153,14)]),
 (49,49,1):(49,[(14,32768,22547,22545,14),(14,32768,22539,22537,14),(7,256,171,171,0)]),
 (77,79,0):(79,[(14,32768,9747,9745,14),(14,32768,9739,9737,14)]),
 (77,79,1):(79,[(14,32768,26633,26635,14),(14,32768,26641,26643,14)]),
 (81,81,0):(81,[(14,32768,10259,10257,14),(14,32768,10251,10249,14),(7,256,77,77,0)]),
 (105,111,0):(105,[(14,32768,13331,13329,14),(7,2304,937,939,7),(7,768,313,309,7)]),
 (113,113,0):(113,[(14,32768,14355,14353,14),(14,32768,14347,14345,14),(7,256,107,107,0)]),
 (125,127,1):(127,[(14,98304,97043,97041,14),(14,32768,32353,32355,14)])}

def require(ok,msg):
    if not ok: raise ValueError(msg)

def normalized(a,b,k,p=2):
    require(a>=0 and b>0,'nonpositive normalized ray')
    for _ in range(k):
        require(a%2==0,'nonuniform parity')
        if WORD[p]=='U':
            a,b=(3*a//2,3*b//2) if b%2==0 else (a//2,(b+1)//2)
        else:
            a,b=(a//2,b//2) if b%2==0 else (3*a//2,(3*b+1)//2)
        p=(p+1)%7
        require(b>0,'normalization escaped positive domain')
    return a,b

def physical(a,b,k,p=2):
    """Independent signed physical recurrence, not the U/T implementation."""
    b=b-1+H[p]
    require(a>=0 and b>=H[p],'unsafe physical launch')
    for _ in range(k):
        require(a%2==0,'physical parity not uniform')
        if b%2: a,b=3*a//2,(3*b+1)//2+D[p]
        else: a,b=a//2,b//2+D[p]
        p=(p+1)%7
        require(b>=H[p],'physical safety failure')
    return a,b+1-H[p]

def replay(a,b,k):
    x=physical(a,b,k)
    require(x==normalized(a,b,k),'physical/normalized disagreement')
    return x

@lru_cache(None)
def inverse(a,b,k):
    Q={(a,b)}
    for j in range(k):
        p=(2-j-1)%7; c=int(WORD[p]=='T'); R=set()
        for A,B in Q:
            R.add((2*A,2*B-(1-c)))
            if A%3==0 and (2*B-c)%3==0 and (2*B-c)//3>0:
                R.add((2*A//3,(2*B-c)//3))
        Q=R
    return tuple(sorted((A,B) for A,B in Q if A%2==0 and B>0 and B%2==1))

def odd_connected(known,A,B,E):
    require(A>0 and A%128==0 and B>0 and E>0 and B%2==E%2==1,'invalid odd chain')
    return all(r%128 in known for r in range(min(B,E),max(B,E),2))

def literal_capture(z,cap=20000):
    n,p=z-1,2
    for k in range(cap+1):
        if n==CYCLE[p]:return k
        n=(3*n+1)//2+D[p] if n%2 else n//2+D[p]
        p=(p+1)%7
        require(n>=H[p],'literal safety failure')
    raise ValueError('finite boundary replay failed')

def find_descent(lo,hi,q,depth):
    M=1<<(depth+1); bound=128*q+lo
    for L in range(7,depth+1,7):
        for s in range(lo,hi+1,2):
            a,b=normalized(M,128*q+s,L)
            for K in range(0,L+1,7):
                for A,B in inverse(a,b,K):
                    # Strict inequality for v>=1; check v=0 separately if needed.
                    if A<=M and B<bound+M-A:
                        return s,L,K,A,B
    return None

def check_descent(lo,hi,q,depth,row):
    require(row is not None,'uncovered block ray')
    s,L,K,A,B=row; M=1<<(depth+1); bound=128*q+lo
    require(lo<=s<=hi and s%2==1 and L%7==K%7==0,'bad representative/clocks')
    require(A>0 and A%2==0 and B>0 and B%2==1,'bad smaller odd partner')
    require(replay(M,128*q+s,L)==replay(A,B,K),'false common future')
    require(A<=M and B<bound+M-A,'not below original block rank')
    if B>=bound:
        literal_capture(128*q+s)
        return 1
    return 0

def check_bridge(known,key,value):
    lo,hi,p=key; s,steps=value; bound=128*p+lo
    require(lo<=s<=hi and s%2==1,'bad bridge representative')
    current=replay(256,128*p+s,7)
    for L,A,B,E,K in steps:
        require(L%7==K%7==0,'phase mismatch')
        require(replay(A,B,L)==current,'bad incoming bridge')
        require(odd_connected(known,A,B,E),'bridge crosses unknown boundary')
        current=replay(A,E,K)
    A,B=current
    require(A>0 and A%2==0 and B>0 and B%2==1,'bridge did not end odd')
    require(A<=256 and B<bound,'bridge not below original block rank')
    return current

def classify_d2():
    loops=[];mergers=[];singletons=[]
    for r in range(1,129):
        a,b=replay(128,r,7); c,d=replay(128,r+2,7)
        for gap in (-2,0,2):
            if a==c and d-b==gap:
                (mergers if gap==0 else loops).append((r,a,b,gap))
            elif a!=c and (gap-d+b)%(c-a)==0 and (gap-d+b)//(c-a)>=0:
                singletons.append((128*((gap-d+b)//(c-a))+r,gap))
    require(loops==[(36,243,72,2),(56,81,36,2),(98,81,63,2),(111,81,72,2)],'loop partition changed')
    require(len(mergers)==21 and singletons==[(7,2)],'merge/singleton partition changed')
    require([r for r,*_ in mergers if r%2]==list(DIRECT),'odd merge bank mismatch')
    for r,a,b,_ in loops:
        require(a%9==b%9==0,'loop loses divisibility by nine')
        if r==36:require(a<=256 and b<=2*r,'F factor bound')
        else:require(3*a<=256 and 3*b<=2*r,'K factor bound')
    require(replay(16384,1569,14)==(729,72) and replay(16384,1571,14)==(729,74),'bad nonloop bridge')
    return loops,mergers,singletons

def root_screen():
    # The exact final relation is P(n) iff P(27n-22). Every accepted
    # recursive row strictly decreases its original n; no claim on others.
    M=16384; merge=[]; reduce=[]; one=[]; union=set()
    for r in range(1,129):
        a,b=replay(128,r,7);c,d=replay(27*128,27*r-22,7)
        if c==27*a and d==27*b-22 and a<=128 and b<r:one.append((r,a,b))
    require(one==[(120,27,26)],'one-lap root return changed')
    for r in range(1,M+1):
        x=replay(M,r,14); y=replay(27*M,27*r-22,14)
        a,b=x;c,d=y
        if x==y:merge.append(r);union.add(r)
        elif c==27*a and d==27*b-22 and a<=M and b<r:
            reduce.append((r,a,b,False));union.add(r)
        elif a==27*c and b==27*d-22 and c<=M and d<r:
            reduce.append((r,c,d,True));union.add(r)
        if r%128==120:union.add(r)
    require(len(merge)==206 and len(reduce)==38,'root screen count changed')
    return {'one_lap_recursive':one,'two_lap_merge':len(merge),'two_lap_recursive':len(reduce),'union_residues_mod_16384':len(union),'remaining_residues_mod_16384':M-len(union)}

def main():
    loops,mergers,singletons=classify_d2()
    known={17}
    for r in DIRECT:
        require(replay(128,r,7)==replay(128,r+2,7),'direct merger failed');known.add(r)
    for r,A,B,E,L,K in LINKS:
        require(r not in known and L%7==K%7==0,'bad conditional link metadata')
        require(odd_connected(known,A,B,E),'unproved dependency')
        require(replay(128,r,L)==replay(A,B,K) and replay(128,r+2,L)==replay(A,E,K),'bad conditional link')
        known.add(r)
    require(len(known)==31,'known bank must have 31 residues')
    # Root17 exactly corresponds to the pair (v+1,27v+5) after a lap.
    require(replay(128,17,7)==(27,5) and replay(128,19,7)==(1,1),'root equivalence failed')
    # Every positive phase-two z has an odd antecedent 128z-109.
    require(replay(128,19,7)==(1,1),'odd entrance failed')
    require(literal_capture(1)==0,'target cycle base failure')
    unknown=sorted(set(range(1,128,2))-known)
    blocks=[(r+2,s) for r,s in zip(unknown,unknown[1:]+[unknown[0]+128])]
    require(unknown[0]==1 and [s for lo,hi in blocks for s in range(lo,hi+1,2)]==list(range(3,130,2)),'incomplete block partition')
    for lo,hi in blocks:require(odd_connected(known,128,lo,hi),'block crosses unknown link')
    coarse=split=deep=finite=0; checked_bridges={};ray_records=[]
    for lo,hi in blocks:
        for p in (0,1):
            key=lo,hi,p
            if key in BRIDGES:
                checked_bridges[str(key)]=check_bridge(known,key,BRIDGES[key]);continue
            row=find_descent(lo,hi,p,7)
            if row is not None:
                finite+=check_descent(lo,hi,p,7,row);coarse+=1;ray_records.append([lo,hi,p,7,*row]);continue
            split+=1
            for q in range(p,256,2):
                row=find_descent(lo,hi,q,14)
                finite+=check_descent(lo,hi,q,14,row);deep+=1;ray_records.append([lo,hi,q,14,*row])
    require(len(checked_bridges)==len(BRIDGES)==10 and coarse+split+len(checked_bridges)==2*len(blocks),'partition incomplete')
    require(deep==128*split,'fine partition incomplete')
    # Adversarial controls: known-link violation; wrong bridge endpoint/clock;
    # wrong original-rank comparison. Explicit exceptions survive -O.
    bad=[lambda: check_bridge(known,(125,127,1),(127,[(14,98304,97043,97045,14)])),
         lambda: check_bridge(known,(125,127,1),(127,[(7,98304,97043,97041,14)])),
         lambda: check_descent(3,3,0,7,(3,0,0,256,3))]
    for f in bad:
        try:f()
        except ValueError:continue
        raise ValueError('corrupt certificate accepted')
    out={'status':'PASS','scope':'conditional whole-ray theorem, not all-seed capture','root_obligation':'forall n>=1, P(n) iff P(27*n-22), phase 2',
         'd2_loops':loops,'d2_full_mergers':len(mergers),'d2_singletons':singletons,
         'direct_odd_links':len(DIRECT),'conditional_extra_links':len(LINKS),'known_odd_residues':sorted(known),
         'block_types':len(blocks),'block_parity_types':2*len(blocks),'coarse_parity_types':coarse,'split_parity_types':split,'fine_affine_rays':deep,
         'whole_parity_bridges':checked_bridges,'finite_boundary_replays':finite,'negative_controls':len(bad),
         'root_screen':root_screen(),'all_seed_capture_proved':False}
    print(json.dumps(out,sort_keys=True,indent=2))
    return out
if __name__=='__main__':main()
