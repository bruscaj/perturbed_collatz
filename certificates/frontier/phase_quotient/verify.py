#!/usr/bin/env python3
"""Phase-identification/control certificates for the fixed UUUTUUT system.
No assumption of phase equality or global capture is claimed as proved.
"""
from itertools import combinations
import json
from fractions import Fraction

MAIN=(0,0,0,1,0,0,1)
KNOWN=(1,1,1,1,2,3,2)

def need(ok,msg):
    if not ok: raise ValueError(msg)

def closure(H,i,j,directed=False):
    p=len(H)
    R={(a,a) for a in range(p)}|{(i,j)}
    if not directed:R.add((j,i))
    while True:
        old=set(R)
        for a in range(p):
            for b in range(p):
                if H[a]==H[b]:
                    c,d=(a+1)%p,(b+1)%p
                    if (a,b) in R:R.add((c,d))
                    if (c,d) in R:R.add((a,b))
        R|={(a,d) for a,b in R for c,d in R if b==c}
        if R==old:return R

def quotient(H,i,j):
    R=closure(H,i,j)
    c=tuple(min(b for b in range(len(H)) if (a,b) in R) for a in range(len(H)))
    return c,{q:sorted({(H[p],c[(p+1)%len(H)]) for p in range(len(H)) if c[p]==q}) for q in set(c)}

def normalized(a,b,w):
    for h in w:
        need(a%2==0,'parity not constant')
        s=b%2;m=3 if s==h else 1
        a,b=m*a//2,(m*b+s)//2
    return a,b

def signed(a,b,w):
    # Each letter has arbitrary next H; use the next letter's H,
    # and 0 at the end. This is an independent physical-coordinate replay
    # of the conditional word, not a claim that it is an actual fixed lap.
    for j,h in enumerate(w):
        hnext=w[j+1] if j+1<len(w) else 0
        n=b-1+h; need(n>=h and a%2==0,'invalid signed affine state')
        if n%2:a,n=3*a//2,(3*n+1)//2
        else:a,n=a//2,n//2
        n+=hnext-h;need(n>=hnext,'unsafe')
        b=n+1-hnext
    return a,b

def capture(z,p,H=MAIN,cycle=KNOWN,cap=10000):
    n=z-1+H[p]
    for k in range(cap+1):
        if n+1-H[p]==cycle[p]:return k
        q=(p+1)%len(H);n=((3*n+1)//2 if n%2 else n//2)+H[q]-H[p];p=q
        need(n>=H[p],'unsafe literal state')
    return None

def solve(H,i,j,maxk=15):
    c,adj=quotient(H,i,j);start=c[i]
    if len(set(c))==1:return {'full_phase_collapse':True,'partition':list(c)}
    pending=[((),start)];remain=[1];counts=[];accepted=[];exception=set()
    for k in range(1,maxk+1):
        M=2**k;remain=remain+[r+M//2 for r in remain]
        pending=[(w+(h,),dst) for w,q in pending for h,dst in adj[q]]
        words=[w for w,q in pending if q==start]
        old=len(remain)
        for w in words:
            nxt=[]
            for r in remain:
                a,b=normalized(M,r,w)
                if a<M:
                    v0=max(0,(b-r)//(M-a)+1)
                    accepted.append((M,r,w,a,b,v0))
                    exception.update(r+M*v for v in range(v0))
                else:nxt.append(r)
            remain=nxt
            if not remain:break
        counts.append((k,old,len(remain),len(words)))
        if not remain:break
        if len(remain)>50000 or len(pending)>100000:break
    return {'full_phase_collapse':False,'partition':list(c),'depth':k,'residual':len(remain),'counts':counts,'accepted':accepted,'exceptions':sorted(exception)}

def validate(H,i,j,r,known=None):
    c,adj=quotient(H,i,j);need(list(c)==r['partition'],'partition mismatch')
    if r['full_phase_collapse']:
        need(len(set(c))==1 and set(h for h,_ in adj[c[i]])=={0,1},'bad full collapse')
        return {'full_phase_collapse':True,'classes':1}
    M=2**r['depth'];covered=set();exception=set()
    for a,b,w,aa,bb,v0 in r['accepted']:
        q=c[i]
        for h in w:
            choices=[x for h0,x in adj[q] if h==h0];need(len(choices)==1,'illegal control word');q=choices[0]
        need(q==c[i] and a==2**len(w) and 1<=b<=a and aa<a,'bad source or slope')
        need(signed(a,b,w)==(aa,bb),'physical affine mismatch')
        need(a*v0+b>aa*v0+bb>0,'nondecrease or nonpositive')
        need(v0==0 or a*(v0-1)+b<=aa*(v0-1)+bb,'nonminimal floor')
        for x in range(b,M+1,a):
            need(x not in covered,'overlapping guards');covered.add(x)
        exception.update(b+a*v for v in range(v0))
    need(len(covered)+r['residual']==M,'bad partition count')
    need(sorted(exception)==r['exceptions'],'bad finite exceptions')
    clocks=[]
    if known is not None:
        for z in sorted(exception):
            t=capture(z,i,H,known);need(t is not None,'unverified finite base');clocks.append((z,t))
    return {'full_phase_collapse':False,'classes':len(set(c)),'depth':r['depth'],'residual':r['residual'],'rays':len(r['accepted']),'exceptions':sorted(exception),'base_clocks':clocks,'certificate':[[a,b,''.join('UT'[h] for h in w),aa,bb,v0] for a,b,w,aa,bb,v0 in r['accepted']]}

def step(z,h):return ((3 if z%2==h else 1)*z+z%2)//2

def xor(*bits):return sum(bits)%2

def binary_defect_test():
    # Symbolic algebra of phase differences. Each term is (p,q,composition)
    # on an arbitrary test integer. Formal identities follow by the stated
    # phase/letter transport and XOR; this tests indices, not capture.
    def U(z):return step(z,0)
    def T(z):return step(z,1)
    def S(z):return 2*z-1
    terms=[];checks=0;max_ratio=Fraction(0)
    for z in range(1,513):
        y=(z+1)//2
        w=y if z%2 else z
        a=U(U(w));b=U(w)
        args=[S(S(a)),T(a)]
        if z%2==0:args += [S(S(b)),T(b),S(S(w))]
        need(all(1<=x<=9*z for x in args),'argument bound')
        max_ratio=max(max_ratio,*[Fraction(x,z) for x in args]);checks+=1
    # Nonconstant bounded-height labels satisfy the physical edge identity
    # whenever both endpoints stay below the cap. Test the actual XOR identity
    # against these labels, not against an assumed globally captured basin.
    bounded=[]
    for cap in (4608,10000,100000):
        memo={}
        def label(z,p):
            path=[];seen=set()
            while (z,p) not in memo:
                if z>cap or (z,p) in seen:out=0;break
                if z==KNOWN[p]:out=1;break
                seen.add((z,p));path.append((z,p));z,p=step(z,MAIN[p]),(p+1)%7
            else:out=memo[(z,p)]
            for q in path:memo[q]=out
            return out
        def E(z):return xor(label(z,0),label(z,4))
        nonzero=0
        for z in range(1,513):
            y=(z+1)//2;w=y if z%2 else z;a=U(U(w));b=U(w)
            args=[S(S(a)),T(a)]
            if z%2==0:args += [S(S(b)),T(b),S(S(w))]
            actual=xor(label(z,0),label(y,0));need(actual==xor(*[E(x) for x in args]),'phase defect identity')
            nonzero+=actual
        bounded.append({'height_cap':cap,'identities':512,'nonzero_parent_defects':nonzero})
    need(any(row['nonzero_parent_defects'] for row in bounded),'vacuous finite label fixtures')
    # Verify phase-0 inverse loops: all-shrink and one-grow per ternary class.
    lap=[]
    for r in range(1,129):
        a,b=normalized(128,r,MAIN)
        if a in (1,3):
            need(signed(128,r,MAIN)==(a,b),'inverse lap mismatch');lap.append((r,a,b))
    need({b for r,a,b in lap if a==3}=={1,2,3},'missing one-grow output')
    need(len([r for r,a,b in lap if a==1])==1,'all-shrink branch count')
    R=closure(MAIN,4,0,directed=True)
    order=(3,6,2,5,1,4,0)
    need(R=={(a,b) for i,a in enumerate(order) for b in order[i:]},'directed order mismatch')
    # At phase3 T, for odd z>=5 the next free choice at phase4 is a shrink;
    # 4 residue guards guarantee strict contraction.
    for r in range(1,5):
        z0=r; a,b=normalized(4,r,(1,))
        if r%2:
            h=1-(b%2);aa,bb=normalized(a,b,(h,))
        else:aa,bb=a,b
        need(aa<4,'directed control slope')
        need(aa+bb<4+r,'directed control tail')
    need(all(capture(z,3) is not None for z in (1,2,3)),'directed bases')
    return {'binary_argument_point_checks':checks,'truncated_label_checks':bounded,'max_sample_argument_ratio':str(max_ratio),'phase0_lap_rows':lap,'directed_order':list(order),'directed_bases':[capture(z,3) for z in (1,2,3)]}

def main():
    report={}
    for i,j in combinations(range(7),2):
        row=validate(MAIN,i,j,solve(MAIN,i,j),KNOWN);need(row.get('residual',0)==0,'main unresolved');report[f'{i},{j}']=row
    controls={}
    for name,H in [('UTT',(0,1,1)),('TUTUTUU',(1,0,1,0,1,0,0)),('TTUUUUU',(1,1,0,0,0,0,0)),('TUTUUUU',(1,0,1,0,0,0,0))]:
        rows=[]
        for i,j in combinations(range(len(H)),2):
            r=validate(H,i,j,solve(H,i,j));rows.append({'pair':[i,j],'residual':r.get('residual',0),'full_phase_collapse':r['full_phase_collapse'],'depth':r.get('depth',0)})
        controls[name]=rows
    # The separate UTT control really has competing cycles. No phase-pair
    # premise is inferred from success of the conditional controller.
    H=(0,1,1);D=tuple(H[(p+1)%3]-H[p] for p in range(3))
    cycles=[[(0,0),(1,1),(2,2)],[(1,0),(3,1),(5,2),(7,0),(12,1),(6,2),(2,0),(2,1),(1,2)]]
    for cyc in cycles:
        for (n,p),(m,q) in zip(cyc,cyc[1:]+cyc[:1]):need(((3*n+1)//2 if n%2 else n//2)+D[p]==m and (p+1)%3==q,'bad UTT control cycle')
    need(not set(cycles[0])&set(cycles[1]),'control cycles intersect')
    print(json.dumps({'status':'PASS','scope':'conditional phase equality and dominance only; no all-seed theorem','main':report,'total_rays':sum(r.get('rays',0) for r in report.values()),'base_checks':sum(len(r.get('base_clocks',[])) for r in report.values()),'max_depth':max(r.get('depth',0) for r in report.values()),'binary_parent':binary_defect_test(),'controls':controls},indent=2,sort_keys=True))
if __name__=='__main__':main()
