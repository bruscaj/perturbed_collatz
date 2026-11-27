#!/usr/bin/env python3
"""Exact arithmetic checks for inverse mantissa steering. Standard library only.
Unbounded density/rotation and regular-language arguments are in README.md.
"""
from fractions import Fraction as Q
from itertools import combinations
import json

H=(0,0,0,1,0,0,1)
IMP=(0,0,1,-1,0,1,-1)
A=Q(91,127)
L=Q(128,3)
K=Q(2**28,162)

def need(ok,msg):
    if not ok: raise ValueError(msg)

def affine(p,k,slots):
    """Reverse word: output (2**k*z-N)/d, d=3**len(slots)."""
    N,d=0,1
    for i in range(k):
        h=H[(p-i-1)%7]
        grow=i in slots
        N=2*N+(h if grow else 1-h)*d
        if grow:d*=3
    return N,d

def reverse(z,p,k,slots):
    for i in range(k):
        p=(p-1)%7;h=H[p];grow=i in slots
        numerator=2*z-(h if grow else 1-h)
        z,r=divmod(numerator,3 if grow else 1)
        need(r==0 and z>0,'illegal inverse')
    return z,p

def forward_ray(a,b,p,k):
    """Independent literal physical signed recurrence on entire z=a*v+b ray."""
    g=0;n=b-1+H[p]
    for _ in range(k):
        need(a>0 and a%2==0 and n>=H[p],'nonuniform or unsafe source')
        if n%2:a,n=3*a//2,(3*n+1)//2+IMP[p];g+=1
        else:a,n=a//2,n//2+IMP[p]
        p=(p+1)%7
        need(n>=H[p],'unsafe output')
    return a,n+1-H[p],p,g

def forward(z,p,k):
    n=z-1+H[p];g=0
    for _ in range(k):
        if n%2:n=(3*n+1)//2+IMP[p];g+=1
        else:n=n//2+IMP[p]
        p=(p+1)%7
        need(n>=H[p],'unsafe point')
    return n+1-H[p],p,g

def connectors():
    need(affine(1,7,())==(91,1),'shrink anchor')
    # Choose the first legal one-grow slot separately on each ternary class.
    single={};bounds=[]
    for i in range(7):
        N,d=affine(1,7,(i,));need(d==3,'wrong grow count')
        r=N*pow(128,-1,3)%3
        single.setdefault(r,(i,))
        bounds.append(abs((L-1)*A-Q(N,3)))
    need(set(single)==set(range(3)) and max(bounds)<30,'single-lap coverage or bound')
    for r,slots in single.items():
        z0=r or 3;N,d=affine(1,7,slots);b,rem=divmod(128*z0-N,d)
        need(rem==0 and b>0,'invalid one-grow ray')
        need(forward_ray(128,b,1,7)==(3,z0,1,1),'one-grow whole-ray replay')
    # Also verify a universal two-grow seven-step lap, useful for later optimization.
    double={}
    for slots in combinations(range(7),2):
        N,d=affine(1,7,slots);r=N*pow(128,-1,9)%9
        double.setdefault(r,slots)
    need(len(double)==9,'two-grow coverage')
    for r,slots in double.items():
        z0=r or 9;N,d=affine(1,7,slots);b,rem=divmod(128*z0-N,d)
        need(rem==0 and b>0 and forward_ray(128,b,1,7)==(9,z0,1,2),'two-grow whole-ray replay')
    # End on a grow at phase 1, impose 3|z_out via precision 81.
    # Among the three-grow candidates minimize the nonnegative numerator offset.
    table={}
    for a,b in combinations(range(27),2):
        slots=(a,b,27);N,d=affine(1,28,slots)
        need(d==27,'adapter growth count')
        if N%2:continue
        r=N*pow(2**28,-1,81)%81
        if r not in table or (N,slots)<table[r]:table[r]=(N,slots)
    need(len(table)==81,'adapter does not cover all ternary classes')
    bound=max(abs(A-Q(N,2**28)) for N,slots in table.values())
    need(bound<Q(1,10) and Q(30)/(L-1)+bound<1,'centered error bound')
    for r,(N,slots) in table.items():
        z0=r or 81;B,rem=divmod(2**28*z0-N,27)
        need(rem==0 and B>0 and B%6==0,'not positive B1')
        need(forward_ray(3*2**28,B,1,28)==(81,z0,1,3),'adapter whole-ray physical replay')
        need(reverse(z0,1,28,slots)==(B,1),'adapter inverse point replay')
    return single,double,table,bound

def net(count,stride=1,offset=0):
    """Mantissas of 3^-g modulo 128, with exact largest circular ratio."""
    v=Q(1,3**offset)
    while v<1:v*=128
    a=[]
    for _ in range(count):
        a.append(v);v/=3**stride
        while v<1:v*=128
    a.sort();need(len(set(a))==count,'duplicate mantissas')
    return max([a[i+1]/a[i] for i in range(count-1)]+[128*a[0]/a[-1]])

def ceil_lap(x,J):
    n=max(J,(x.numerator.bit_length()-x.denominator.bit_length()+6)//7)
    while n>J and 128**(n-1)>=x:n-=1
    while 128**n<x:n+=1
    return n

def hit(z,p,X,delta,count,stride,offset,single,table):
    align=(p-1)%7
    z0,q=reverse(z,p,align,())
    need(q==1,'phase alignment')
    C=z0-A
    J=0
    while 128**J*Q(36,127)<16/delta:J+=1
    G=offset+stride*(count-1)
    need(X>=K*C*L**G*128**J,'fixture scale too small')
    Y=X*(1+delta/4);scale=K*C*L**offset
    for g in range(offset,G+1,stride):
        j=ceil_lap(Y/scale,J);ideal=scale*128**j
        if Y<=ideal<=(1+delta/4)*Y:break
        scale*=L**stride
    else:raise ValueError('certified net failed')
    zz=(128**j*C+A)
    need(zz.denominator==1 and zz>0,'shrink formula not positive integer')
    zz=int(zz)
    for _ in range(g):zz,q=reverse(zz,1,7,single[zz%3])
    N,slots=table[zz%81];zz,q=reverse(zz,1,28,slots)
    need(zz%6==0 and q==1,'connector failed')
    t=zz//6;clock=align+7*(j+g)+28
    need(X<t<(1+delta)*X and abs(Q(t)-ideal)<K*L**g,'band or error failure')
    need(forward(6*t,1,clock)==(z,p,g+3),'literal witness replay')
    return {'target':[z,p],'X_bits':X.bit_length(),'g':g,'j':j,'clock':clock,'t_bits':t.bit_length(),'delta':str(delta)}

def residue_graphs():
    results=[]
    for r in range(1,11):
        M=2**r;rows=[set() for _ in range(M)]
        for a in range(128*M):
            z,p,g=forward(a+128*M,1,7)
            need(p==1,'period map phase')
            rows[a%M].add(z%M)
        degree=2**min(r,7)
        need(all(len(row)==degree for row in rows),'wrong dyadic graph degree')
        for graph in (rows,[set() for _ in range(M)]):
            if graph is not rows:
                for a,row in enumerate(rows):
                    for b in row:graph[b].add(a)
            seen={0};pending=[0]
            while pending:
                for b in graph[pending.pop()]:
                    if b not in seen:seen.add(b);pending.append(b)
            need(len(seen)==M,'dyadic graph not strongly connected')
        root=(-420)*pow(2059,-1,128*M)%(128*M)+128*M
        end,p,g=forward(root,1,7)
        need(g==7 and end%M==root%M and 128*end==2187*root+420,'expanding fixed residue')
        results.append({'precision':r,'states':M,'outdegree':degree,'edges':M*degree})
    return results

def control():
    # UTT normalized phase zero. Both cycles have a phase-zero representative.
    H0=(0,1,1);d=(1,0,-1)
    for r in range(3):
        y=r;hits=[]
        for i in range(3):
            h=H0[(-i-1)%3]
            if (2*y-h)%3==0:hits.append(i)
            y=(2*y-(1-h))%3
        need(len(hits)>0,'control one-grow lap unavailable')
    cycles=(((0,0),(1,1),(2,2)),((1,0),(3,1),(5,2),(7,0),(12,1),(6,2),(2,0),(2,1),(1,2)))
    for c in cycles:
        for (n,p),dst in zip(c,c[1:]+c[:1]):
            need(((3*n+1)//2+d[p] if n%2 else n//2+d[p],(p+1)%3)==dst,'bad control cycle')
    need(set(cycles[0]).isdisjoint(cycles[1]),'control cycles overlap')
    return [len(c) for c in cycles]

def main():
    single,double,table,bound=connectors()
    rows=[];examples=[]
    for delta,count,stride,offset in ((Q(1,2),64,1,0),(Q(1,2),64,2,0),(Q(1,2),64,2,1),
                                      (Q(1,10),2048,1,0),(Q(1,10),1024,2,0),(Q(1,10),1024,2,1)):
        gap=net(count,stride,offset)
        need(gap<=1+delta/4,'insufficient rotation net')
        rows.append({'delta':str(delta),'count':count,'stride':stride,'offset':offset,'gap_upper_millionths':(gap.numerator*10**6+gap.denominator-1)//gap.denominator})
        # Choose a scale large enough for the entire certified net, not a guessed float.
        X=2**(6*(offset+stride*(count-1))+80)
        for z,p in ((1,0),(6,1),(17,2),(91,3),(101,4),(1000,5),(2,6)):
            examples.append(hit(z,p,X,delta,count,stride,offset,single,table))
    # Check the eventual excess-grow index of B1(1) on the known cycle.
    z,p,g=forward(6,1,42);z2,p2,g2=forward(z,p,7)
    need((z,p)==(z2,p2) and g2==2 and g-12==2,'base index or cycle mismatch')
    distinct_indices=[]
    for offset in range(0,8*68,68):
        row=hit(6,1,2**(6*(8*68+64)+80),Q(1,2),64,1,offset,single,table)
        row['index']=-3-2*row['j']-row['g']
        distinct_indices.append(row)
    need(len({row['index'] for row in distinct_indices})==8,'index spread fixture')
    print(json.dumps({'status':'PASS' ,'one_grow_lap_classes':len(single),'two_grow_lap_classes':len(double),
        'B1_connector_classes':len(table),'B1_clock':28,'B1_grows':3,'centered_adapter_error_bound':str(bound),
        'adapter_table':{str(r):{'N':N,'slots':slots} for r,(N,slots) in sorted(table.items())},
        'whole_affine_rays':len(single)+len(double)+len(table),'rotation_nets':rows,'point_replays':examples,
        'UTT_control_cycle_lengths':control(),'index_spread_examples':distinct_indices,'dyadic_graphs':residue_graphs(),'all_seed_capture_proved':False},indent=2,sort_keys=True))

if __name__=='__main__':main()
