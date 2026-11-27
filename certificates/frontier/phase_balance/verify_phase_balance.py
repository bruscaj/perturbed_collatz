"""Exact generation and independent signed-coordinate replay of phase-error paths.
Run: python3 verify_phase_balance.py > certificate.json
No orbit cutoff, floating point arithmetic, or assumptions of capture are used for the path identities.
"""
import json
from collections import defaultdict, deque
from itertools import combinations

H=(0,0,0,1,0,0,1)

def canonical(a,b,p):
    """x=z-1. Remove all powers of two from the affine slope."""
    assert a>0 and 0<=b<a and 0<=p<7
    while a%2==0:
        r=b%2
        if r==H[p]: a,b=a//2,b//2
        else: a,b=3*(a//2),3*(b//2)+1+r
        p=(p+1)%7
    return (a,b,p)

def signed_replay(a,b,p):
    """Independent physical n=x+H[p], ordinary shortcut Collatz plus impulse."""
    if not (a>0 and 0<=b<a and 0<=p<7): raise ValueError('bad source')
    # (A,B) are the physical affine coefficients in n.
    A,B=a,b+H[p]
    while A%2==0:
        q=(p+1)%7
        d=H[q]-H[p]
        if B%2:
            A,B=(3*A)//2,(3*B+1)//2+d
        else:
            A,B=A//2,B//2+d
        p=q
        if B+1-H[p]<1: raise ValueError('unsafe height')
    return (A,B-H[p],p)

def graph(cap,i,j,directed=True,mod=1,res=0):
    g=defaultdict(list)
    a2=1
    while a2<=cap:
        a=a2
        while a<=cap:
            if a%mod==0:
                for b in range(res,a,mod):
                    s=canonical(a,b,i); t=canonical(a,b,j)
                    g[s].append((t,a,b,1))
                    if not directed: g[t].append((s,a,b,-1))
            a*=3
        a2*=2
    return g

def path(g,start,end):
    q=deque([start]); prev={start:None}
    while q:
        s=q.popleft()
        if s==end: break
        for t,a,b,d in g[s]:
            if t not in prev:
                prev[t]=(s,a,b,d);q.append(t)
    if end not in prev: return None
    out=[]; cur=end
    while cur!=start:
        s,a,b,d=prev[cur]
        out.append({'from':s,'to':cur,'a':a,'b':b,'direction':d});cur=s
    return out[::-1]

def replay(rows,start,end,i,j,mod=1,res=0,directed=True,strict_growth=False):
    """Replay selected paths independently; raise rather than assert, including under -O."""
    if not rows: raise ValueError('missing path')
    cur=tuple(start)
    for row in rows:
        a,b,d=row['a'],row['b'],row['direction']
        s=tuple(row['from']);t=tuple(row['to'])
        if a%mod or b%mod!=res or (strict_growth and a<2): raise ValueError('bad argument')
        if d==1: p,q=i,j
        elif d==-1 and not directed: p,q=j,i
        else: raise ValueError('bad orientation')
        if cur!=s or signed_replay(a,b,p)!=s or signed_replay(a,b,q)!=t:
            raise ValueError('path endpoint mismatch')
        cur=t
    if cur!=tuple(end): raise ValueError('bad terminal')
    return len(rows)

def get_balance(i,j):
    start=(1,0,j); end=(1,0,i)
    for cap in (8,16,32,64,128,256,512):
        rows=path(graph(cap,i,j),start,end)
        if rows:
            replay(rows,start,end,i,j,strict_growth=True)
            # Compare each row in normalized and independent signed coordinate.
            for row in rows:
                for p in (i,j):
                    if canonical(row['a'],row['b'],p)!=signed_replay(row['a'],row['b'],p):
                        raise ValueError('cross-replay mismatch')
            return {'phase_pair':[i,j],'cap':cap,'terms_including_x':len(rows)+1,'rows':rows}
    raise ValueError('not found')

def get_transfer(i,j):
    start=(1,0,0);end=(1,0,4)
    rows=path(graph(64,i,j,False),start,end)
    replay(rows,start,end,i,j,directed=False)
    return {'phase_pair':[i,j],'cap':64,'rows':rows}

def get_restricted():
    i,j,mod,res,cap=1,4,32,4,2048
    start=(1,0,0);end=(1,0,4)
    g=graph(cap,i,j,True,mod,res)
    forward=path(g,start,end);back=path(g,end,start)
    replay(forward,start,end,i,j,mod,res);replay(back,end,start,i,j,mod,res)
    return {'phase_pair':[i,j],'modulus':mod,'residue':res,'cap':cap,'forward':forward,'backward':back}

def get_adjacent(i,j,mod=1,res=0,cap_values=(64,128,256,512)):
    # P1(18v+2)=P2(27v+3), P1(18v+3)=P2(9v+2).
    start=(27,2,2);end=(9,1,2)
    for cap in cap_values:
        g=graph(cap,i,j,True,mod,res)
        forward=path(g,start,end);backward=path(g,end,start)
        if forward and backward:
            replay(forward,start,end,i,j,mod,res);replay(backward,end,start,i,j,mod,res)
            return {'phase_pair':[i,j],'modulus':mod,'residue':res,'cap':cap,
                    'forward':forward,'backward':backward}
    raise ValueError('no adjacent transfer')

def tick(z,p):
    n=z-1+H[p];q=(p+1)%7
    n=n//2 if n%2==0 else (3*n+1)//2
    n+=H[q]-H[p]
    return n+1-H[q],q

def bases():
    cycle=(1,1,1,1,2,3,2)
    result=[]
    for p in range(7):
        z,q=1,p
        k=0
        while z!=cycle[q] and k<1000: z,q=tick(z,q);k+=1
        if z!=cycle[q]: raise ValueError('base not captured')
        result.append(k)
    return result

def main():
    balance=[get_balance(i,j) for i,j in combinations(range(7),2)]
    transfer=[get_transfer(i,j) for i,j in combinations(range(7),2)]
    restricted=get_restricted()
    adjacent=[get_adjacent(i,j) for i,j in combinations(range(7),2)]
    restricted_adjacent=get_adjacent(2,6,3,2,(8192,))
    report={'scope':'fixed UUUTUUT only; global capture remains open',
            'H':H,'balance':balance,'transfer':transfer,'restricted':restricted,'adjacent':adjacent,'restricted_adjacent':restricted_adjacent,
            'height_one_capture_clocks':bases(),
            'summary':{'phase_pairs':len(balance),'balance_edges':sum(len(r['rows']) for r in balance),
                       'transfer_edges':sum(len(r['rows']) for r in transfer),
                       'max_balance_slope':max(e['a'] for r in balance for e in r['rows']),
                       'max_transfer_slope':max(e['a'] for r in transfer for e in r['rows']),
                       'max_transfer_length':max(len(r['rows']) for r in transfer),
                       'adjacent_edges':sum(len(r['forward'])+len(r['backward']) for r in adjacent),
                       'max_adjacent_slope':max(e['a'] for r in adjacent for e in r['forward']+r['backward']),
                       'restricted_adjacent_edges':len(restricted_adjacent['forward'])+len(restricted_adjacent['backward']),
                       'restricted_forward_length':len(restricted['forward']),
                       'restricted_backward_length':len(restricted['backward'])}}
    # Check the verifier is sensitive to at least one affine corruption.
    row=balance[0]; bad=[dict(e) for e in row['rows']];bad[0]['b']+=1
    i,j=row['phase_pair']
    try: replay(bad,(1,0,j),(1,0,i),i,j,strict_growth=True)
    except ValueError: report['summary']['corruption_rejected']=True
    else: raise ValueError('corrupt certificate accepted')
    print(json.dumps(report,sort_keys=True,separators=(',',':')))

if __name__=='__main__': main()
