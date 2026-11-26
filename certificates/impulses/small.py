"""Complete one/two-pair excursion census; Python standard library only."""
if not __debug__:
    raise SystemExit("Run without Python -O: assertions are evidence checks.")
from pathlib import Path
import json
import sys
sys.path.insert(0, str(Path(__file__).resolve().parent / "six_impulses"))
from certify import BASE, outside_endpoints, segment


def words(q, n=1, prefix=()):
    if q == 0:
        yield prefix
    else:
        for pair, endpoint in outside_endpoints(n):
            yield from words(q-1, endpoint, prefix+(pair,))


def replay(word, seed, phase):
    forcing = [d for b,a in word for d in [1]+[0]*b+[-1]+[0]*a]
    p = len(forcing)
    start = sum(2+b+a for b,a in word[:phase])
    values, seen, n = [], {}, seed
    while (n,(start+len(values))%p) not in seen:
        t=len(values); seen[n,(start+t)%p]=t; values.append(n)
        n=(n//2 if n%2==0 else (3*n+1)//2)+forcing[(start+t)%p]
        if n<0 or len(values)>100000:
            raise ArithmeticError("unsafe or unclosed witness")
    mu=seen[n,(start+len(values))%p]; cycle=values[mu:]
    primitive=next(k for k in range(1,p+1) if p%k==0 and forcing==forcing[:k]*(p//k))
    scalar=next(k for k in range(1,len(cycle)+1) if len(cycle)%k==0 and cycle==cycle[:k]*(len(cycle)//k))
    return dict(peak=max(values), supplied_period=p, fundamental_period=primitive,
                cycle_updates=len(cycle), scalar_period=scalar, onset=mu)


def census(q):
    count=0; top=0; ratio=0; peak_w=None; period_w=None
    for word in words(q):
        count+=1
        for phase in range(q):
            for seed in (1, 2, 0):
                n=seed; ph=phase; seen={}; depth=0; peak=n
                while (n,ph) not in seen:
                    seen[n,ph]=depth
                    n,high=segment(word[ph],n); peak=max(peak,high)
                    ph=(ph+1)%q; depth+=1
                    if depth>10000:
                        raise ArithmeticError("unclosed core walk")
                length=depth-seen[n,ph]
                if length%q:
                    raise ArithmeticError("phase mismatch")
                if peak>top:
                    top=peak; peak_w=dict(pairs=word,seed=seed,before_pair=phase)
                if length//q>ratio:
                    ratio=length//q; period_w=dict(pairs=word,seed=seed,before_pair=phase)
    for witness in (peak_w,period_w):
        witness["literal"]=replay(witness["pairs"],witness["seed"],witness["before_pair"])
    assert peak_w["literal"]["peak"]==top
    w=period_w["literal"]
    assert w["cycle_updates"]==ratio*w["supplied_period"]
    assert w["fundamental_period"]==w["supplied_period"]
    assert w["scalar_period"]==w["cycle_updates"]
    return dict(pairs=q,rooted_words=count,peak=top,max_cycle_laps=ratio,peak_witness=peak_w,period_witness=period_w)

if __name__=="__main__":
    data=[census(1),census(2)]
    assert [(x["rooted_words"],x["peak"],x["max_cycle_laps"]) for x in data]==[(15,122,7),(2854,195020,7)]
    print(json.dumps(data,indent=2))
