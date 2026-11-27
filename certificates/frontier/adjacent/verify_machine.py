#!/usr/bin/env python3
"""Independent signed-physical verifier for the direct adjacent digit machine."""
from pathlib import Path
from collections import Counter, deque
from fractions import Fraction
import json, hashlib, copy
HERE=Path(__file__).resolve().parent
H=(0,0,0,1,0,0,1); D=(0,0,1,-1,0,1,-1); CYCLE=(1,1,1,1,2,3,2)
def need(ok,msg):
    if not ok: raise ValueError(msg)
def signed(a,b,p,k):
    # Affine u=a*w+b, physical n=u+H[p].
    n=b+H[p]
    for _ in range(k):
        need(a%2==0 and n>=H[p],'unsafe/nonuniform ray')
        if n&1: a,n=3*a//2,(3*n+1)//2+D[p]
        else: a,n=a//2,n//2+D[p]
        p=(p+1)%7
        need(n>=H[p],'unsafe output')
    return a,n-H[p],p
def ends(a,b):
    need(type(a) is int and type(b) is int and a>0 and 0<=b<a,'root digits')
    k=(a&-a).bit_length()-1
    need(k%7==0,'phase mismatch')
    return signed(9*a,9*b+1,2,k),signed(27*a,27*b+2,2,k)
def support(path):
    return sorted(x for x,c in Counter((a,b) for a,b,s in path).items() if c&1)
def verify(data):
    need(data['complete'] is True and data['entry_level']==2,'complete entry')
    states=[(3**e,b,2) for e,b in data['states']]
    need(len(set(states))==len(states) and len(states)>0,'distinct states')
    need(all(0<=b<a for a,b,p in states),'state digit bound')
    n=len(states);roots=set();lengths=[]
    def path_check(start,goal,path):
        node=start
        for a,b,s in path:
            need(type(s) is int and s in (-1,1),'edge orientation')
            x,y=ends(a,b)
            if s==-1:x,y=y,x
            need(x==node,'disconnected path');node=y;roots.add((a,b))
        need(node==goal,'wrong endpoint');lengths.append(len(path))
    need(len(data['entry'])==len(data['entry_paths'])==9,'entry coverage')
    for b,(dest,path) in enumerate(zip(data['entry'],data['entry_paths'])):
        need(0<=dest<n,'entry state');path_check((9,b,2),states[dest],path)
    delta=[[-1]*3 for _ in states];supports=[None]*(3*n)
    for t in data['transitions']:
        q,d,j=t['q'],t['d'],t['dest'];need(0<=q<n and 0<=d<3 and 0<=j<n and delta[q][d]==-1,'transition coverage')
        a,b,p=states[q];path_check((3*a,a*d+b,2),states[j],t['path']);delta[q][d]=j;supports[3*q+d]=support(t['path'])
    need(all(x>=0 for row in delta for x in row),'missing transition')
    # All bases captured: literal signed integer replay, not assumed universal capture.
    base=[]
    for a,b,p in states:
        n0=b+H[p]
        for k in range(100000):
            if n0+1-H[p]==CYCLE[p]:break
            n0=(3*n0+1)//2+D[p] if n0&1 else n0//2+D[p];p=(p+1)%7;need(n0>=H[p],'unsafe base')
        else:raise ValueError('unverified base')
        base.append(k)
    # Finite pair automaton; zero once equal. Exact recurrence for number of nonreset words.
    pairs=[(i,j) for i in range(n) for j in range(i+1,n)];idx={p:i for i,p in enumerate(pairs)}
    edges=[[idx.get(tuple(sorted((delta[i][d],delta[j][d]))),-1) for d in range(3)] for i,j in pairs]
    prev=[[] for _ in pairs];dist={};todo=deque()
    for i,row in enumerate(edges):
        if -1 in row:dist[i]=1;todo.append(i)
        for j in row:
            if j>=0:prev[j].append(i)
    while todo:
        j=todo.popleft()
        for i in prev[j]:
            if i not in dist:dist[i]=dist[j]+1;todo.append(i)
    need(len(dist)==len(pairs),'nonmerging pair automaton')
    counts=[1]*len(pairs);maxima=[1];sums=[len(pairs)]
    for k in range(1,7):
        nxt=[sum(counts[j] for j in e if j>=0) for e in edges];maxima.append(max(nxt));sums.append(sum(nxt))
        if k==6:need(nxt==counts,'pair recurrence not fixed')
        counts=nxt
    image=set(range(n))
    for d in (1,0,0,1):image={delta[q][d] for q in image}
    need(len(image)==1,'reset word')
    entry_supports=[support(p)for p in data['entry_paths']]
    S_E=max(sum(a for a,b in s)for s in entry_supports)
    S=max(sum(a for a,b in s)for s in supports)
    S_T=sum(sum(a for a,b in s)for s in supports)
    # sum_j B_{j-1}/3^{j-1} where B_k is maximal nonsync count and B_k=B_5 for k>=5
    tail=sum((Fraction(b,3**k)for k,b in enumerate(maxima[:5])),Fraction())+Fraction(maxima[5],3**5)*Fraction(3,2)
    return {'states':n,'entry_classes':9,'transitions':3*n,'distinct_root_edges':len(roots),'path_edge_occurrences':sum(lengths),'max_path_length':max(lengths),'max_dependency_slope':max(a for a,b in roots),'max_base_capture_clock':max(base),'base_capture_clocks':base,'max_nonsync_counts_through_6':maxima,'pair_count_sums_through_6':sums,'pair_count_vector_fixed_at_5':True,'max_pair_reset_distance':max(dist.values()),'reset_word_lsf':[1,0,0,1],'reset_state':next(iter(image)),'entry_supports_empty':all(not s for s in entry_supports),'entry_max_slope_sum':S_E,'transition_max_slope_sum':S,'all_transition_slope_sum':S_T,'nonsync_sum_bound':str(tail)}
def main():
    p=HERE/'minimax_machine.json'; data=json.loads(p.read_text());r=verify(data);bad=0
    for kind in range(4):
        w=copy.deepcopy(data)
        if kind==0:w['transitions'].pop()
        elif kind==1:
            t=next(x for x in w['transitions'] if x['path']);t['path'][0][1]+=1
        elif kind==2:
            t=next(x for x in w['transitions'] if x['path']);t['path'][0][2]*=-1
        else:w['entry'][0]=(w['entry'][0]+1)%len(w['states'])
        try:verify(w)
        except ValueError:bad+=1
        else:raise ValueError('corrupted certificate accepted')
    print(json.dumps({'status':'PASS',**r,'negative_controls_rejected':bad,'certificate_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'all_seed_capture_proved':False},indent=2,sort_keys=True))
if __name__=='__main__':main()
