#!/usr/bin/env python3
"""Exact certificate generation/independent verification, no global capture claim."""
from fractions import Fraction
from itertools import combinations
from math import comb
import json
from block_constructor import H,DIMP,Block,block,step,physical,need,shrink_center,inv

Q=(2619,2899,3319,-169,2835,3223,-313)
C=(280,420,630,945,388,582,873)

def v3(n):
    need(n!=0,'zero valuation input')
    j=0
    while n%3==0:n//=3;j+=1
    return j

def inverse_word(L,p,slots):
    N=0;d=1;q=p;slots=set(slots)
    for j in range(L):
        q=(q-1)%7;grow=j in slots
        N=2*N+(H[q] if grow else 1-H[q])*d
        if grow:d*=3
    return N,d,q

def fixed_block_bank():
    obj=Block(2,256,252);spec=obj.verify();need(obj.p==3 and obj.forms[0]==(81,81),'fixed block')
    R=8;P=3**R;cov=bytearray(P);chosen=[]
    for L in range(0,36,7):
        for g in range(min(L,4)+1):
            for slots in combinations(range(L),g):
                N,d,q=inverse_word(L,3,slots);M=81*d
                r=N*pow(2**L,-1,M)%M
                if all(cov[r:P:M]):continue
                for i in range(r,P,M):
                    if not cov[i]:
                        z=i or P;w=z;p=3
                        for j in range(L):w,p=inv(w,p,j in slots)
                        need(p==3 and w>=81 and w%81==0,'inverse block guard')
                cov[r:P:M]=b'\1'*len(cov[r:P:M]);chosen.append((L,g,r,M))
    need(all(cov),'fixed block incomplete')
    return {'block':spec,'modulus':P,'selected_rows':len(chosen),'max_inverse_clock':max(r[0] for r in chosen),'all_phase_entry_clock':max(r[0] for r in chosen)+6+9}

def build_tm_bank(R=9,max_k=29):
    P=3**R
    live={(2,0,0):0};seen=[{} for _ in range(7)];best=[[None]*(P+1) for _ in range(7)]
    snapshots=[]
    for k in range(max_k+1):
        p=(2+k)%7;M=1<<k
        for (a,c,b),r in live.items():
            key=(a,c,b,r==0)
            if key not in seen[p]:seen[p][key]=(k,r)
        for a,c in {(a,c) for a,c,b in live}:
            A=3**a
            for f0 in (False,True):
                e0=seen[p].get((a,c,0,f0))
                if e0 is None:continue
                for f1 in (False,True):
                    e1=seen[p].get((a,c,1,f1))
                    if e1 is None:continue
                    k0,u=e0;k1,v=e1
                    cost=(1<<max(k0,k1))*3**(R-a)
                    floor=c+A*int(f0 or f1);start=c%A or A
                    if start<floor:start+=((floor-start+A-1)//A)*A
                    row=(cost,k0,u,k1,v,a,c)
                    for z in range(start,P+1,A):
                        prev=best[p][z]
                        if prev is None or row<prev:best[p][z]=row
        counts=[sum(x is not None for x in bb[1:]) for bb in best]
        snapshots.append({'clock':k+1,'coverage':counts,'live_types':len(live)})
        if min(counts)==P:break
        old=live;live={}
        for (a,c,b),r in old.items():
            A=3**a
            for d in (0,1):
                x=c+A*d;g=x%2==H[p];aa=a+g
                if aa>R:continue
                y=step(x,p);rr=r+M*d;key=(aa,y,b^d)
                if key not in live or (not live[key] and rr):live[key]=rr
    need(min(counts)==P,'incomplete TM cover')
    return best,snapshots

def verify_tm_bank(best,R=9):
    P=3**R;seen=set();max_cost=0;unequal=0
    for p,rr in enumerate(best):
        for z,row in enumerate(rr[1:],1):
            need(row is not None,'missing target residue')
            cost,k0,r0,k1,r1,a,c=row;A=3**a
            need(a<=R and cost==(1<<max(k0,k1))*3**(R-a),'cost mismatch')
            need(z>=c and (z-c)%A==0,'incorrect target guard')
            v=(z-c)//A;v_floor=int(r0==0 or r1==0)
            need(v>=v_floor,'unsafe source floor')
            need((2+k0)%7==(2+k1)%7==p,'clock-phase mismatch')
            max_cost=max(cost,max_cost)
            if (p,row) in seen:continue
            seen.add((p,row));unequal+=k0!=k1
            need(0<=r0<1<<k0 and 0<=r1<1<<k1,'low digit range')
            need(r0.bit_count()%2==0 and r1.bit_count()%2==1,'digit parity failure')
            for k,r in ((k0,r0),(k1,r1)):
                M=1<<k
                need(A*r<=M*c,'inverse height bound')
                # Whole affine signed physical replay on v=v_floor+w.
                a0=6*M;b0=6*(M*v_floor+r)-1+H[1];q=1
                for _ in range(k+1):
                    need(a0%2==0 and b0>=H[q],'invalid signed guard')
                    m=3 if b0%2 else 1
                    a0,b0=m*a0//2,(m*b0+b0%2)//2+DIMP[q]
                    q=(q+1)%7
                need(q==p and (a0,b0+1-H[q])==(A,A*v_floor+c),'whole-affine endpoint failure')
    return {'target_modulus':P,'phase_residue_classes':7*P,'distinct_selected_pair_rows':len(seen),
            'unequal_clock_rows':unequal,'maximum_entry_clock':max(max(row[1],row[3])+1 for _,row in seen),
            'max_t_over_target_height':str(Fraction(max_cost,P))}

def centered_checks():
    D=2059
    for p in range(7):
        q=(p+1)%7
        need(2*C[q]==3*C[p]-D*H[p],'centered grow identity')
        need(Q[p]==D*(1-H[p])+2*C[q]-C[p],'centered shrink identity')
        need(Q[p]%2==1,'nonodd offset')
    m=[v3(x) for x in Q]
    diff={d:max(v3(2**d*Q[(p+d)%7]-3**d*Q[p]) for p in range(7)) for d in range(1,5)}
    need(max(m)==4 and max(diff.values())==4,'constant gap bound')
    return {'Q':Q,'valuations':m,'max_shifted_difference_valuations':diff,'sufficient_grows_between_shrinks':5}

def sparse_words(n,r,gap=5):
    # a_i=j_i-i: cumulative grow count before the i-th shrink.
    for xs in combinations(range(1,n-gap*r+1),r):
        # choosing y_i strictly increasing, a_i=y_i+(gap-1)(i+1)
        aa=[x+(gap-1)*(i+1) for i,x in enumerate(xs)]
        jj=[a+i for i,a in enumerate(aa)]
        # last j must be <n: xs bound is n-gap*r, so yes.
        need(jj[-1]<n and aa[0]>=gap and all(b-a>=gap for a,b in zip(aa,aa[1:])),'bad sparse word')
        yield tuple(jj)

def sparse_replay(n,r,p=3):
    seen=set();count=0
    for jj in sparse_words(n,r):
        S=set(jj);A=1;c=0;res=0;q=p
        for j in range(n):
            s=H[q] if j not in S else 1-H[q]
            if c%2!=s:res+=1<<j;c+=A
            need(c%2==s,'parity lift')
            m=3 if j not in S else 1
            c=(m*c+s)//2;A*=m;q=(q+1)%7
        z=res+(1<<n);w=z-1+H[p];q=p
        for j in range(n):
            zz=w+1-H[q]
            need((zz%2==H[q])==(j not in S),'literal branch mismatch')
            w=physical(w,q);q=(q+1)%7
        z1=w+1-H[q]
        need(z1==A+c and z1 not in seen,'endpoint collision')
        seen.add(z1);count+=1
    need(count==comb(n-5*r,r),'sparse word census')
    return {'length':n,'shrinks':r,'phase':p,'distinct_endpoints':count}

# Direct phase-three fixed-clock modular steering, independent of the large
# general fixed-modulus adapter. E(z)=128 z-118, anchor a=118/127.
A0=128**2; anchor=Fraction(118,127);lam=Fraction(128,3)
def pump_mod(z,j,m):
    return (pow(A0,j,m)*(127*z-118)+118)*pow(127,-1,m)%m

def pump_exact(z,j):
    N=((127*z-118)<<(14*j))+118;need(N%127==0,'pump integrality');return N//127

def norm_slots():
    table=[];K=[]
    for slot in range(7):
        N,d,q=inverse_word(7,3,(slot,));need(d==3 and q==3,'lap shape')
        k=lam*anchor-Fraction(N,3)-anchor;need(abs(k)<16,'lap offset');K.append(N)
    for r in range(9):
        z=r or 9;chosen=None
        for slot,N in enumerate(K):
            if (128*z-N)%3:continue
            w=(128*z-N)//3
            if (127*w-118)%3:chosen=slot;break
        need(chosen is not None,'no unit normalization');table.append(chosen)
        # A full z=r+9v ray has fixed legality and output mod3.
        N=K[chosen];need((128*z-N)%3==0 and (127*((128*z-N)//3)-118)%3!=0,'normalization guard')
    need(v3(A0-1)==1,'pump LTE base')
    return table,K

def adapter_mod(z,c,a,pad=1):
    # Returns the chosen split exponent and common clock. The endpoint
    # can be represented symbolically when the required pump is enormous.
    table,nums=norm_slots();M=3**a
    N0=nums[table[z%9]];z1=(128*z-N0)//3
    need(z1>0 and (127*z1-118)%3!=0,'normalizer')
    J=next(N for N in nums if (128*z1-N)%3==0)
    T=M-1+pad
    def endpoint_mod(t,m):
        u=pump_mod(z1,t,3*m);n=128*u-J
        need(n%3==0,'illegal slide')
        return pump_mod(n//3,T-t,m)
    t=0;m=1
    for _ in range(a):
        mm=3*m;choices=[t+j*m for j in range(3) if endpoint_mod(t+j*m,mm)==c%mm]
        need(len(choices)==1,'digit lift failed');t=choices[0];m=mm
    need(endpoint_mod(t,M)==c%M,'adapter residue')
    return z1,J,t,T

def adapter_checks():
    table,nums=norm_slots();literal=[]
    # Exact small modulus examples with the entire constructed inverse
    # sequence replayed by the independent signed forward kernel.
    for a in (1,2,3,4):
        M=3**a
        for z in (1,2,3,17,128):
            for c in (0,1,M-1):
                z1,J,t,T=adapter_mod(z,c,a)
                w=pump_exact(z1,t);need((128*w-J)%3==0,'inverse J legality')
                w=(128*w-J)//3;w=pump_exact(w,T-t)
                need(w>0 and w%M==c%M,'adapter output')
                q=3;n=w-1+H[q];L=14*(T+1)
                for _ in range(L):n=physical(n,q);q=(q+1)%7
                need(q==3 and n+1-H[q]==z,'adapter signed replay')
                literal.append({'modulus':M,'target':z,'requested_residue':c,'clock':L,'output_bits':w.bit_length()})
    # Large modulus: digit-lift modular certificate without enormous output.
    large=[]
    for a in (10,25,50,100):
        z1,J,t,T=adapter_mod(123456789,98765,a)
        large.append({'exponent':a,'split_index':t,'clock':14*(T+1),'literal_replay':False})
    return {'one_grow_slot_by_mod9':table,'lap_numerators':nums,'literal_checks':len(literal),'examples':literal,'compressed_modular_checks':large}

if __name__=='__main__':
    blocks=[block(d).verify() for d in (2,3,4,8,16,32,64)]
    best,snapshots=build_tm_bank();tm=verify_tm_bank(best)
    result={'scope':'partial forced-map research; all_seed_capture_proved=false',
            'deterministic_blocks':blocks,'fixed_block_inverse_cover':fixed_block_bank(),
            'tm_cover':tm,'tm_coverage_history':snapshots,'centered_checks':centered_checks(),
            'sparse_replays':[sparse_replay(n,r) for n,r in ((14,1),(28,2),(42,3))],
            'phase3_adapter':adapter_checks()}
    print(json.dumps(result,indent=2))
