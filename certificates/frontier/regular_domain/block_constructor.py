#!/usr/bin/env python3
"""Constructive block merging and bounded entry into syndetic regular sets.
No global capture claim. Standard library, exact integer arithmetic.
"""
from fractions import Fraction
import json
import math

H=(0,0,0,1,0,0,1)
DIMP=tuple(H[(p+1)%7]-H[p] for p in range(7))
TERMINALS=(('110','10010','10110','11110','11110'),
 ('0010','1110','0100010','1110','0001110'),
 ('110','110','000110','100010','100110'),
 ('10','00010','11010','01110','0100110'),
 ('0010','1110','100110','1110','110100'),
 ('110','110','11110','10110','0111110'),
 ('10','0110','010110','010010','010110'))

def need(x,msg):
    if not x: raise ValueError(msg)
def vp2(n):
    if not n: return math.inf
    return (abs(n)&-abs(n)).bit_length()-1

def step(z,p):
    s=z%2
    return ((3 if s==H[p] else 1)*z+s)//2

def physical(n,p):
    return ((3*n+1)//2 if n%2 else n//2)+DIMP[p]

def shape(forms,i,j):
    if forms[i]>forms[j]: i,j=j,i
    a,b=forms[i]; A,B=forms[j]
    need(A%a==0,'ratio')
    q=A//a
    e=0
    while q>1 and q%3==0: q//=3;e+=1
    need(q==1,'ratio power')
    return i,j,e,B-3**e*b

def pair_step(e,b,p,s):
    a=3**e;r=(s+b)%2
    m=3 if s==H[p] else 1;n=3 if r==H[p] else 1
    ap=Fraction(n*a,m);bp=Fraction(n*b+r-ap*s,2)
    if ap<1 or (ap==1 and bp<0): ap,bp=1/ap,-bp/ap
    need(ap.denominator==bp.denominator==1,'nonintegral type')
    return ap.numerator,bp.numerator

class Block:
    def __init__(self,width,mod=1,res=1):
        need(mod>0 and mod&(mod-1)==0 and res>=1,'initial domain')
        # Initial even stride: strip its binary precision through literal ticks,
        # retaining the mandatory first B1 update. At end all coefficients odd.
        self.width=width;self.M=mod;self.r=res;self.p=2;self.clock=1
        self.forms=[(9*mod,9*(res+j)) for j in range(width)]
        self.steps=[]
        while self.forms[0][0]%2==0:
            self.tick(None)
    def tick(self,bit):
        if bit is not None:
            self.r+=self.M*bit;self.M*=2
        new=[]
        for a,b in self.forms:
            if bit is not None: a,b=2*a,b+a*bit
            need(a%2==0 and b>0,'nonuniform or unsafe')
            s=b%2;m=3 if s==H[self.p] else 1
            new.append((m*a//2,(m*b+s)//2))
        self.forms=new;self.p=(self.p+1)%7;self.clock+=1
        self.steps.append(bit)
    def choose(self,i,s):
        a,b=self.forms[i];need(a%2==1,'even free slope');self.tick((s-b)%2)
    def merge(self,j):
        # Lexicographic descent on exponent then positive equal-slope gap.
        while self.forms[0]!=self.forms[j]:
            i,k,e,b=shape(self.forms,0,j);p=self.p
            if e>0:
                if b%2: s=H[p]
                else:
                    # Both options stay at same exponent; choose minimal valuation.
                    s=min((0,1),key=lambda s:vp2(pair_step(e,b,p,s)[1]))
                self.choose(i,s)
                continue
            if b<=5:
                for s in TERMINALS[p][b-1]:
                    i,k,e,b=shape(self.forms,0,j)
                    self.choose(i,int(s))
                need(self.forms[0]==self.forms[j],'terminal table failure')
                continue
            if b%2==0:
                self.choose(i,1-H[p]);continue
            # One e=1 excursion, strictly decreases original positive gap.
            old=b;self.choose(i,1-H[p])
            while True:
                i,k,e,b=shape(self.forms,0,j);p=self.p
                need(e==1,'unexpected exponent in gap excursion')
                if b%2:
                    self.choose(i,H[p]);break
                s=1-H[p] if abs(b)>=4 else (1 if b==0 else 0)
                self.choose(i,s)
            i,k,e,b=shape(self.forms,0,j)
            need(e==0 and b<old,'gap descent failed')
    def verify(self):
        # Reconstruct entire original affine ray in signed physical n.
        ends=[]
        for j in range(self.width):
            p=1;a=6*self.M;b=6*(self.r+j)-1+H[p]
            for _ in range(self.clock):
                need(a%2==0 and b>=H[p],'physical guard')
                m=3 if b%2 else 1
                a,b=m*a//2,(m*b+b%2)//2+DIMP[p]
                p=(p+1)%7
            ends.append((a,b+1-H[p]))
        need(ends==self.forms,'physical affine mismatch')
        need(len(set(ends))==1,'block not merged')
        return {'width':self.width,'modulus_bits':self.M.bit_length()-1,'residue':self.r,
          'clock':self.clock,'phase':self.p,'endpoint_coefficient':self.forms[0][0],
          'endpoint_intercept':self.forms[0][1]}

def block(width,align=1,res=1):
    obj=Block(width,align,res)
    for j in range(1,width): obj.merge(j)
    obj.verify();return obj

def inv(z,p,g):
    q=(p-1)%7
    if g:
        num=2*z-H[q]
        if num%3:return None
        u=num//3
    else:u=2*z-(1-H[q])
    need(u>0 and step(u,q)==z,'inverse failure')
    return u,q

def shrink_center(p):
    # Compute all-shrink inverse lap with offset -C, formal argument 0.
    z=0;q=p
    for _ in range(7):
        q=(q-1)%7;z=2*z-(1-H[q])
    return Fraction(-z,127)

def unit_residue(z,p):
    c=shrink_center(p)
    return (c.denominator*z-c.numerator)%3!=0

def normalize(z,p):
    if unit_residue(z,p):return z,0
    for L in (7,14,21,42):
        for slot in range(L):
            w=z;q=p
            for j in range(L):
                ans=inv(w,q,j==slot)
                if ans is None:break
                w,q=ans
            else:
                if unit_residue(w,p):return w,L
    raise ValueError('normalization not found')

def unitize(obj):
    # Common trajectory can choose arbitrary parity on dyadic refinements.
    # Find a grow-output phase whose all-shrink anchor differs mod 3.
    for _ in range(7):
        if unit_residue(obj.forms[0][1],obj.p) and obj.forms[0][0]%3==0:
            return obj
        q=(obj.p+1)%7
        grow_residue=H[obj.p]*2%3  # (3z+h)/2 mod 3 = 2h
        if unit_residue(grow_residue,q):obj.choose(0,H[obj.p])
        else:obj.choose(0,1-H[obj.p])
    raise ValueError('unitize failure')

def entry(obj,target,phase):
    # For small endpoint modulus, elementary unit rotation adapter.
    A,c=obj.forms[0];p=obj.p
    need(A>=3 and unit_residue(c,p),'wrong endpoint guard')
    tmp=A
    while tmp%3==0:tmp//=3
    need(tmp==1,'endpoint coefficient not a power of 3')
    z=target;q=phase;clock=0
    while q!=p:z,q=inv(z,q,False);clock+=1
    z,L=normalize(z,p);clock+=L
    a=shrink_center(p)
    # 128 is primitive modulo every 3^k, by v3(128^2-1)=1.
    period=2*A//3
    inv127=pow(127,-1,A)
    center=(a.numerator*pow(a.denominator,-1,A))%A
    modz=z%A;found=None
    for j in range(period):
        if modz==c%A:found=j;break
        modz=(128*(modz-center)+center)%A
    need(found is not None,'unit orbit missed')
    # Pad by full periods if needed to attain v>=0. For practical tests, the
    # power may be large, but exact integers suffice at these small moduli.
    num=127*z-a.numerator*(127//a.denominator)
    anchor_num=a.numerator*(127//a.denominator)
    j=found
    while True:
        w=((num<< (7*j))+anchor_num)//127
        if w>=c:break
        j+=period
    need((w-c)%A==0,'endpoint not in ray')
    v=(w-c)//A;t=obj.r+obj.M*v
    return t,clock+7*j+obj.clock,found,j,period

def replay(t,clock,target,phase):
    z=6*t;p=1
    n=z-1+H[p]
    for _ in range(clock):n=physical(n,p);p=(p+1)%7
    return n+1-H[p]==target and p==phase

def tm(t):return t.bit_count()%2==0

def run():
    rows=[]
    for w in (2,3,4,8,16,32,64):
        x=block(w);rows.append(x.verify())
    # Every even-aligned pair has opposite digit-sum parity.
    obj=unitize(block(2,2,2));spec=obj.verify()
    samples=[]
    for p in range(7):
        for z in (1,2,3,17,128,1023):
            t,L,j,jpad,period=entry(obj,z,p)
            u=t if tm(t) else t+1
            need(t%2==0 and tm(u),'not accepted')
            need(replay(u,L,z,p),'literal target replay failure')
            samples.append({'target':z,'phase':p,'bits':u.bit_length(),'clock':L,'accepted_offset':u-t})
    return {'scope':'exact constructive synchronization and bounded inverse entry for Thue-Morse even digit sum; not a capture proof',
            'block_constructions':rows,'even_aligned_block':spec,'entry_samples':samples}
if __name__=='__main__':print(json.dumps(run(),indent=2))
