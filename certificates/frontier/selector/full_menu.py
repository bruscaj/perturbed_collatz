"""Exact guard predicates for the pinned PR17 paired/direct terminal menu.

Coordinates are ORIGINAL row parameters, never trajectory parity. The menu is
local reduction coverage; rejection is not noncapture. Terminal singletons are
used only as exact equalities, never as dyadic congruences.
"""
from pathlib import Path
from fractions import Fraction
import hashlib, json

D=1<<14
PERIOD=7*(1<<12)
DEFAULT_CERTIFICATE=Path(__file__).resolve().parent/'inputs/pair_terminal_certificate.json'
CERTIFICATE_SHA256='78593459eea625aebbe64be1c035e42b469e9d6f94e5429fcd81d17e2959b207'


def require(ok, message):
    if not ok:
        raise ValueError(message)


def u_count(p,k):
    return 5*(k//7)+sum((p+j)%7 not in (3,6) for j in range(k%7))


class Menu:
    def __init__(self, certificate=DEFAULT_CERTIFICATE):
        path=Path(certificate)
        data=path.read_bytes()
        self.source_sha256=hashlib.sha256(data).hexdigest()
        require(self.source_sha256==CERTIFICATE_SHA256,'terminal certificate differs from pinned PR17 input')
        self.cert=json.loads(data)
        require(self.cert['word']=='UUUTUUT' and self.cert['horizon']==14,'wrong terminal scope')
        self.tables={c:[bytearray(D) for _ in range(7)] for c in (3,9)}
        self.singleton={c:[{} for _ in range(7)] for c in (3,9)}
        self.rows={}
        for lib in self.cert['libraries']:
            c=lib['ratio'];self.rows[c]=lib['rows']
            require(c in (3,9),'wrong ratio')
            for row in lib['rows']:
                p,M,r,L=row['phase'],row['modulus'],row['residue'],row['steps']
                require(p in range(7) and 2<=M<=D and M&(M-1)==0 and r%2==1 and 0<r<M,'invalid terminal row')
                for residue in range(r,D,M):
                    require(self.tables[c][p][residue]==0,'overlapping terminal rows')
                    self.tables[c][p][residue]=L
            for row in lib['isolated_singleton_collisions']:
                self.singleton[c][row['phase']][row['value']]=row['first_steps']
        self.finite_singleton_inputs=self._singleton_preimages()

    def pair(self,c,p,x,exact=False):
        require(x>0,'positive pair initialization required')
        k=(x&-x).bit_length()-1
        q=x>>k
        phase=(p+k)%7
        u=u_count(p,k)
        ymod=pow(3,u,D)*q%D
        if self.tables[c][phase][ymod]:
            return True
        if exact and self.singleton[c][phase]:
            # All saved exceptions are <=101. Bound u before exponentiating.
            largest=max(self.singleton[c][phase])
            if q<=largest and u<=5:
                return (3**u*q) in self.singleton[c][phase]
        return False

    def b1_ratio3(self,t,exact=True):
        require(t>=1,'B1 parameter t>=1 required')
        return self.pair(3,2,3*t,exact=exact)

    def b1_ratio9(self,t,exact=True):
        require(t>=1,'B1 parameter t>=1 required')
        return t%2==0 and self.pair(9,3,3*t//2,exact=exact)

    def b1_periodic(self,t):
        require(t>=1,'B1 parameter t>=1 required')
        return self.pair(3,2,3*t) or (t%2==0 and self.pair(9,3,3*t//2))

    def b1_exact(self,t):
        require(t>=1,'B1 parameter t>=1 required')
        return self.b1_periodic(t) or t in self.finite_singleton_inputs['B1']

    def row(self,name,t,include_singletons=True,include_pump=False):
        require(name in ('B1','A3','N03'),'unknown row')
        require(t>0 if name=='B1' else t>=0,'invalid row parameter')
        if name=='B1':
            result=self.b1_periodic(t)
            residue=0
        elif name=='A3':
            result=(t%8 in (0,6)) or (t%2==1 and self.pair(9,6,(9*t+7)//2))
            residue=60
        else:
            result=self.pair(3,6,12*t+3) or (t%4==3 and self.pair(9,3,3*(27*t+7)//4))
            residue=182
        if include_singletons:
            result=result or t in self.finite_singleton_inputs[name]
        if include_pump:
            result=result or t%243==residue
        return bool(result)

    def b1_reduced_formula(self,t):
        """Independent algebraic simplification used by the decision DAG."""
        require(t>=1,'B1 parameter t>=1 required')
        k=(t&-t).bit_length()-1
        q=t>>k
        if k==0:
            return bool(self.tables[3][2][3*q%D])
        p=(2+k)%7
        y=pow(3,u_count(2,k),D)*q%D
        return bool(self.tables[9][p][y] or self.tables[3][p][3*y%D])

    def _singleton_preimages(self):
        # k>=7 gives at least five U steps, hence y>=243>101.
        maximum=max(v for c in self.singleton.values() for row in c for v in row)
        require(maximum==101,'singleton horizon maximum changed')
        specs=[('B1',3,2,lambda x:x//3 if x%3==0 else None),
               ('B1',9,3,lambda x:2*(x//3) if x%3==0 else None),
               ('A3',9,6,lambda x:(2*x-7)//9 if (2*x-7)%9==0 else None),
               ('N03',3,6,lambda x:(x-3)//12 if (x-3)%12==0 else None),
               ('N03',9,3,lambda x:(4*x-21)//81 if (4*x-21)%81==0 else None)]
        result={name:set() for name in ('B1','A3','N03')}
        self.singleton_preimage_records=[]
        for name,c,p,inverse in specs:
            require(u_count(p,7)>=5,'singleton k>=7 bound invalid')
            for k in range(7):
                u=u_count(p,k);factor=3**u
                for y,L in self.singleton[c][(p+k)%7].items():
                    if y%factor:
                        continue
                    q=y//factor
                    if q<=0 or q%2==0:
                        continue
                    x=(1<<k)*q
                    t=inverse(x)
                    if t is None or (t<1 if name=='B1' else t<0):
                        continue
                    if name=='A3' and t%2!=1:
                        continue
                    if name=='N03' and c==9 and t%4!=3:
                        continue
                    if name=='N03' and c==3 and (k!=0 or L<2):
                        continue
                    result[name].add(t)
                    self.singleton_preimage_records.append(dict(row=name,ratio=c,start_phase=p,
                        initial_x=x,valuation=k,terminal_y=y,terminal_steps=L,parameter=t))
        return result

    def densities(self,include_pump=False):
        fractions={'B1':Fraction(196283,520192),'A3':Fraction(147687,520192),'N03':Fraction(304285,4161536)}
        return {row:d+(1-d)/243 if include_pump else d for row,d in fractions.items()}


_default_menu=None

def default_menu():
    global _default_menu
    if _default_menu is None:
        _default_menu=Menu()
    return _default_menu


def b1_periodic(t):
    return default_menu().b1_periodic(t)


def b1_exact(t):
    return default_menu().b1_exact(t)


def row_accept(name,t,include_singletons=True,include_pump=True):
    return default_menu().row(name,t,include_singletons,include_pump)


def b1_ratio3(t,exact=True):
    return default_menu().b1_ratio3(t,exact)


def b1_ratio9(t,exact=True):
    return default_menu().b1_ratio9(t,exact)
