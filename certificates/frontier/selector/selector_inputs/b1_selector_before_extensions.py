"""Single constructive B1 cover selector, with explicit unhandled output.

Combines selected finite-state guard languages and TWO explicitly accelerated
counter guards. No claim that the whole unbounded relation is a DFA is made.
All reductions compare original B1 ranks W=8t and supply physical meeting clocks.
"""
from pathlib import Path
import hashlib,json
from full_menu import Menu,D,u_count,require

INPUTS=Path(__file__).with_name('selector_inputs')
IMPULSES=(0,0,1,-1,0,1,-1)
CYCLE=(0,0,0,1,1,2,2)
ELEMENTARY={1:1,2:3,4:1,5:3,6:1,8:3,9:1,11:3,12:1,13:3}


def v2(n):
    require(n>0,'positive valuation input required')
    return (n&-n).bit_length()-1


def physical_run(t,steps):
    n,p=6*t-1,1
    for _ in range(steps):
        n=(n//2 if n%2==0 else (3*n+1)//2)+IMPULSES[p]
        p=(p+1)%7
        require(n>=0,'physical path leaves safe domain')
    return n,p


def reduction(t,s,rule,source_steps,target_steps,**metadata):
    require(type(t) is int and type(s)is int and 0<s<t,'not a strict original B1 rank drop')
    require(source_steps>=0 and target_steps>=0 and (source_steps-target_steps)%7==0,'incorrect meeting clocks')
    return {'status':'reduction','source_t':t,'target_t':s,'proof_rule':rule,
            'source_steps':source_steps,'target_steps':target_steps,
            'meeting_phase':(1+source_steps)%7,
            'original_source_W':8*t,'alternate_W':8*s,'original_W_drop':8*(t-s),
            **metadata}


def pair_witness(menu,c,p,x):
    k=v2(x);q=x>>k;u=u_count(p,k);terminal_phase=(p+k)%7
    residue=pow(3,u,D)*q%D
    L=menu.tables[c][terminal_phase][residue]
    kind='uniform_terminal'
    if not L and u<=5:
        value=3**u*q
        L=menu.singleton[c][terminal_phase].get(value,0)
        kind='exact_terminal_singleton'
    if not L:return None
    return {'ratio':c,'pair_initial_phase':p,'even_prefix_steps':k,
            'terminal_phase':terminal_phase,'terminal_steps':L,
            'pair_steps':k+L,'terminal_kind':kind,
            'terminal_odd_residue_mod16384':residue}


def unbounded_g_h(t):
    """Exact maximal G-run, then ceil(k/4) legal H laps; no cutoff."""
    if t<8:return None
    S=115*t+52;k=v2(S)//7
    if k==0:return None
    q=S>>(7*k)
    numerator=pow(243,k)*q-52
    require(numerator%115==0,'G-conjugacy integrality failed')
    value=numerator//115
    # All earlier exits still satisfy G's4mod128 guard and cannot start H.
    require(value%128!=4,'maximal G-run did not exit')
    ell=(k+3)//4
    suffix_shift=119*value-29
    if v2(suffix_shift)<7*ell:return None
    suffix_numerator=pow(9,ell)*(suffix_shift>>(7*ell))+29
    require(suffix_numerator%119==0,'H-conjugacy integrality failed')
    value=suffix_numerator//119
    return reduction(t,value,'unbounded_G4_H11_repayment',7*(k+ell),0,
                     growing_periods=k,contracting_periods=ell,
                     maximal_growing_run=True,
                     guard_semantics='G=(243t+52)/128 on4mod128; H=(9t+29)/128 on11mod128')


def inherited_shadow_repayment(t):
    """Exact selector for the concurrent Lean B1RepaymentGuard.

    The terminal equation forces v2(601*T+151)=4, hence the only possible
    h is the maximal growing depth with v2(601*t+151)=7*h+4.
    """
    S=601*t+151;k=v2(S)
    if k%7!=4 or k<11:return None
    h=k//7;q=S>>(7*h)
    numerator=pow(729,h)*q-752
    denominator=601*(1<<17)*(1<<(7*h))
    if numerator<=0 or numerator%denominator:return None
    r=numerator//denominator
    target=1+(1<<17)*pow(9,h)*r
    return reduction(t,target,'inherited_growth_shadow_repayment',14*h+18,18,
                     growing_periods=h,shadow_repayments=h,
                     defining_q=q,defining_r=r,
                     provenance='Pinned concurrent working-tree B1RepaymentGuard; commit/merge status not asserted')


class B1Selector:
    def __init__(self,inputs=INPUTS):
        self.menu=Menu()
        self.inputs=Path(inputs)
        self.pins=json.loads((self.inputs/'SOURCE_PINS.json').read_text())
        for name,record in self.pins.items():
            require(hashlib.sha256((self.inputs/name).read_bytes()).hexdigest()==record['sha256'],'selector input pin differs: '+name)
        self.composed=json.loads((self.inputs/'period_composition.json').read_text())
        self.beyond=json.loads((self.inputs/'beyond_screen_candidates.json').read_text())
        self.unbounded=json.loads((self.inputs/'unbounded_excursions.json').read_text())
        self.period_maps={}
        for ray in self.composed['rays']:
            M,r,A,B=(ray[x] for x in('M','r','A','B'))
            require(0<A<=M and 0<B<r<=M,'invalid composed ray')
            self.period_maps.setdefault(M,{})[r]=ray
        self.extra_rays=[]
        for ray in self.beyond['rays']:
            M,r,A,B=(ray[x] for x in('M','r','A','B'))
            require(0<A<M and 0<B<r<=M and len(ray['path'])==4,'invalid28-step ray')
            self.extra_rays.append(ray)
        self.direct_residues={r%128 for r in self.period_maps[128]}
        require(len(self.direct_residues)==28,'direct guard catalogue mismatch')

    def select(self,t):
        require(type(t)is int and t>=1,'positive integer B1 parameter required')
        if t==1:
            return {'status':'capture','source_t':1,'proof_rule':'B1_anchor_capture',
                    'source_steps':18,'cycle_phase':5,'cycle_physical_value':2}
        if t%3==0:
            witness=pair_witness(self.menu,3,2,3*t)
            if witness:
                steps=1+witness['pair_steps']
                return reduction(t,t//3,'full_ratio3_B1_self_merger',steps,steps,pair=witness)
        if t%9==0:
            witness=pair_witness(self.menu,9,2,t)
            if witness:
                steps=1+witness['pair_steps']
                return reduction(t,t//9,'full_ratio9_B1_self_merger',steps,steps,pair=witness)
        if t%243==0:
            return reduction(t,128*(t//243),'known_seven_even_step_pump',0,7)
        if (t-1)%(1<<24)==0:
            v=(t-1)>>24
            return reduction(t,1179648*v+1,'known_cycle_shadow',25,18,shadow_parameter=v)
        for M,lookup in sorted(self.period_maps.items()):
            r=(t-1)%M+1
            ray=lookup.get(r)
            if ray is not None and t>=r:
                v=(t-r)//M;s=ray['A']*v+ray['B']
                return reduction(t,s,'composed_seven_step_self_return',7*len(ray['path']),0,
                                 periods=len(ray['path']),ray_modulus=M,ray_residue=r,path=ray['path'])
        for ray in self.extra_rays:
            M,r=ray['M'],ray['r']
            if t>=r and (t-r)%M==0:
                v=(t-r)//M;s=ray['A']*v+ray['B']
                return reduction(t,s,'four_period_whole_ray',28,0,
                                 periods=4,ray_modulus=M,ray_residue=r,path=ray['path'],
                                 scope='Whole dyadic ray valid; named-screen escape was proved only on the recorded CRT subprogression')
        witness=unbounded_g_h(t)
        if witness:return witness
        witness=inherited_shadow_repayment(t)
        if witness:return witness
        return {'status':'unhandled','source_t':t,
                'reason':'No guard in this explicitly selected combined B1 library applies.',
                'meaning':'Not a noncapture claim.'}

    def old_bank_predicate(self,t):
        """Literal arithmetic reading of the pinned B1SelfCertified definition."""
        require(t>=1,'positive B1 input required')
        k=v2(t);q=t>>k
        elementary=t%3==0 and ELEMENTARY.get(k%14)==q%4
        trip=t%3==0 and k%14==6 and pow(59049,k//14,32)*(q%32)%32==15
        shadow=(t-1)%(1<<24)==0
        direct=t%128 in self.direct_residues
        repayment=inherited_shadow_repayment(t) is not None
        return elementary or trip or shadow or direct or repayment


def replay_witness(witness):
    status=witness['status']
    if status=='unhandled':return False
    if status=='capture':
        actual=physical_run(witness['source_t'],witness['source_steps'])
        require(actual==(witness['cycle_physical_value'],witness['cycle_phase']),'capture witness failed')
        require(CYCLE[actual[1]]==actual[0],'capture endpoint not in distinguished cycle')
        return True
    require(status=='reduction','unknown witness status')
    require(witness['original_W_drop']==8*(witness['source_t']-witness['target_t'])>0,'wrong original rank gap')
    first=physical_run(witness['source_t'],witness['source_steps'])
    second=physical_run(witness['target_t'],witness['target_steps'])
    require(first==second,'physical common-future replay failed: '+witness['proof_rule'])
    require(first[1]==witness['meeting_phase'],'meeting phase metadata failed')
    return True
