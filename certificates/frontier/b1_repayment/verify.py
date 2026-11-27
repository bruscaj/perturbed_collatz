#!/usr/bin/env python3
"""Signed-physical and exact-arithmetic checks of unbounded B1 repayment.

The arbitrary-h statement follows from the finite primitive identities,
induction and CRT argument in THEOREM.md, with separate Lean proof evidence.
The affine constructor instances below check implementation, not a bound on h.
"""
from __future__ import annotations
import argparse
from copy import deepcopy
import hashlib
import json
from math import gcd
from pathlib import Path

HERE=Path(__file__).resolve().parent
D=(0,0,1,-1,0,1,-1)
H=(0,0,0,1,0,0,1)
W={1:4,2:7,3:4,5:5}


def require(ok,message):
    if not ok:raise ValueError(message)


def exact_json_types(value,path=()):
    """Reject Python's bool/int and float/int equality coercions at input."""
    boolean_paths={('global_capture_proved',),('whole_B1_capture_proved',)}
    if path in boolean_paths:
        require(type(value) is bool,'scope flag must be a JSON boolean')
    elif type(value) is dict:
        for key,child in value.items():
            require(type(key) is str,'JSON object key must be a string')
            exact_json_types(child,path+(key,))
    elif type(value) is list:
        for index,child in enumerate(value):exact_json_types(child,path+(index,))
    else:
        require(type(value) in (int,str),'noninteger numeric field or misplaced boolean/null')


def physical_z(pair,phase,steps):
    """Whole affine progression z=a*v+b for every integer v>=0."""
    a,b=pair;b=b-1+H[phase]
    trace=[]
    for tick in range(steps+1):
        require(a>=0 and b>=H[phase],'unsafe affine state')
        trace.append([a,b+1-H[phase],phase])
        if tick==steps:break
        require(a%2==0,'missing parity split for whole affine progression')
        if b%2:a,b=3*a//2,(3*b+1)//2+D[phase]
        else:a,b=a//2,b//2+D[phase]
        phase=(phase+1)%7
    return trace[-1],trace


def validate_certificate(c):
    require(type(c) is dict,'certificate must be a JSON object')
    exact_json_types(c)
    require(c['schema']==1 and c['word']=='UUUTUUT','wrong model')
    require(c['physical_impulses']==list(D) and c['safe_shifts']==list(H),'wrong signed physical convention')
    require(c['rank_weights']=={str(p):v for p,v in W.items()},'wrong original W rank')
    require(c['source_parent']=='eac53ea4746ca4f02571bf9d6da1b4c6ce42ca25','wrong source pin')
    require(c['global_capture_proved'] is False and c['whole_B1_capture_proved'] is False,'overstated scope')
    grow=c['growing_B1_lap']
    require(grow['parameter_t']==[128,17] and grow['source_z']==[768,102]
            and grow['phase']==1 and grow['steps']==7,'wrong B1 growing domain')
    require(grow['target_t']==[729,98] and grow['target_z']==[4374,588]
            and grow['target_phase']==1,'wrong B1 growing endpoint')
    end,trace=physical_z(grow['source_z'],1,7)
    require(end==grow['target_z']+[1],'false growing endpoint')
    require(grow['counter_coefficient']==601 and grow['counter_offset']==151
            and grow['counter_multiplier']==[729,128],'wrong growing counter')
    require([128*601*729,128*(601*98+151)]==[729*601*128,729*(601*17+151)],'counter transport fails')
    require((-151*pow(601,-1,128))%128==17,'counter guard differs')
    visits=[];gains=[]
    for tick,(a,b,p) in enumerate(trace):
        if p in W:
            require(a%3==0,'unaccounted ternary section split')
            if b%3==0:
                visits.append([tick,p,a//3,b//3])
                if tick:
                    g=[W[p]*a//3-1024,W[p]*b//3-136]
                    require(g[0]>=0 and g[1]>0,'growing lap has a strict W descent')
                    gains.append(g)
    require(visits==grow['section_visits'] and gains==grow['original_W_gains'],'growing section visits or rank gains differ')
    shadow=c['inherited_shadow_merger']
    require(shadow['source_t']==[2**24,1] and shadow['alternate_t']==[1179648,1]
            and shadow['source_z']==[6*2**24,6] and shadow['alternate_z']==[7077888,6], 'wrong shadow launch')
    require(shadow['source_phase']==shadow['alternate_phase']==1
            and shadow['source_steps']==25 and shadow['alternate_steps']==18,'wrong shadow clocks')
    for side in ['source','alternate']:
        e,_=physical_z(shadow[side+'_z'],shadow[side+'_phase'],shadow[side+'_steps'])
        require(e==shadow['common_z']+[shadow['common_phase']],'false shadow common future')
    require(shadow['common_z']==[177147,3] and shadow['common_phase']==5
            and shadow['parameter_map']=='S(a)=(9*a+119)/128'
            and shadow['strict_rank_gap_for_v_positive']==[8*(2**24-1179648),0], 'wrong shadow parameter map/rank')
    require(128*1179648==9*2**24 and 128==9+119,'shadow affine map algebra fails')
    bridge=c['eighteen_step_bridge']
    require(bridge==dict(source_t=[131072,1],source_z=[786432,6],source_phase=1,steps=18,target_z=[19683,3],target_phase=5),'wrong eighteen-step bridge domain')
    require(physical_z(bridge['source_z'],1,18)[0]==bridge['target_z']+[5],'false eighteen-step bridge')
    contract=c['contracting_phase_five_lap']
    require(contract==dict(source_z=[128,3],source_phase=5,steps=7,target_z=[9,3],target_phase=5,counter='z-3',counter_multiplier=[9,128]),'wrong contracting lap domain')
    require(physical_z(contract['source_z'],5,7)[0]==contract['target_z']+[5],'false contracting lap')
    expected=dict(h_minimum=1,v_minimum=0,M='729^h',r0='least positive residue of -752*(601*2^(7*h+17))^(-1) modulo M',r='r0+M*v',T='1+2^(7*h+17)*r',q='(601*T+151)/M',t='(128^h*q-151)/601',U='1+2^17*9^h*r',source_t_mod128=17,source_counter_valuation='7*h+4',source_free_parameter_stride='2^(14*h+17)',alternate_free_parameter_stride='2^17*6561^h')
    require(c['all_parameter_construction']==expected,'changed all-parameter construction/guard')
    sh=c['unbounded_shadow_history']
    require(sh['source_t']=='1+2^(7*h+17)*r' and sh['alternate_t']=='1+9^h*2^17*r'
            and sh['source_clock']=='18+7*h' and sh['alternate_clock']==18
            and sh['intermediate_shadow_parameter']=='v_j=9^j*2^(7*(h-j-1))*r, 0<=j<h',
            'changed unequal-clock composition or intermediate guard')
    out=c['unbounded_repayment']
    require(out==dict(source_section='(2*t,1)',alternate_section='(2*U,1)',source_clock='14*h+18',alternate_clock=18,common_z='3^(2*h+9)*r+3',common_phase=5,direct_target_section_m='3^(2*h+8)*r+1',strict_parameter_drop='U<t',original_W_merger_gap='8*(t-U)',strict_direct_target_rank='5*(3^(2*h+8)*r+1)<8*U<8*t',scope='A proper unbounded subfamily of B1 parameters t=17 mod128; no whole arithmetic progression capture.'),'changed repayment conclusion, strictness or clocks')
    require(c['strict_drop_identity']=='601*729^h*(t-U)=601*2^17*r*(16384^h-6561^h)-752*(729^h-128^h)','changed strict-drop identity')
    # The power inequalities used in the written induction hold from these
    # base comparisons. This verifies their integer constants and units.
    require(gcd(601,729)==gcd(2,729)==1 and 752%3!=0,'CRT unit/nonzero residue check fails')
    require(729%601==128 and 601>151 and 752==601+151,'counter integrality constants fail')
    require(752//16==47 and 752%16==0 and 47%2==1 and 7+17>=5,'exact binary valuation constant fails')
    require(16384>2*6561 and 6561>729>128 and 601*2**17>752,'uniform strict-drop constants fail')
    require(5*3**8<8*2**17 and 5<8,'direct endpoint rank comparison fails')
    return dict(whole_affine_physical_primitives=5,growing_lap_multiplier='729/128',growing_counter='601*t+151',contracting_lap_multiplier='9/128',original_W_growing_gains=gains,unequal_clock_shadow_identity=[25,18],unbounded_total_clocks=['14*h+18',18],direct_forward_endpoint='(3^(2*h+9)*r+3,phase5)')


def v2(a):
    require(a>0,'valuation requires a positive integer')
    return (a&-a).bit_length()-1


def construct(h,v=0):
    require(type(h) is int and h>=1 and type(v) is int and v>=0,'construction requires h>=1,v>=0')
    M=729**h
    r0=-752*pow(601*2**(7*h+17),-1,M)%M
    require(0<r0<M,'least CRT residue is not positive')
    r=r0+M*v
    T=1+2**(7*h+17)*r
    C=601*T+151
    require(C%M==0,'missing ternary divisibility guard')
    q=C//M
    require((128**h*q-151)%601==0,'initial B1 parameter is not integral')
    t=(128**h*q-151)//601
    U=1+2**17*9**h*r
    require(t>=17 and t%128==17 and v2(601*t+151)==7*h+4,'source positivity/residue/valuation differs')
    require(M*v+1<=r<=M*(v+1)-1,'CRT representative bounds fail')
    require(17+2**(14*h+17)*v<=t<2**(14*h+17)*(v+1),'original B1 parameter bounds fail')
    require(1+2**17*9**h+2**17*6561**h*v<=U<=1+2**17*6561**h*(v+1)-2**17*9**h,'alternate B1 parameter bounds fail')
    require(128**h*q==601*t+151 and 729**h*q==601*T+151,'growing history counter equation differs')
    require(601*M*(t-U)==601*2**17*r*(16384**h-6561**h)-752*(M-128**h),'strict-drop algebra differs')
    require(U<t and 5*(3**(2*h+8)*r+1)<8*U<8*t,'strict original-rank drop fails')
    return dict(h=h,v=v,M=M,r0=r0,r=r,T=T,q=q,t=t,U=U)


def construction_checks():
    examples=[]
    for h in [1,2,3,5,8]:
        a=construct(h)
        # Entire v-progression, not three numerical points at a fixed h.
        at=2**(14*h+17);au=2**17*6561**h
        src=[6*at,6*a['t']];alt=[6*au,6*a['U']]
        expected=[3**(8*h+9),3**(2*h+9)*a['r0']+3,5]
        require(physical_z(src,1,14*h+18)[0]==expected,'constructor whole-affine source replay fails')
        require(physical_z(alt,1,18)[0]==expected,'constructor whole-affine alternate replay fails')
        b=construct(h,1)
        require(b['t']-a['t']==at and b['U']-a['U']==au,'free-parameter stride differs')
        for j in range(h):
            stage=1+9**j*2**(7*(h-j)+17)*a['r']
            parameter=9**j*2**(7*(h-j-1))*a['r']
            require(stage==1+2**24*parameter and parameter>=1,'an intermediate shadow guard fails')
        examples.append({k:str(a[k]) for k in ['h','r0','T','q','t','U']} | dict(source_clock=14*h+18,alternate_clock=18,whole_affine_free_parameter_checked=True))
    failures=[]
    for name,fn in [('h zero',lambda:construct(0)),('negative free parameter',lambda:construct(1,-1)),('boolean depth',lambda:construct(True))]:
        try:fn()
        except ValueError:failures.append(name)
        else:raise ValueError('invalid constructor guard accepted')
    require((752+601*2**24*521)%729!=0,'wrong-residue negative fixture accidentally valid')
    failures.append('h=1,r=521 fails required ternary divisibility')
    return dict(constructor_examples=examples,constructor_example_scope='These fixed-h whole-affine examples check the implementation; arbitrary h is justified by finite primitive induction and the CRT/power argument, not by this list.',invalid_constructor_inputs_rejected=failures)


def hostile_checks(c):
    mutations=[
        ('boolean schema',lambda x:x.__setitem__('schema',True)),
        ('boolean phase',lambda x:x['growing_B1_lap'].__setitem__('phase',True)),
        ('boolean affine coefficient',lambda x:x['inherited_shadow_merger']['source_t'].__setitem__(1,True)),
        ('floating numeric field',lambda x:x.__setitem__('schema',1.0)),
        ('wrong growing multiplier',lambda x:x['growing_B1_lap']['target_t'].__setitem__(0,243)),
        ('wrong growing offset',lambda x:x['growing_B1_lap'].__setitem__('counter_offset',8413)),
        ('wrong growing phase',lambda x:x['growing_B1_lap'].__setitem__('phase',2)),
        ('wrong source convention',lambda x:x['physical_impulses'].__setitem__(2,0)),
        ('wrong shadow alternate',lambda x:x['inherited_shadow_merger']['alternate_t'].__setitem__(0,1179649)),
        ('wrong shadow clock',lambda x:x['inherited_shadow_merger'].__setitem__('alternate_steps',17)),
        ('wrong bridge endpoint',lambda x:x['eighteen_step_bridge']['target_z'].__setitem__(1,4)),
        ('wrong contracting factor',lambda x:x['contracting_phase_five_lap']['target_z'].__setitem__(0,27)),
        ('missing positive depth',lambda x:x['all_parameter_construction'].__setitem__('h_minimum',0)),
        ('removed CRT guard',lambda x:x['all_parameter_construction'].__setitem__('r0','any positive integer')),
        ('wrong composition clock',lambda x:x['unbounded_shadow_history'].__setitem__('source_clock','25*h')),
        ('wrong total clock',lambda x:x['unbounded_repayment'].__setitem__('source_clock','14*h+17')),
        ('nonstrict rank claim',lambda x:x['unbounded_repayment'].__setitem__('strict_parameter_drop','U<=t')),
        ('wrong direct target phase',lambda x:x['unbounded_repayment'].__setitem__('common_phase',3)),
        ('global capture overclaim',lambda x:x.__setitem__('global_capture_proved',True)),
    ]
    rejected=[]
    for name,change in mutations:
        bad=deepcopy(c);change(bad)
        try:validate_certificate(bad)
        except (ValueError,KeyError,TypeError):rejected.append(name)
        else:raise ValueError('corrupt certificate accepted: '+name)
    return rejected


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--certificate',type=Path,default=HERE/'certificate.json');p.add_argument('--output',type=Path);args=p.parse_args()
    c=json.loads(args.certificate.read_text())
    primitives=validate_certificate(c);construction=construction_checks();hostile=hostile_checks(c)
    result=dict(status='PASS',source_parent=c['source_parent'],certificate_sha256=hashlib.sha256(args.certificate.read_bytes()).hexdigest(),physical_primitive_review=primitives,all_parameter_constructor_review=construction,rejected_corruption_types=hostile,rejected_corruption_count=len(hostile),disjointness_scope='Every constructed t is 17 mod 128, so it is outside the previously certified odd/even B1 guards explicitly identified in the accompanying formal frontier; this is not a comparison to every repository certificate.',infinite_proof_scope='The finite exact physical identities, growing-counter induction, guarded shadow/contracting induction and CRT plus power inequalities prove the arbitrary-h statement. Lean evidence is separately reported.',global_capture_proved=False,whole_B1_capture_proved=False,whole_t_17_mod128_capture_proved=False)
    if args.output:args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
