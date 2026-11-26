#!/usr/bin/env python3
"""Independent exact witness checker for the six-branch phase-rank lower bound.

This does not import the frontier builder or enumerate a seed interval.
Each witness is checked on its entire positive affine parameter domain.
"""
from fractions import Fraction
from math import gcd
import json
import argparse
from pathlib import Path

WORD='UUUTUUT'
SECTION={3,5,6}

# All parameters are nonnegative except where the explicit minimum is one.
# name, phase, input M,r, output A,b, output phase, trace, parameter minimum
SPECS=[
 ('S00',3,4,3,9,7,5,'AA',0),
 ('S01',5,2,0,3,0,6,'A',1),
 ('S02',5,32,3,81,9,3,'DAAAA',0),
 ('S03',5,128,115,243,220,5,'DAAADAA',0),
 ('S06',6,16,7,81,36,3,'AAAA',0),
 ('S08',6,64,15,243,58,5,'AAADAA',0),
 ('D53',5,32,31,27,27,3,'DADAA',0),
 ('D35',3,4,1,3,1,5,'AD',1),
 ('D36',3,8,2,3,1,6,'DDA',0),
 ('D65',6,8192,6239,6561,4999,5,'AAADDDDAAADAA',0),
 ('D56',5,256,147,81,47,6,'DAAADDDA',0),
]
CYCLES=[
 ['S03'],
 ['S00','D53'],
 ['S02','D35'],
 ['S06','D36'],
 ['S01','D65'],
 ['S08','D56'],
]


def replay(a,b,phase,trace,lo=0,first_section=False):
    """Propagate z=a*q+b using exact fixed-parity guards for every q>=lo."""
    states=[dict(phase=phase,a=a,b=b)]
    for index,branch in enumerate(trace):
        assert a>0 and a*lo+b>0
        assert a%2==0, ('parity is not fixed on the whole domain',index,a)
        is_A=b%2==int(WORD[phase]=='T')
        assert branch==('A' if is_A else 'D')
        multiplier=3 if is_A else 1
        offset=int(WORD[phase]=='T') if is_A else int(WORD[phase]=='U')
        assert (multiplier*b+offset)%2==0
        a,b=multiplier*a//2,(multiplier*b+offset)//2
        phase=(phase+1)%7
        assert a>0 and a*lo+b>0
        states.append(dict(phase=phase,a=a,b=b))
        if first_section and index+1<len(trace):
            assert a%3==0
            assert not (phase in SECTION and b%3==0), ('earlier section visit',index)
    return a,b,phase,states


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if not __debug__: raise RuntimeError('Run without -O: assertions must remain enabled.')
    rows={}
    for name,p,M,r,A,b,q,tr,lo in SPECS:
        a1,b1,q1,states=replay(3*M,3*r,p,tr,lo,True)
        assert (a1,b1,q1)==(3*A,3*b,q)
        assert M*lo+r>0 and A*lo+b>0
        if name.startswith('D'):
            assert M>A and (M-A)*lo+r-b>0
        else:
            assert A>M and (A-M)*lo+b-r>0
        rows[name]=dict(input_phase=p,modulus=M,residue=r,
             output_multiplier=A,output_offset=b,output_phase=q,
             trace=tr,t_min=lo,slope=str(Fraction(A,M)),states=states)
    # The eleven starting domains are pairwise disjoint, even before lower bounds.
    for i,left in enumerate(SPECS):
        for right in SPECS[i+1:]:
            if left[1]==right[1]:
                assert (left[3]-right[3])%gcd(left[2],right[2])!=0, (left[0],right[0])
    cycle_results=[];used=set()
    for cycle in CYCLES:
        product=Fraction(1)
        for index,name in enumerate(cycle):
            assert name not in used;used.add(name)
            current=rows[name];nxt=rows[cycle[(index+1)%len(cycle)]]
            assert current['output_phase']==nxt['input_phase']
            product*=Fraction(current['slope'])
        assert product>1
        cycle_results.append(dict(rows=cycle,slope_product=str(product)))
    assert len(used)==11 and len(cycle_results)==6

    # The selected (1,1,2) weights leave the six S witnesses increasing and
    # preserve all five descending witness tails; D36 only has its known tie.
    weights={3:1,5:1,6:2}
    slacks={}
    for name,row in rows.items():
        a=weights[row['input_phase']]*row['modulus']-weights[row['output_phase']]*row['output_multiplier']
        b=weights[row['input_phase']]*row['residue']-weights[row['output_phase']]*row['output_offset']
        if name.startswith('S'):
            assert a<0
        else:
            assert a>0 and a*row['t_min']+b>=0
            if a*row['t_min']+b==0:
                assert name=='D36' and row['t_min']==0
        slacks[name]=dict(coefficient=a,constant=b)

    # Whole S12 reduction under the new simultaneous section rank.
    a,b,p,states=replay(192,189,6,'AAADDA',0,True)
    assert (a,b,p)==(243,240,5)
    assert (2*64-81,2*63-80)==(47,46)

    result=dict(
      status='PASS',
      input_model='UUUTUUT, z=3m, section phases3,5,6; fixed prescribed dynamics',
      scope='At least six disjoint direct first-return domains have increasing tails for every positive phase-affine rank; no claim about other certificate classes.',
      witness_rows=rows,disjoint_starting_domains=11,disjoint_inequality_cycles=cycle_results,
      universal_lower_bound=6,
      lower_bound_domain='The eleven specified disjoint witness domains, without counting arbitrary residue refinements as new branches.',
      rank_class='R(m,i)=w_i*m+c_i, with arbitrary positive real w_i and fixed real c_i',
      chosen_weights=weights,chosen_weight_slacks=slacks,
      s12_rank_drop=dict(coefficient=47,constant=46,trace=states,
                        conclusion='S12 cannot be a smallest exceptional section state under rank(m,3)=m, rank(m,5)=m, rank(m,6)=2m.'),
      attainment_dependency='Attainment uses the complete frontier reconstruction in verify_relational.py and independent.py, including long-return bounds and finite exceptions.',
      verification_kind='Symbolic affine parity, positivity and first-return checks on entire progressions; exact rational products; no seed cutoff.')
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(status='PASS',witness_rows=11,disjoint_inequality_cycles=cycle_results,
         universal_lower_bound=6,s12_rank_drop='47*t+46 > 0 for every t>=0'),indent=2))


if __name__=='__main__':main()
