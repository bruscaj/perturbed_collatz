#!/usr/bin/env python3
"""Independent original-rank and physical replay checks for the unified selector."""
from collections import Counter
from fractions import Fraction
from pathlib import Path
import argparse,hashlib,json,re,time
from b1_selector import (B1Selector,INPUTS,ELEMENTARY,IMPULSES,v2,
    unbounded_g_h,inherited_shadow_repayment,maximal_g_h,replay_witness,physical_run)
from full_menu import require,D
from verify_balanced_repayment import load_previous_selector
from maximal_two_run import strict_extension_ray

HERE=Path(__file__).resolve().parent
HEIGHT=(0,0,0,1,0,0,1)


def affine(a,b,p,n):
    for _ in range(n):
        require(a%2==0 and a>0 and b>=HEIGHT[p],'nonuniform or unsafe affine path')
        if b%2:a,b=3*a//2,(3*b+1)//2
        else:a,b=a//2,b//2
        b+=IMPULSES[p];p=(p+1)%7
    require(b>=HEIGHT[p],'unsafe affine endpoint')
    return a,b,p


def validate_ray(ray):
    M,r,A,B,path=(ray[k] for k in('M','r','A','B','path'))
    require(M==128**len(path) and 0<A<=M and 0<B<r<=M,'ray domain/rank invalid')
    a,b,p=6*M,6*r-1,1
    for label in path:
        require(a%768==0 and ((b+1)//6-1)%128+1==label,'ray primitive guard metadata invalid')
        a,b,p=affine(a,b,p,7)
        require(a%6==0 and (b+1)%6==0 and p==1,'period does not return to B1')
    require((a,b,p)==(6*A,6*B-1,1),'whole-ray physical endpoint differs')


def independent_word_ray(k):
    ell=(k+3)//4
    M,r,A,B=1,1,1,1
    for rho,alpha,beta in [(4,243,8)]*k+[(11,9,1)]*ell:
        j=(rho-B)*pow(A,-1,128)%128
        M,r,A,B=M*128,M*j+r,alpha*A,alpha*((A*j+B-rho)//128)+beta
    return {'M':M,'r':r,'A':A,'B':B,'path':[4]*k+[11]*ell}


def inherited_example(h,j=0):
    modulus=729**h
    coefficient=601*(1<<17)*(1<<(7*h))
    r=(-752*pow(coefficient,-1,modulus))%modulus
    if r==0:r=modulus
    r+=j*modulus
    q=(752+coefficient*r)//modulus
    numerator=(1<<(7*h))*q-151
    require(numerator%601==0,'inherited CRT source not integral')
    return numerator//601,h,q,r


def check_bank_inclusion(selector):
    elementary_text=(INPUTS/'B1AllGuards.lean').read_text()
    section=elementary_text.split('def B1ElementaryGuard',1)[1].split('theorem',1)[0]
    pairs={int(a):int(b) for a,b in re.findall(r'r = (\d+) ∧ c = (\d+)',section)}
    require(pairs==ELEMENTARY,'pinned elementary definition changed')
    direct_text=(INPUTS/'B1SelfReturns.lean').read_text().split('def B1DirectGuard',1)[1].split('theorem',1)[0]
    residues={int(v) for v in re.findall(r't % 128 = (\d+)',direct_text)}
    require(residues==selector.direct_residues,'pinned direct bank differs')
    definition=(INPUTS/'B1FinalObligation.lean').read_text().split('def B1SelfCertified',1)[1].split('theorem',1)[0]
    required=('B1ElementaryGuard','59049^h*q','16777216*v+1','B1DirectGuard t','B1RepaymentGuard t')
    require(all(x in definition for x in required),'pinned bank clauses differ')
    # Whole low-residue terminals prove inclusion for every unbounded h.
    terminal_classes=0
    for k,q in ELEMENTARY.items():
        p=(2+k)%7
        u=sum((2+j)%7 not in(3,6) for j in range(k))
        y=pow(3,u+1,4)*q%4
        require(all(selector.menu.tables[3][p][r] for r in range(y,D,4)),
                'elementary whole terminal class not in full ratio3')
        terminal_classes+=1
    require(pow(3,10,4)==1,'14-step pump does not preserve elementary class')
    # Trip: k=14h+6; y=3^(10h+5)q, and 3^(10h)q=15 mod32.
    require(pow(3,5,32)*15%32==29,'tripling residue conversion failed')
    require(all(selector.menu.tables[3][1][r]==5 for r in range(29,D,32)),
            'tripling bridge terminal class absent')
    # Check the inherited selector's forced terminal valuation symbolically.
    require(752==16*47 and 601%2==1,'inherited terminal valuation premise')
    return {'bank_scope':'Pinned concurrent working-tree B1SelfCertified, including its inherited repayment clause; no commit/merge status claimed.',
            'elementary_clauses_contained_by_full_ratio3':terminal_classes,
            'tripling_clause_contained_by_ratio3_phase1_residue29_mod32':True,
            'direct_residues_contained':len(residues),'shadow_and_base_included':True,
            'inherited_repayment_included_with_exact_unique_depth_selector':True,
            'proof':'See B1_SELECTOR.md; finite residue checks establish complete terminal classes, and valuation identities cover arbitrary pump depths.'}


def proof_unbounded():
    g=Fraction(243,128);h=Fraction(9,128)
    c=Fraction(52,115);d=Fraction(29,119)
    budget=g**4*h
    require(budget==Fraction(31381059609,34359738368)<1,'wrong uniform repayment budget')
    require(all(g**j*h<=budget for j in range(1,5)),'remainder budget failed')
    gap=8-budget*(8+c)-d
    require(gap==Fraction(4332506554387,117553254891520)>0,'original t>=8 rank floor failed')
    for t in range(128):
        require(((115*t+52)%128==0)==(t==4),'G guard equivalence failed')
        require(((119*t-29)%128==0)==(t==11),'H guard equivalence failed')
        require(((601*t+151)%128==0)==(t==17),'inherited growth guard failed')
    require(affine(768,23,1,7)==(1458,47,1),'G whole physical primitive')
    require(affine(768,65,1,7)==(54,5,1),'H whole physical primitive')
    require(affine(768,101,1,7)==(4374,587,1),'inherited growth whole primitive')
    require(affine(6*(1<<24),5,1,25)==affine(6*1179648,5,1,18),'shadow whole affine merger')
    require(affine(768,767,1,7)==(1458,1457,1),'243 pump whole physical primitive')
    density=sum((Fraction(1,128**(j+1)) for j in range(1,5)),Fraction())/(1-Fraction(1,128**5))
    require(density==Fraction(2113665,34359738367),'unbounded word-family density')
    return {'G_H_budget_multiplier':str(budget),'positive_rank_floor_gap_at_t8':str(gap),
            'G_H_exact_source_density':str(density),
            'G_H_density_scope':'This disjoint guarded-word family only; no overall selected-union density claim.',
            'maximal_G_depth':'floor(v2(115t+52)/7)',
            'H_suffix_equivalent_guard':'128^ceil(k/4) divides 119*G^k(t)-29',
            'inherited_repayment_depth':'v2(601t+151)=7h+4, h>=1',
            'new_G_sources_excluded_from_inherited_repayment':'t=4mod128 is even, so601t+151 is odd.',
            'physical_primitives_verified':5,
            'model':'Finite-state guard selector plus explicit accelerated natural counters; not a DFA theorem for the full unbounded relation.'}


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path,default=HERE/'b1_selector_verification.json');args=parser.parse_args()
    started=time.time();selector=B1Selector();previous_selector=load_previous_selector()
    for ray in selector.composed['rays']:validate_ray(ray)
    for ray in selector.extra_rays:validate_ray(ray)
    bank=check_bank_inclusion(selector);proof=proof_unbounded()
    counts=Counter();examples={};unhandled=[];old_count=0;replays=0
    baseline_preserved=0;new_in_diagnostic=0
    for t in range(1,100001):
        w=selector.select(t)
        previous=previous_selector.select(t)
        if previous['status']!='unhandled':
            require(w==previous,'a pre-extension selected witness or label changed')
            baseline_preserved+=1
        elif w['status']!='unhandled':new_in_diagnostic+=1
        label=w.get('proof_rule','unhandled');counts[label]+=1
        if w['status']=='unhandled':
            if len(unhandled)<30:unhandled.append(t)
        else:
            replay_witness(w);replays+=1;examples.setdefault(label,w)
        if selector.old_bank_predicate(t):
            old_count+=1;require(w['status']!='unhandled','selector lost a pinned old-bank input')
    large=[]
    # Exercise each infinite guard family separately, including guards that
    # another earlier selector rule may also recognize.
    for k in (1,2,3,4,5,8,12,20,40,100,1000):
        ray=independent_word_ray(k);validate_ray(ray)
        for v in (0,1,243):
            t=ray['M']*v+ray['r'];w=unbounded_g_h(t)
            require(w is not None and w['target_t']==ray['A']*v+ray['B'],'unbounded selector missed generated whole ray')
            require(w['growing_periods']==k,'not exact maximal growing depth')
            require(v2(601*t+151)==0 and inherited_shadow_repayment(t) is None,'new and inherited guard separation failed')
            replay_witness(w)
        large.append({'k':k,'source_bit_length':ray['r'].bit_length(),'steps':7*len(ray['path']),
                      'whole_ray_checked':True,'sampled_parameters':3})
    repayment=[]
    for h in (1,2,3,4,8,20,40,100):
        for j in (0,1):
            t,_,q,r=inherited_example(h,j)
            w=inherited_shadow_repayment(t)
            require(w is not None and w['growing_periods']==h and w['defining_q']==q and w['defining_r']==r,'inherited exact selector missed witness')
            require(selector.old_bank_predicate(t),'inherited example not in old bank')
            combined=selector.select(t);require(combined['status']!='unhandled','combined selector lost inherited guard')
            replay_witness(w);replay_witness(combined)
        repayment.append({'h':h,'examples':2})
    # Recorded CRT examples at arbitrary k exercise the combined selector's
    # unbounded branch after all earlier finite/paired rules have declined.
    unbounded_selected=[]
    for row in selector.unbounded['examples']:
        if row['k']<4:continue
        t=row['escape_source_t'][1]
        w=selector.select(t)
        require(w['status']=='reduction' and w['proof_rule']=='unbounded_G4_H11_repayment',
                'recorded unbounded CRT family not selected after finite rules')
        replay_witness(w)
        examples.setdefault(w['proof_rule'],w)
        unbounded_selected.append({'k':row['k'],'source_t':t,'target_t':w['target_t'],
                                   'source_steps':w['source_steps'],'target_steps':w['target_steps']})
    # Explicitly exercise all new28-step rays and shadow clocks.
    for ray in selector.extra_rays:
        for v in(0,1,19683):
            t=ray['M']*v+ray['r'];w=selector.select(t)
            require(w['status']!='unhandled','28-step ray lost');replay_witness(w)
            examples.setdefault(w['proof_rule'],w)
    for v in (1,2,243,10000):
        t=(1<<24)*v+1;w=selector.select(t);require(w['status']!='unhandled','shadow missed');replay_witness(w)
        examples.setdefault(w['proof_rule'],w)
    # Universal pump inclusions are proved above; these high-depth examples
    # check the executable predicate's arithmetic and returned clocks.
    pumped_examples=0
    for h in (0,1,4,20,100):
        for k0,residue in ELEMENTARY.items():
            q=residue+4*((-residue)*pow(4,-1,3)%3)
            t=(1<<(14*h+k0))*q
            require(t%3==0 and selector.old_bank_predicate(t),'elementary sample invalid')
            w=selector.select(t);require(w['status']!='unhandled','elementary pump missed');replay_witness(w)
            pumped_examples+=1
        q0=15*pow(pow(59049,h,32),-1,32)%32
        q=q0+32*((-q0)*pow(32,-1,3)%3)
        t=(1<<(14*h+6))*q
        require(selector.old_bank_predicate(t),'trip sample invalid')
        w=selector.select(t);require(w['status']!='unhandled','trip sample missed');replay_witness(w)
        pumped_examples+=1
    # Exercise the extensions through the combined entry point, not merely
    # their standalone functions. The original quota keeps its earlier label.
    extension_examples=[]
    strict_ray,_=strict_extension_ray()
    for v in(0,1,2):
        t=strict_ray['source_a']*v+strict_ray['source_b']
        require(unbounded_g_h(t) is None,'maximal strict-extension source lies in old quota')
        direct=maximal_g_h(t)
        require(direct is not None and direct['growing_periods']==33 and direct['contracting_periods']==8,
                'maximal adapter did not preserve exact run lengths')
        replay_witness(direct)
        w=selector.select(t);require(w['status']!='unhandled','combined maximal source lost')
        replay_witness(w)
        if w['proof_rule']=='maximal_G4_H11_repayment':
            require(previous_selector.select(t)['status']=='unhandled','maximal branch preempted a frozen witness')
            extension_examples.append(w);examples.setdefault(w['proof_rule'],w)
    require(any(w['proof_rule']=='maximal_G4_H11_repayment' for w in extension_examples),
            'combined selector never exercised new maximal branch')
    homogeneous_checks=0
    for k in(1,2,7,32):
        for residue in selector.balanced.growing:
            ray=selector.balanced.homogeneous_ray(residue,k)
            for v in(0,1):
                t=ray['M']*v+ray['r'];w=selector.select(t)
                require(w['status']!='unhandled','combined homogeneous family lost')
                replay_witness(w);homogeneous_checks+=1
    t=217760110;w=selector.select(t)
    require(w['proof_rule']=='homogeneous_growth_J123_balanced_repayment' and w['target_t']==34920345,
            'combined homogeneous extension example changed')
    require(previous_selector.select(t)['status']=='unhandled','homogeneous example already in frozen selector')
    replay_witness(w);extension_examples.append(w);examples.setdefault(w['proof_rule'],w)
    word=[4,14,23];ray=selector.balanced.mixed_ray(word)
    mixed=selector.consume_mixed(ray['r'],word)
    require(mixed is not None and mixed['target_t']==ray['B'],'supplied-word mixed API failed')
    replay_witness(mixed)
    require(selector.consume_mixed(ray['r'],[14,4,23]) is None,'mixed API accepted an incorrect first guard')
    result={'scope':'Constructive selector for explicitly combined B1 library, containing the frozen B1SelfCertified bank and preserving the frozen pre-extension selector. Includes maximal G/H and all21 homogeneous balanced families. No all-repository coverage or global capture.',
      'source_pins':selector.pins,'bank_inclusion':bank,'unbounded_proof_audit':proof,
      'whole_finite_rays_verified':len(selector.composed['rays'])+len(selector.extra_rays),
      'composed_depth3_rays':len(selector.composed['rays']),'additional28_step_rays':len(selector.extra_rays),
      'bounded_diagnostic':{'through_parameter':100000,'selector_label_counts':dict(counts),
                            'returned_witnesses_physically_replayed':replays,
                            'pinned_old_bank_inputs_checked':old_count,'old_bank_misses':0,
                            'pre_extension_witnesses_preserved_exactly':baseline_preserved,
                            'newly_selected_vs_pre_extension':new_in_diagnostic,
                            'first_unhandled_parameters':unhandled,
                            'interpretation':'Diagnostic on these finite parameters only, not an asymptotic density or noncapture list.'},
      'representative_constructive_witnesses':examples,
      'unbounded_G_H_whole_ray_checks':large,'inherited_repayment_checks':repayment,
      'combined_selector_unbounded_CRT_examples':unbounded_selected,
      'other_unbounded_old_bank_replays':pumped_examples,
      'extension_integration':{'homogeneous_generated_sources_checked':homogeneous_checks,
                               'maximal_G33_H8_sources_checked':3,
                               'new_branch_examples':extension_examples,
                               'mixed_supplied_word_witness':mixed,
                               'mixed_wrong_word_rejected':True,
                               'original_quota_rule_and_labels_preserved':True,
                               'source_language_nonregularity_scope':'Any nonregularity theorem in the surrounding research concerns only the original fixed-quota language D, not the enlarged selector, maximal domain, homogeneous language or mixed language.'},
      'all_passed':True,'elapsed_seconds':round(time.time()-started,3),
      'source_hashes':{name:hashlib.sha256((HERE/name).read_bytes()).hexdigest() for name in('b1_selector.py','verify_b1_selector.py','full_menu.py','balanced_repayment.py','maximal_two_run.py','verify_balanced_repayment.py','selector_inputs/b1_selector_before_extensions.py')},
      'formalization_boundary':'Pinned old-bank Lean source is preserved for provenance; this verifier does not perform a new Lean build. The parent formal package supplies a generic repayment-envelope bound; concrete J123/21-branch adaptation and the combined selector are checked here by exact arithmetic and physical replay.'}
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'output':str(args.output),'finite_rays':result['whole_finite_rays_verified'],
                      'counts':dict(counts),'old_bank_misses':0,'unbounded_max_k':1000,
                      'all_passed':True,'elapsed_seconds':result['elapsed_seconds']}))

if __name__=='__main__':main()
