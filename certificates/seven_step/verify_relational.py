"""Exact whole-domain S06/S08 coalescence and complete rank refinement.

All trajectory calculations use physical n with the fixed forcing clock.
The residue exhaustions describe infinite affine domains, not seed samples.
No repository builder or earlier verifier is imported.
"""

from __future__ import annotations

if not __debug__:
    raise RuntimeError("This proof checker must not run with Python -O")

import argparse
import json
from collections import Counter
from fractions import Fraction as F
from pathlib import Path

DELTA = (0, 0, 1, -1, 0, 1, -1)
HEIGHT = (0, 0, 0, 1, 0, 0, 1)
SECTION = (3, 5, 6)
WEIGHT = {3: 1, 5: 1, 6: 2}
TIE = {3: 0, 5: 0, 6: 1}
CAP = {3: 3, 5: 8, 6: 7}
RESIDUAL = [
    dict(id="S00", phase=3, M=4, residue=3, A=9, b=7, out=5, steps=2, t_min=0),
    dict(id="S01", phase=5, M=2, residue=0, A=3, b=0, out=6, steps=1, t_min=1),
    dict(id="S02", phase=5, M=32, residue=3, A=81, b=9, out=3, steps=5, t_min=0),
    dict(id="S03", phase=5, M=128, residue=115, A=243, b=220, out=5, steps=7, t_min=0),
]


def physical_step(a: int, b: int, p: int) -> tuple[int, int, int]:
    assert a % 2 == 0, "Parity is not constant on this whole affine domain"
    if b % 2:
        a, b = 3 * a // 2, (3 * b + 1) // 2
    else:
        a, b = a // 2, b // 2
    b += DELTA[p]
    return a, b, (p + 1) % 7


def run_z(a: int, b: int, phase: int, length: int, q_min: int = 0,
          stop_at_section: bool = True) -> tuple[int, int, int, int, bool]:
    """Input/output use z; internal arithmetic independently uses physical n."""
    b = b - 1 + HEIGHT[phase]
    assert a * q_min + b >= 0
    for step in range(1, length + 1):
        a, b, phase = physical_step(a, b, phase)
        zb = b + 1 - HEIGHT[phase]
        assert a * q_min + b >= 0 and a * q_min + zb >= 1
        if stop_at_section and phase in SECTION and zb % 3 == 0:
            assert a % 3 == 0
            return a, zb, phase, step, True
    return a, b + 1 - HEIGHT[phase], phase, length, False


def affine_trace(m_a: int, m_b: int, phase: int, length: int) -> list[dict]:
    a, b = 3 * m_a, 3 * m_b - 1 + HEIGHT[phase]
    trace = [dict(phase=phase, physical_n_a=a, physical_n_b=b)]
    for _ in range(length):
        a, b, phase = physical_step(a, b, phase)
        assert a >= 0 and b >= 1
        trace.append(dict(phase=phase, physical_n_a=a, physical_n_b=b))
    return trace


def merger_proof() -> dict:
    # m=4q+3, all q>=0.  Source phase6; alternate phase5 has m_alt=2m.
    original = affine_trace(4, 3, 6, 2)
    alternate = affine_trace(8, 6, 5, 3)
    assert original[-1] == alternate[-1] == dict(phase=1, physical_n_a=27, physical_n_b=20)
    # rho_source=4m+1; rho_alternate=2(2m): strict gap exactly one.
    assert (4 * 4 - 2 * 8, 4 * 3 + 1 - 2 * 6) == (0, 1)
    families = []
    for label, M, residue in (("S06", 16, 7), ("S08", 64, 15)):
        assert M % 4 == 0 and residue % 4 == 3
        lhs = affine_trace(M, residue, 6, 2)
        rhs = affine_trace(2 * M, 2 * residue, 5, 3)
        assert lhs[-1] == rhs[-1]
        families.append(dict(id=label, original_m_a=M, original_m_b=residue,
                             alternate_phase=5, alternate_m_a=2*M, alternate_m_b=2*residue,
                             original_trace=lhs, alternate_trace=rhs,
                             refined_rank_gap=1))
    # Integer V decrease >=1 implies refined rank decrease >=1 for all phase pairs.
    minimum_preserved_gap = min(2 + TIE[p] - TIE[q] for p in SECTION for q in SECTION)
    assert minimum_preserved_gap == 1
    return dict(general_domain="phase6, m=4q+3, every integer q>=0",
                original_trace=original, alternate_trace=alternate,
                refined_rank_gap=1, minimum_preserved_old_strict_gap=1,
                families=families)


def literal_return(m: int, p: int) -> tuple[int, int, int]:
    n = 3*m - 1 + HEIGHT[p]
    for steps in range(1, 100):
        n = (n//2 if n % 2 == 0 else (3*n+1)//2) + DELTA[p]
        p = (p+1) % 7
        z = n + 1 - HEIGHT[p]
        assert n >= 0 and z >= 1
        if p in SECTION and z % 3 == 0:
            return z//3, p, steps
    raise AssertionError("Explicit finite base trace did not return")


def long_return_proof() -> dict:
    avoid, exits = [], []
    for r in range(384):
        lo = int(r == 0)
        a, b, p, d, hit = run_z(384, r, 0, 7, lo)
        if hit:
            assert 27*384 - 8*WEIGHT[p]*a >= 0
            assert 27*(384*lo+r) - 8*WEIGHT[p]*(a*lo+b) >= 0
            exits.append((r, p, d))
        else:
            assert p == 0 and a < 384 and 1 <= b < r
            assert 128*a <= 27*384 and 128*b <= 27*r+220
            avoid.append((r, a, b))
    assert len(avoid) == 14 and len(exits) == 370

    for p, length, alpha, beta in ((5,2,F(3,4),F(5,4)), (6,1,F(3,2),F(1,2))):
        M = 2**length
        for r in range(M):
            lo = int(r == 0)
            a, b, q, d, hit = run_z(3*M, 3*r, p, length, lo)
            if hit:
                assert (p, q, d) == (5, 6, 1)
            else:
                assert q == 0 and d == length
                ga, gb = alpha*3*M-a, alpha*3*r+beta-b
                assert ga >= 0 and ga*lo+gb >= 0

    c, fixed, g = F(27,128), F(220,101), F(27,8)
    long_cases = []
    for p, alpha, beta, threshold in ((5,F(3,4),F(5,4),15), (6,F(3,2),F(1,2),9)):
        # The affine alignment bound is above the avoiding-map fixed point.
        # Thus iterating its increasing contraction cannot exceed its first image.
        assert alpha * threshold + beta >= fixed
        a = g*c*alpha
        b = g*(fixed+c*(beta-fixed))
        assert a < WEIGHT[p] and a*threshold+b < WEIGHT[p]*threshold
        assert CAP[p] == (7-p)+6
        finite = []
        for m in range(1, (threshold+2)//3):
            out, q, steps = literal_return(m,p)
            assert steps <= CAP[p] or WEIGHT[q]*out < WEIGHT[p]*m
            finite.append((m,out,q,steps))
        long_cases.append(dict(phase=p, z_threshold=threshold,
                               weighted_z_bound_a=str(a), weighted_z_bound_b=str(b),
                               finite_checks=finite))
    return dict(phase_zero_domains=384, avoiding_domains=len(avoid),
                exit_domains=len(exits), weighted_exit_envelope="w_out*z_out <= 27z/8",
                avoiding_envelope="z_next <= (27z+220)/128", long_cases=long_cases)


def complete_frontier() -> dict:
    summaries, finite_exceptions = [], set()
    for phase, cap in CAP.items():
        M = 2**cap
        counts = Counter()
        for r in range(M):
            lo = int(r == 0)
            a,b,p,steps,hit = run_z(3*M,3*r,phase,cap,lo)
            matches = [row for row in RESIDUAL
                       if row['phase']==phase and r%row['M']==row['residue']]
            assert len(matches) <= 1
            if not hit:
                assert phase in (5,6) and not matches
                counts['long_return_rank_decrease'] += 1
                continue
            assert a%3 == b%3 == 0
            a,b = a//3,b//3
            # Old weighted target minus source, before the tie-break refinement.
            gain = WEIGHT[p]*a-WEIGHT[phase]*M
            const = WEIGHT[p]*b-WEIGHT[phase]*r
            assert gain != 0
            if gain > 0:
                assert gain*lo+const > 0
                if phase == 6:
                    assert not matches and M%4==0 and r%4==3
                    # Entire domain uses the checked merger; alternate rank is source minus1.
                    assert (2*WEIGHT[phase]*M - 2*(2*M),
                            2*WEIGHT[phase]*r+TIE[phase] - 2*(2*r)) == (0,1)
                    counts['strict_relational_reduction'] += 1
                else:
                    assert len(matches)==1
                    row = matches[0]
                    scale,shift=M//row['M'],(r-row['residue'])//row['M']
                    assert (a,b,p,steps)==(row['A']*scale,row['A']*shift+row['b'],row['out'],row['steps'])
                    counts['remaining_growing'] += 1
            else:
                assert not matches
                upper=const//(-gain)
                if upper >= lo:
                    assert lo==upper==0
                    finite_exceptions.add((phase,r,p,b,steps))
                    counts['finite_base_exception'] += 1
                else:
                    assert 2*(gain*lo+const)+TIE[p]-TIE[phase] < 0
                    counts['strict_forward_rank_decrease'] += 1
        assert sum(counts.values())==M
        summaries.append(dict(phase=phase, input_modulus=M, **dict(counts)))
    assert finite_exceptions=={(3,1,5,1,2),(3,2,6,1,3),(5,1,5,1,7)}
    assert literal_return(1,3)==(1,5,2)
    assert literal_return(2,3)==(1,6,3)
    assert literal_return(1,6)==(1,3,4)
    assert literal_return(1,5)==(1,5,7)
    known=(0,0,0,1,1,2,2)
    for p,n in enumerate(known):
        assert (n//2 if n%2==0 else (3*n+1)//2)+DELTA[p]==known[(p+1)%7]
    return dict(infinite_input_domains=sum(2**cap for cap in CAP.values()),
                audit=summaries, finite_base_exceptions=sorted(finite_exceptions),
                remaining_families=RESIDUAL)


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    result=dict(status='passed', rank='rho(m,3)=rho(m,5)=2m; rho(m,6)=4m+1',
                physical_forcing=list(DELTA), height=list(HEIGHT),
                section_phases=list(SECTION),
                coordinate='z=n+1-height[phase]; section parameter m=z/3',
                return_convention='First strictly later section visit, including shrinking-step visits',
                merger=merger_proof(), long_returns=long_return_proof(),
                complete_frontier=complete_frontier(),
                scope='S06 and S08 are whole-family induction reductions; four infinite obligations remain.',
                numeric_seed_census=False)
    if args.output:
        args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(status='passed', newly_reduced=['S06','S08'],
                          remaining=[r['id'] for r in RESIDUAL],
                          infinite_input_domains=392, phase_zero_domains=384)))


if __name__=='__main__':
    main()
