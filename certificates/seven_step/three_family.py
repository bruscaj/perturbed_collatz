"""Exact alternative four-phase section: 43 cylinders, three growing families.

Adaptive positive-coordinate partition and independent full-modulus physical
replay. All arithmetic is integer or Fraction. This checker does not prove
capture of the three universal residual domains. A separate bundled Lean
theorem formalizes the conditional positive-seed capture equivalence;
these Python calculations remain a distinct arithmetic reconstruction.
"""
from __future__ import annotations
if not __debug__:
    raise SystemExit("Exact checks require normal Python; do not use -O.")
import argparse
from collections import Counter
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
DELTA = (0, 0, 1, -1, 0, 1, -1)
HEIGHT = (0, 0, 0, 1, 0, 0, 1)
KNOWN_N = (0, 0, 0, 1, 1, 2, 2)
MARKS = (1, 2, 3, 5)
WEIGHTS = {1: 4, 2: 7, 3: 4, 5: 5}
CAPS = {1: 2, 2: 7, 3: 6, 5: 7}


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False)


def read_json(path):
    def unique(pairs):
        out = {}
        for key, value in pairs:
            if key in out:
                raise ValueError("Duplicate JSON key")
            out[key] = value
        return out
    def bad(value):
        raise ValueError("Nonfinite JSON number: " + value)
    return json.loads(Path(path).read_text(), object_pairs_hook=unique, parse_constant=bad)


def positive_step(a, b, phase):
    """Whole-domain z=a*q+b update, with constant parity."""
    assert a % 2 == 0
    growing = b % 2 == HEIGHT[phase]
    if growing:
        a, b = 3*a//2, (3*b + HEIGHT[phase])//2
    else:
        a, b = a//2, (b + 1-HEIGHT[phase])//2
    return a, b, (phase+1)%7, "G" if growing else "S"


def adaptive(source):
    """Split the free parameter into even/odd lifts before every update."""
    leaves = []
    def visit(modulus, residue, a, b, phase, trace):
        if len(trace) == CAPS[source]:
            raise ArithmeticError("A cylinder did not return by the stated cap")
        assert a % 2 == 1 and a % 3 == 0
        for parity in (0, 1):
            mod, res = 2*modulus, residue+parity*modulus
            aa, bb, target, letter = positive_step(2*a, b+parity*a, phase)
            lower = int(res == 0)
            assert aa*lower+bb >= 1 and aa % 3 == 0
            history = trace+letter
            if target in MARKS and bb % 3 == 0:
                leaves.append(dict(source=source, modulus=mod, residue=res,
                    parameter_min=lower, coefficient=aa//3, offset=bb//3,
                    target=target, steps=len(history), trace=history))
            else:
                visit(mod, res, aa, bb, target, history)
    visit(1, 0, 3, 0, source, "")
    assert sum((Fraction(1,r["modulus"]) for r in leaves), Fraction()) == 1
    for i, row in enumerate(leaves):
        for other in leaves[i+1:]:
            assert (row["residue"]-other["residue"]) % min(row["modulus"],other["modulus"]) != 0
    return sorted(leaves, key=lambda r:(r["modulus"],r["residue"]))


def physical_affine(a, b, phase, lower, cap):
    """Independent signed n arithmetic, stopping at the first later mark."""
    assert a*lower+b >= HEIGHT[phase]
    for clock in range(1,cap+1):
        assert a % 2 == 0
        if b % 2:
            a, b = 3*a//2, (3*b+1)//2+DELTA[phase]
        else:
            a, b = a//2, b//2+DELTA[phase]
        phase=(phase+1)%7
        assert a*lower+b >= HEIGHT[phase]
        z_offset=b+1-HEIGHT[phase]
        assert a % 3 == 0
        if phase in MARKS and z_offset % 3 == 0:
            return dict(coefficient=a//3, offset=z_offset//3,
                        target=phase, steps=clock)
    raise ArithmeticError("Full physical affine class did not reach the section")


def capture(m, phase):
    n=3*m-1+HEIGHT[phase]; path=[]
    for ticks in range(101):
        path.append([n,phase])
        if n == KNOWN_N[phase]:
            return dict(m=m, phase=path[0][1], ticks=ticks, physical_path=path)
        if ticks == 100:
            raise ArithmeticError("Finite exceptional state not captured")
        n=(n//2 if n%2==0 else (3*n+1)//2)+DELTA[phase]
        phase=(phase+1)%7
        assert n >= HEIGHT[phase]


def reconstruct():
    assert all(HEIGHT[(i+1)%7]-HEIGHT[i]==DELTA[i] for i in range(7))
    assert all((KNOWN_N[i]//2 if KNOWN_N[i]%2==0 else (3*KNOWN_N[i]+1)//2)+DELTA[i]
               ==KNOWN_N[(i+1)%7] for i in range(7))
    rows=[row for phase in MARKS for row in adaptive(phase)]
    assert len(rows)==43
    growing=[]; exceptions=set()
    for row in rows:
        slope=WEIGHTS[row["target"]]*row["coefficient"]-WEIGHTS[row["source"]]*row["modulus"]
        offset=WEIGHTS[row["target"]]*row["offset"]-WEIGHTS[row["source"]]*row["residue"]
        row["rank_change"]=[slope,offset]
        if slope>0:
            assert slope*row["parameter_min"]+offset>0
            growing.append(row)
        elif slope==0:
            assert offset<0
        else:
            for q in range(row["parameter_min"],offset//(-slope)+1):
                exceptions.add((row["modulus"]*q+row["residue"],row["source"]))
    assert [(r["source"],r["modulus"],r["residue"],r["coefficient"],r["offset"],r["target"],r["rank_change"])
            for r in growing]==[(1,2,0,3,0,2,[13,0]),(3,4,3,9,7,5,[29,23]),(5,8,2,27,7,1,[68,18])]
    assert exceptions=={(1,1),(1,3),(1,5),(3,5),(5,3)}
    finite=[capture(m,p) for m,p in sorted(exceptions)]
    assert [r["ticks"] for r in finite]==[4,2,0,14,16]

    replay=[]
    for phase, cap in CAPS.items():
        modulus=2**cap
        for residue in range(modulus):
            leaf,=[r for r in rows if r["source"]==phase and residue%r["modulus"]==r["residue"]]
            got=physical_affine(3*modulus,3*residue-1+HEIGHT[phase],phase,int(residue==0),cap)
            assert got["coefficient"]==leaf["coefficient"]*(modulus//leaf["modulus"])
            assert got["offset"]==leaf["coefficient"]*((residue-leaf["residue"])//leaf["modulus"])+leaf["offset"]
            assert got["target"]==leaf["target"] and got["steps"]==leaf["steps"]
            replay.append(dict(source=phase,modulus=modulus,residue=residue,**got))
    assert len(replay)==324
    entry=[]; modulus=3*2**9
    for residue in range(modulus):
        got=physical_affine(modulus,residue-1,0,int(residue==0),5)
        entry.append(dict(modulus=modulus,residue=residue,**got))
    assert len(entry)==1536 and max(r["steps"] for r in entry)==5

    cycle_keys=[[(1,"G"),(2,"SGG"),(5,"GGS")],
                [(1,"SG"),(3,"GS"),(5,"GGG")],
                [(2,"G"),(3,"GG"),(5,"GSSG")]]
    witness_rows=[]; used=set()
    for keys in cycle_keys:
        cycle=[];gain=Fraction(1)
        for key in keys:
            row,=[r for r in rows if (r["source"],r["trace"])==key]
            assert key not in used;used.add(key)
            cycle.append(row);gain*=Fraction(row["coefficient"],row["modulus"])
        assert all(cycle[i]["target"]==cycle[(i+1)%3]["source"] for i in range(3))
        assert gain==Fraction(243,128)>1
        witness_rows.append(dict(keys=keys,gain=str(gain)))

    return dict(schema=1,forcing=DELTA,height=HEIGHT,marks=MARKS,
        weights={str(k):v for k,v in WEIGHTS.items()},caps={str(k):v for k,v in CAPS.items()},
        return_convention="first strictly later phase in marks with positive z divisible by three",
        scope="Conditional positive-seed global capture equivalence with three universal obligations; separately formalized by Collatz.ReleaseBridge.global_capture_iff_three. Python affine/entry reconstruction remains separate evidence.",
        cylinders=rows,growing_families=growing,finite_captures=finite,
        physical_return_classes=len(replay),physical_return_digest=sha256(canonical(replay).encode()).hexdigest(),
        entry_classes=len(entry),entry_max_ticks=5,arbitrary_phase_entry_bound=11,
        entry_histogram=dict(sorted(Counter(str(r["steps"]) for r in entry).items())),
        entry_digest=sha256(canonical(entry).encode()).hexdigest(),rank_obstruction_cycles=witness_rows)


def check(candidate=HERE/"three_family.json"):
    result=reconstruct()
    if canonical(read_json(candidate))!=canonical(result):
        raise ValueError("Three-family certificate differs from exact reconstruction")
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    parser.add_argument("--certificate",type=Path,default=HERE/"three_family.json")
    args=parser.parse_args()
    if args.output:
        value=reconstruct();args.output.write_text(json.dumps(value,indent=2)+"\n")
    else:
        value=check(args.certificate)
    print("Three-family exact checks passed: 43 adaptive cylinders, 324 independent physical return classes, 1536 entry classes, 5 finite captures.")


if __name__=="__main__":
    main()
