"""Exact intermediate calculations used in the expanded inverse exposition."""
if not __debug__:
    raise SystemExit("Run without -O so mathematical assertions remain enabled.")
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
WORD=(1,0,-1)


def step(n,d):
    return (n//2 if n%2==0 else (3*n+1)//2)+d


def run(n,length):
    path=[n]
    for k in range(length):
        n=step(n,WORD[k%3]);path.append(n)
        assert n>=0
    return path


def reconstruct():
    rows=[]
    for r in range(8):
        a,b=8,r;parities=[];intermediate=[]
        for d in WORD:
            assert a%2==0
            odd=b%2;parities.append(odd)
            if odd:a,b=3*a//2,(3*b+1)//2+d
            else:a,b=a//2,b//2+d
            intermediate.append([a,b])
        assert a==3**sum(parities)
        rows.append(dict(residue=r,parities=parities,intermediate_affine=intermediate,
                         return_coefficient=a,return_offset=b))
    assert [(r['return_coefficient'],r['return_offset']) for r in rows]==[(3,0),(27,7),(3,1),(9,4),(9,7),(9,6),(1,0),(3,2)]
    assert run(18,6)[-1]==2 and run(82,6)[-1]==11
    assert (64*2+34)%9==0 and (64*11+34)%9==0 and (64*5+34)%9!=0
    attachments=[]
    for target,predecessor,middle in ((0,16,6),(1,118,14),(3,70,8),(9,208,78)):
        path=run(predecessor,6)
        assert path[3]==middle and path[-1]==target
        assert predecessor>=2 and predecessor%3!=0
        attachments.append(dict(target=target,predecessor=predecessor,middle=middle,path=path))
    copies=[]
    for seed in (0,1):
        value=seed
        for _ in range(3):value=8*value+6
        path=run(value,9)
        assert path[-1]==seed
        copies.append(dict(target=seed,seed=value,path=path))
    assert [x['seed'] for x in copies]==[438,950]
    assert 438%512==950%512
    assert 6*((8**8-1)//7)==14380470
    assert 281<2**12
    return dict(three_step_affine_branches=rows,eligible_attachments=attachments,
                two_letter_word=dict(application_order=['B2','B1'],formula='(64*y+34)/9',
                    exact_domain='y = 2 (mod 9)',examples=[dict(target=2,predecessor=18,path=run(18,6)),
                                                        dict(target=11,predecessor=82,path=run(82,6))],
                    rejected_target=5),binary_copies=copies,
                all_even_24_step=dict(coefficient=2**24,offset=14380470),
                worst_factor_count=dict(children=281,common_factor=2**24,square_root_threshold=2**12))


def main():
    import argparse
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args();value=reconstruct()
    if args.output:args.output.write_text(json.dumps(value,indent=2)+'\n')
    else:
        stored=json.loads((HERE/'worked_examples.json').read_text())
        if json.dumps(value,sort_keys=True)!=json.dumps(stored,sort_keys=True):
            raise ValueError('Worked inverse examples changed')
    print('Exact inverse worked examples passed: eight affine branches, legal/illegal inverse words, binary copies, and weighted-count comparison.')


if __name__=='__main__':main()
