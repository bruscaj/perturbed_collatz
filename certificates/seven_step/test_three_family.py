"""Reject malformed or mathematically altered three-family certificates."""
if not __debug__:
    raise SystemExit("Exact checks require normal Python; do not use -O.")
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile

import three_family as certificate


def main():
    baseline=json.loads(certificate.canonical(certificate.check()))
    cases=[]
    def mutate(name,change):
        value=copy.deepcopy(baseline);change(value)
        cases.append((name,json.dumps(value)))
    mutate('changed forcing',lambda x:x['forcing'].__setitem__(0,1))
    mutate('changed section',lambda x:x['marks'].append(6))
    mutate('incompatible rank',lambda x:x['weights'].__setitem__('2',6))
    mutate('missing affine domain',lambda x:x['cylinders'].pop())
    mutate('wrong affine coefficient',lambda x:x['cylinders'][0].__setitem__('coefficient',2))
    mutate('wrong destination phase',lambda x:x['cylinders'][0].__setitem__('target',3))
    mutate('later return substituted',lambda x:x['cylinders'][0].__setitem__('steps',8))
    mutate('zero input admitted',lambda x:x['cylinders'][0].__setitem__('parameter_min',0))
    mutate('wrong rank change',lambda x:x['cylinders'][0].__setitem__('rank_change',[0,0]))
    mutate('omitted open family',lambda x:x['growing_families'].pop())
    mutate('empty capture chain',lambda x:x['finite_captures'][-1].__setitem__('physical_path',[]))
    mutate('incorrect entry bound',lambda x:x.__setitem__('arbitrary_phase_entry_bound',10))
    mutate('omitted obstruction',lambda x:x['rank_obstruction_cycles'].pop())
    mutate('scope silently strengthened',lambda x:x.__setitem__('scope','Unconditional global capture'))
    mutate('boolean schema accepted as integer',lambda x:x.__setitem__('schema',True))
    cases += [('empty object','{}'),('duplicate key','{"schema":1,"schema":1}'),
              ('nonfinite number','{"schema":NaN}')]
    with tempfile.TemporaryDirectory(prefix='collatz-three-family-hostile-') as tmp:
        path=Path(tmp)/'candidate.json'
        for name,content in cases:
            path.write_text(content)
            try: certificate.check(path)
            except (ValueError,AssertionError): pass
            else: raise RuntimeError('Accepted corrupted certificate: '+name)
    for name in ('three_family.py','test_three_family.py'):
        result=subprocess.run([sys.executable,'-O','-B',str(certificate.HERE/name)],
                              capture_output=True,text=True)
        if result.returncode==0 or 'do not use -O' not in result.stdout+result.stderr:
            raise RuntimeError('Missing optimization rejection: '+name)
    print(f'Three-family hostile checks passed: {len(cases)} corruptions and 2 optimized entry points rejected.')


if __name__=='__main__':main()
