"""Regenerate all exact geometry data and compare the committed certificate."""

if not __debug__:
    raise SystemExit('Geometry certificates require assertions enabled; do not use -O.')

import argparse
import copy
import json
from pathlib import Path
import subprocess
import sys

import attracting_disks
import discrete
import integer_disks
import phase_trace
import separator
from rational import certified_pi, interval_strings, require

HERE = Path(__file__).resolve().parent


def canonical(data):
    """Retain JSON types: in particular true, 1, and 1.0 are different."""
    return json.dumps(data,sort_keys=True,separators=(',',':'),
                      ensure_ascii=False,allow_nan=False)


def strict_json(text):
    def pairs(items):
        result = {}
        for key,value in items:
            if key in result:
                raise ValueError(f'duplicate JSON key: {key}')
            result[key] = value
        return result

    def reject_number(token):
        # Proof rationals are strings; numeric JSON tokens are integers only.
        raise ValueError(f'noninteger or nonfinite JSON number: {token}')

    return json.loads(text,object_pairs_hook=pairs,parse_float=reject_number,
                      parse_constant=reject_number)


def compare_saved(text,expected):
    require(canonical(strict_json(text)) == canonical(expected),
            'saved geometry certificate differs from exact regeneration')


def mutation_tests(expected):
    """Negative tests reuse one regeneration; no numerical resampling."""
    cases = []

    def changed(name,path,value=None,remove=False):
        data = copy.deepcopy(expected)
        container = data
        for key in path[:-1]:
            container = container[key]
        if remove:
            del container[path[-1]]
        else:
            container[path[-1]] = value
        cases.append((name,json.dumps(data)))

    changed('enlarged_integer_capture_radius',('integer_disks','cycles',0,'capture_radius'),'1/10')
    changed('false_integer_remainder_bound',('integer_disks','used_remainder_coefficient'),0)
    changed('altered_cycle_multiplier',('integer_disks','cycles',1,'multiplier'),'0')
    changed('omitted_attracting_disk',('attracting_disks','cycles',0,'disks',4),remove=True)
    changed('omitted_derivative_bound',('attracting_disks','cycles',1,'disks',0,'derivative_upper'),remove=True)
    changed('omitted_interval_leaf',('real_separator','zones',0,'leaves',2),remove=True)
    changed('altered_root_bracket',('real_separator','nonzero_fixed_returns',0,'bracket',0),'0')
    changed('omitted_trace_point',('phase_launches','launches',0,'trajectory_balls',7),remove=True)
    changed('false_zero_trace_error',('phase_launches','launches',0,'trajectory_balls',7,'radius'),'0')
    changed('wrong_trace_phase',('phase_launches','launches',0,'trajectory_balls',7,'phase'),2)
    changed('wrong_entry_time',('phase_launches','launches',0,'first_target_disk_entry'),42)
    changed('wrong_model',('model',),'absorbing zero')
    changed('omitted_section',('phase_launches',),remove=True)
    changed('empty_disk_list',('attracting_disks','cycles'),[])
    changed('boolean_for_integer',('schema_version',),True)
    changed('float_for_integer',('schema_version',),1.0)
    changed('wrong_integer_cycle_phase',('discrete_cycles','cycles',0,'states',0,1),1)
    changed('altered_pi_enclosure',('pi_interval',0),'0')
    changed('unexpected_field',('unverified_extra_claim',),True)
    cases.extend((('empty_object','{}'),('empty_list','[]'),
                  ('duplicate_key','{"schema_version":1,'+canonical(expected)[1:]),
                  ('nonfinite_nan','{"schema_version":NaN}'),
                  ('nonfinite_infinity','{"schema_version":Infinity}'),
                  ('overflowing_float','{"schema_version":1e999}')))
    rejected = []
    for name,text in cases:
        try:
            compare_saved(text,expected)
        except (ArithmeticError,ValueError,TypeError):
            rejected.append(name)
        else:
            raise ArithmeticError(f'mutated certificate was accepted: {name}')
    return rejected


def regenerate():
    return {
        'schema_version':1,
        'model':'C(z)=z+1/4-(z/2+1/4)*cos(pi*z), forcing (+1,0,-1), continued zero',
        'arithmetic':'Exact Python integers and fractions; no floating-point proof inequalities',
        'pi_interval':interval_strings(certified_pi()),
        'discrete_cycles':discrete.certify(),
        'integer_disks':integer_disks.certify(),
        'attracting_disks':attracting_disks.certify(),
        'real_separator':separator.certify(),
        'phase_launches':phase_trace.certify(),
        'scope':'Five certified attracting cycles; no exhaustive smooth attractor or global basin census.'
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write',action='store_true',help='write regenerated certificate.json')
    parser.add_argument('--output',type=Path,help='write a concise verification report')
    args = parser.parse_args()
    data = regenerate()
    destination = HERE/'certificate.json'
    if args.write:
        destination.write_text(json.dumps(data,indent=2,allow_nan=False)+'\n')
    else:
        compare_saved(destination.read_text(),data)
    mutations = mutation_tests(data)
    safeguards = []
    for file in sorted(HERE.glob('*.py')):
        run = subprocess.run([sys.executable,'-O','-B',str(file)],capture_output=True,text=True)
        require(run.returncode != 0 and 'do not use -O' in run.stderr+run.stdout,
                f'optimization safeguard missing in {file.name}')
        safeguards.append(file.name)
    report = {'status':'passed','exact_regeneration':True,'saved_certificate_compared':not args.write,
              'integer_cycles':3,'noninteger_cycles':2,
              'real_interval_leaf_counts':data['real_separator']['leaf_counts'],
              'phase_target_disk_entry_times':[r['first_target_disk_entry'] for r in data['phase_launches']['launches']],
              'strict_json_comparison':True,'mutation_rejection_count':len(mutations),
              'mutation_rejections':mutations,
              'optimization_rejections':safeguards,
              'formalized_in_lean':False,'exhaustive_global_attractor_census':False}
    if args.output:
        args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__ == '__main__':
    main()
