"""Pressure-support source controls and real semantic hostile fixtures.

Source mode is explicitly partial. Full mode requires a fresh positive full
pipeline, trusted comparator rejection, transitive-axiom rejection and an actual
copied production-operation corruption. No sandbox fallback is accepted.
"""
import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

import verify

HERE = Path(__file__).resolve().parent


def need(ok, message):
    if not ok:
        raise ValueError(message)


def read(path):
    return json.loads(path.read_text())


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def replace_once(path, old, new):
    text = path.read_text()
    need(text.count(old) == 1 and old != new, 'invalid/no-op source mutation')
    path.write_text(text.replace(old, new, 1))


def change_json(root, name, mutation):
    path = root / name
    value = read(path)
    mutation(value)
    write(path, value)


def replace_first_wrapper(root, proposition, proof):
    path = root / 'PressureSolution.lean'
    text = path.read_text()
    pattern = r'theorem word_zeroVolumeConvention\s*:.*?(?=\n\ntheorem|\nend)'
    text, count = re.subn(pattern, 'theorem word_zeroVolumeConvention : ' + proposition + ' :=\n  ' + proof,
                          text, count=1, flags=re.S)
    need(count == 1, 'missing actual first target wrapper')
    path.write_text(text)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--mode', choices=('source', 'full'), default='full')
    parser.add_argument('--toolchain', type=Path)
    parser.add_argument('--dependency-cache', type=Path)
    parser.add_argument('--mathlib-cache', type=Path)
    parser.add_argument('--report', type=Path, required=True)
    args = parser.parse_args()
    args.report.parent.mkdir(parents=True, exist_ok=True)
    logs = args.report.parent / (args.report.stem + '-logs')
    logs.mkdir(exist_ok=False)
    report = {'mode': args.mode, 'status': 'running', 'controls': [], 'commands': [],
              'scope': '64finite WORD/analytic helpers only; no full canonical48/headline result'}

    def save():
        write(args.report, report)

    try:
        verify.source_gate(HERE)
        inventory = read(HERE / 'inventory.json')
        report['original_source_sha256'] = inventory['sources_sha256']
        report['source_inventory_sha256'] = digest(HERE / 'inventory.json')
        report['required_targets'] = list(verify.TARGETS)
        with tempfile.TemporaryDirectory(prefix='pressure-hostile-') as temporary:
            base = Path(temporary)

            def fixture(name):
                root = base / name
                root.mkdir()
                for filename in inventory['sources_sha256']:
                    shutil.copyfile(HERE / filename, root / filename)
                shutil.copyfile(HERE / 'inventory.json', root / 'inventory.json')
                return root

            cases = [
                ('owned module deleted', lambda r: change_json(r, 'owned_modules.json', lambda v: v.pop())),
                ('target deleted', lambda r: change_json(r, 'inventory.json', lambda v: v['targets'].pop())),
                ('target duplicated', lambda r: change_json(r, 'inventory.json', lambda v: v['targets'].append(v['targets'][0]))),
                ('helper deleted', lambda r: change_json(r, 'inventory.json', lambda v: v['helpers'].pop())),
                ('helper duplicated', lambda r: change_json(r, 'inventory.json', lambda v: v['helpers'].append(v['helpers'][0]))),
                ('helper origin forged', lambda r: change_json(r, 'inventory.json', lambda v: v['helpers'][0].update(module='Unowned'))),
                ('model deleted', lambda r: change_json(r, 'inventory.json', lambda v: v['models'].pop())),
                ('raw proposition deleted', lambda r: change_json(r, 'frozen_propositions.json', lambda v: v.pop())),
                ('raw model value forged', lambda r: change_json(r, 'frozen_models.json', lambda v: v[0].update(raw_value='forged'))),
                ('comparator target deleted', lambda r: change_json(r, 'comparator.json', lambda v: v['theorem_names'].pop())),
                ('custom axiom permitted', lambda r: change_json(r, 'comparator.json', lambda v: v['permitted_axioms'].append('BadPremise.hiddenWord'))),
                ('checker omitted', lambda r: change_json(r, 'comparator.json', lambda v: v.update(external_kernels={}))),
                ('production concatenation corrupted', lambda r: replace_once(r / 'PressureWordDefinitions.lean', 'else v ⟨i.val-m,by omega⟩', 'else v ⟨i.val-m,by omega⟩ + 1')),
                ('provenance coverage omitted', lambda r: change_json(r, 'inventory.json', lambda v: v['sources_sha256'].pop('provenance.json'))),
                ('inventory model value forged', lambda r: change_json(r, 'inventory.json', lambda v: v['models'][0].update(raw_value='forged'))),
                ('inventory model origin forged', lambda r: change_json(r, 'inventory.json', lambda v: v['models'][0].update(module='Unowned'))),
                ('target mapping coverage omitted', lambda r: change_json(r, 'inventory.json', lambda v: v['sources_sha256'].pop('target_map.json'))),
                ('legacy metadata coverage omitted', lambda r: change_json(r, 'inventory.json', lambda v: v['sources_sha256'].pop('word_legacy_model_metadata.json'))),
                ('source file omitted', lambda r: (r / 'PressureSolution.lean').unlink()),
            ]
            for label, mutation in cases:
                root = fixture('source-' + str(len(report['controls'])))
                before = {p.name: digest(p) for p in root.iterdir() if p.is_file()}
                mutation(root)
                after = {p.name: digest(p) for p in root.iterdir() if p.is_file()}
                need(before != after, 'no-op hostile control: ' + label)
                try:
                    verify.source_gate(root)
                except (ValueError, KeyError, OSError) as error:
                    report['controls'].append({'name': label, 'gate': 'immutable source/hash/coverage',
                                               'result': 'rejected', 'reason': str(error)})
                else:
                    raise ValueError('source mutation accepted: ' + label)
                save()
            need(len(report['controls']) == 19, 'source control coverage')
            if args.mode == 'source':
                report['status'] = 'partial: nineteen source/hash/coverage controls only'
                report['missing_gates'] = ['positive full replay/comparator/checkers',
                                           'actual semantic comparator/axiom/operation controls']
                print(report['status'])
                return
            need(sys.platform.startswith('linux'), 'full controls require Linux sandbox support; not executed')
            env = dict(os.environ)
            for key in ('LEAN_PATH', 'LEAN_SRC_PATH', 'PYTHONOPTIMIZE'):
                env.pop(key, None)
            if args.toolchain:
                env['PATH'] = str(args.toolchain.resolve() / 'bin') + os.pathsep + env.get('PATH', '')
            lake = shutil.which('lake', path=env.get('PATH'))
            need(lake is not None, 'lake unavailable')

            def run(root, label, command, reject=False, needles=(), snapshots=()):
                p = subprocess.run(list(map(str, command)), cwd=root, env=env, capture_output=True, text=True)
                raw = (p.stdout + p.stderr).encode()
                path = logs / (str(len(report['commands'])).zfill(3) + '-' + label + '.log.gz')
                path.write_bytes(gzip.compress(raw, mtime=0))
                row = {'label': label, 'command': list(map(str, command)), 'exit_code': p.returncode,
                       'expected_failure': reject, 'log_gzip': str(path),
                       'log_sha256': hashlib.sha256(raw).hexdigest(), 'compressed_sha256': digest(path),
                       'fixture_sources': []}
                for name in snapshots:
                    src = root / name
                    dst = logs / (path.stem + '.fixture.' + name + '.gz')
                    dst.write_bytes(gzip.compress(src.read_bytes(), mtime=0))
                    row['fixture_sources'].append({'name': name, 'gzip': str(dst),
                        'source_sha256': digest(src), 'gzip_sha256': digest(dst)})
                report['commands'].append(row)
                save()
                if reject:
                    text = raw.decode()
                    need(p.returncode != 0 and all(n in text for n in needles), 'wrong rejection: ' + label)
                    need('bubblewrap' not in text.lower() and 'sandbox' not in text.lower(), 'sandbox failure is not semantic rejection')
                    row['rejection_reason_confirmed'] = True
                else:
                    need(p.returncode == 0, 'positive prerequisite failed: ' + label)
                save()
                return p.stdout

            options = []
            for flag, value in [('--toolchain', args.toolchain), ('--dependency-cache', args.dependency_cache),
                                ('--mathlib-cache', args.mathlib_cache)]:
                if value:
                    options += [flag, str(value.resolve())]
            positive_report = logs / 'positive-full.json'
            run(HERE, 'positive-full', [sys.executable, HERE / 'verify.py', '--mode', 'full',
                                       '--report', positive_report, *options])
            positive = read(positive_report)
            need(positive['status'] == 'passed pressure full assurance gates', 'positive full pipeline not passed')
            expected = {k: list(verify.CHECKERS) for k in ('complete proof closure', 'frozen statement comparison')}
            need(positive.get('checker_coverage') == expected, 'positive full six-mode coverage differs')
            compressed = logs / 'positive-full.json.gz'
            compressed.write_bytes(gzip.compress(positive_report.read_bytes(), mtime=0))
            report['positive_full_report_gzip'] = str(compressed)
            report['positive_full_report_sha256'] = digest(positive_report)

            def prepare(root):
                verify.prepare_dependencies(root, dependency_cache=args.dependency_cache,
                                            mathlib_cache=args.mathlib_cache)

            wrong = fixture('wrong-statement')
            prepare(wrong)
            replace_first_wrapper(wrong, 'True', 'True.intro')
            run(wrong, 'wrong-wrapper-build', [lake, 'build'])
            run(wrong, 'wrong-wrapper-comparator', [lake, 'comparator', '--config', 'comparator.json', '--paranoid'],
                reject=True, needles=('do not match',), snapshots=('PressureSolution.lean', 'PressureChallenge.lean'))
            report['controls'].append({'name': 'zero-volume wrapper weakened to True',
                                      'gate': 'actual trusted statement comparator', 'result': 'rejected'})

            hidden = fixture('hidden-axiom')
            prepare(hidden)
            (hidden / 'BadPremise.lean').write_text('import PressureWordExpectedTypes\nnamespace BadPremise\naxiom hiddenWord : ExternalBridgePressureWordDraft.ZeroVolumeConvention\nend BadPremise\n')
            with (hidden / 'lakefile.toml').open('a') as stream:
                stream.write('\n[[lean_lib]]\nname = "BadPremise"\n')
            replace_first_wrapper(hidden, 'ExternalBridgePressureWordDraft.ZeroVolumeConvention', 'BadPremise.hiddenWord')
            path = hidden / 'PressureSolution.lean'
            path.write_text('import BadPremise\n' + path.read_text())
            run(hidden, 'hidden-axiom-build', [lake, 'build'])
            run(hidden, 'hidden-axiom-audit', [lake, 'env', 'lean', '-DwarningAsError=true', 'Audit.lean'],
                reject=True, needles=('Forbidden axiom BadPremise.hiddenWord', 'ExternalBridgePressureSupportChallenge.word_zeroVolumeConvention'),
                snapshots=('PressureSolution.lean', 'BadPremise.lean'))
            report['controls'].append({'name': 'hidden imported zero-volume axiom',
                                      'gate': 'actual all-origin transitive axiom audit', 'result': 'rejected'})

            operation = fixture('corrupt-literal-concatenation')
            prepare(operation)
            run(operation, 'literal-operation-prerequisite-build', [lake, 'build'])
            production = (operation / 'PressureWordDefinitions.lean').read_text()
            found = re.search(r'^def concatenate .*?(?=\n\nend)', production, re.M | re.S)
            need(found is not None, 'missing literal production operation')
            prefix = 'import PressureWordDefinitions\nnamespace ActualConcatFixture\nopen ExternalFiniteBridgeDraft ExternalBridgePressureDraft ExternalBridgePressureWordDraft\nnoncomputable section\n'
            suffix = '\nexample : concatenate 1 1 (fun _ => 1) (fun _ => 2) ⟨1, by omega⟩ = 2 := by norm_num [concatenate]\nend\nend ActualConcatFixture\n'
            good = prefix + found.group() + suffix
            anchor = 'else v ⟨i.val-m,by omega⟩'
            need(good.count(anchor) == 1, 'operation corruption location not unique')
            bad = good.replace(anchor, anchor+' + 1', 1)
            (operation / 'ConcatPositive.lean').write_text(good)
            (operation / 'ConcatCorrupt.lean').write_text(bad)
            run(operation, 'literal-concat-positive', [lake, 'env', 'lean', '-DwarningAsError=true', 'ConcatPositive.lean'],
                snapshots=('ConcatPositive.lean',))
            run(operation, 'literal-concat-corrupt', [lake, 'env', 'lean', '-DwarningAsError=true', 'ConcatCorrupt.lean'],
                reject=True, needles=('unsolved goals',), snapshots=('ConcatCorrupt.lean',))
            report['controls'].append({'name': 'literal production concatenation increments second-block letters',
                                      'gate': 'actual literal production-operation proposition', 'result': 'rejected'})
            need(len(report['controls']) == 22 and all(c['result'] == 'rejected' for c in report['controls']), 'full control coverage')
            verify.source_gate(HERE)
            report['status'] = 'passed pressure semantic controls and positive full sixty-four-target pipeline'
    except Exception as error:
        report.update(status='failed', error=str(error))
        raise
    finally:
        save()
    print(report['status'])


if __name__ == '__main__':
    main()
