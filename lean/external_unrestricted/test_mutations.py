#!/usr/bin/env python3
"""Hostile all-length fixed-reference count controls; source mode is not semantic proof assurance.
Full mode first requires the positive Linux FULL23 replay/comparator/six-checker
pipeline. Fixtures never modify production files. No Python assert is a gate.
"""
from pathlib import Path
import argparse
import gzip
import hashlib
import importlib.util
import itertools
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from fractions import Fraction

HERE = Path(__file__).resolve().parent
TARGETS = ('ExternalM4UnrestrictedChallenge.slopeBounds', 'ExternalM4UnrestrictedChallenge.tripleRotationHighLow', 'ExternalM4UnrestrictedChallenge.highPhaseCountLower', 'ExternalM4UnrestrictedChallenge.largeDefectsUnbounded', 'ExternalM4UnrestrictedChallenge.canonicalPrefixLaw', 'ExternalM4UnrestrictedChallenge.canonicalAllLengthWord', 'ExternalM4UnrestrictedChallenge.canonicalAlphabetAndSites', 'ExternalM4UnrestrictedChallenge.manyDisjointCanonicalSites', 'ExternalM4UnrestrictedChallenge.swapPrefixLaw', 'ExternalM4UnrestrictedChallenge.swapPreservesSource', 'ExternalM4UnrestrictedChallenge.swapFamilyInjective', 'ExternalM4UnrestrictedChallenge.swapCubeCard', 'ExternalM4UnrestrictedChallenge.swapRewardIdentity', 'ExternalM4UnrestrictedChallenge.canonicalRewardBudget', 'ExternalM4UnrestrictedChallenge.canonicalSwapLossBound', 'ExternalM4UnrestrictedChallenge.largeDefectWitnessInjection', 'ExternalM4UnrestrictedChallenge.exponentialCountLower', 'ExternalM4UnrestrictedChallenge.rungCountOne', 'ExternalM4UnrestrictedChallenge.allLengthCountBounds', 'ExternalM4UnrestrictedChallenge.normalizedLogBounds', 'ExternalM4UnrestrictedChallenge.normalizedLogLiminf', 'ExternalM4UnrestrictedChallenge.normalizedLogLimsup', 'ExternalM4UnrestrictedChallenge.noAllLengthLimit')
SPEC_PINS = {'Definitions.lean': 'cf29376721942a78328491cd910690497f95d381711f0d2e758998fbba9374bc', 'ExpectedTypes.lean': '5ce898eb70690f6f77e26a95cbafb5ef268fa93617ab7418a0b25f6878c34968', 'PrefixDefinitions.lean': 'd7b5cd8b624dae007e3c3dc7f3620260dbfcf2169d0211b0859e18ed58180069', 'BridgeDefinitions.lean': '7a36ebc1e9ff89fcec7ad1fdae1c2d5ae9ee011b06ae110fd4f34999e7df19a7', 'BridgeExpectedTypes.lean': '850dcdd0d75479edaeab1c8d6d336b9099f56511e0b6f5a5125bedfca05838aa', 'UnrestrictedDefinitions.lean': 'b22796b599134a98ebcf10002bac7e46d9a463d0e983099353ad524312ac5307', 'UnrestrictedExpectedTypes.lean': '4ce322ba8fcd87a5bdf18244c55df92b27b05a293eab201aa15ee8fa24146670', 'UnrestrictedChallenge.lean': '639af946ad44a5696e625e41276144cc2267cc370fd62c98291af04cbbb99a4e'}
OWNED = ('Definitions', 'ExpectedTypes', 'Arithmetic', 'PopulationWeights', 'DepthOneSeries', 'LogRatioIrrational', 'PositiveCeilReturns', 'PrefixDefinitions', 'RungDefinitions', 'RungTransfer', 'SyracuseSlope', 'BridgeDefinitions', 'BridgeExpectedTypes', 'BridgeArithmetic', 'BridgeEncoding', 'BridgeRungs', 'BridgeRewards', 'BridgeTransport', 'BridgeFinite', 'BridgeExtremal', 'BridgeBoundary', 'BridgeSolution', 'UnrestrictedDefinitions', 'UnrestrictedExpectedTypes', 'UnrestrictedCounts', 'UnrestrictedCountBound', 'UnrestrictedRotation', 'UnrestrictedSwaps', 'UnrestrictedCanonical', 'UnrestrictedInjection', 'UnrestrictedLimits', 'UnrestrictedSolution')
RAW_PIN = '35d68ca025ccd4e4ac5488e3d0fff432b86c9814be375d7950ab06587f036bca'
MODEL_PIN = '2289d1102f9780189687d7cc0e1f31a100c60a3baccfc9e6daa74f440b603541'
HELPER_COUNT = 481  # Actual public audit: 23 roots +481 helpers =504 closures in32 modules.
CHECKERS = ('Lean default', 'Lean paranoid', 'lean4lean', 'nanoda', 'con-leche', 'con-ron')
REQUIRED = tuple(m+'.lean' for m in OWNED) + ('UnrestrictedChallenge.lean', 'Audit.lean',
    'verify.py', 'inventory.json', 'specification.json', 'owned_modules.json',
    'comparator.json', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain',
    'frozen_propositions.json', 'frozen_models.json', 'cache-imports.txt', 'test_mutations.py', 'README.md', 'ARGUMENT.md')
SWAP_ANCHOR = 'fun i => if i ∈ S then 1 else if ∃ j ∈ S, j.val + 1 = i.val then 2 else w i'
SWAP_MUTANT = 'fun i => if i ∈ S then 2 else if ∃ j ∈ S, j.val + 1 = i.val then 2 else w i'
SWAP_PROOF = """
example : ExternalM4UnrestrictedDraft.applySwaps 2
    (fun i : Fin 2 => if i.val = 0 then 2 else 1) {(0 : Fin 2)} =
    (fun i : Fin 2 => if i.val = 0 then 1 else 2) := by
  funext i
  fin_cases i <;> norm_num [ExternalM4UnrestrictedDraft.applySwaps]
"""

def require(ok, message):
    if not ok:
        raise ValueError(message)

def read_json(path):
    return json.loads(path.read_text())

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def names(rows):
    return tuple(rows) if isinstance(rows, dict) else tuple(r if isinstance(r, str) else r['declaration'] for r in rows)

def exact_targets(rows, label):
    actual = names(rows)
    require(len(actual) == 23 and set(actual) == set(TARGETS), label+' target coverage mismatch')

def source_gate(root, reference=None):
    for name in REQUIRED:
        require((root/name).is_file(), 'missing required module/config: '+name)
    require((root/'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.35.0', 'toolchain pin mismatch')
    spec = read_json(root/'specification.json')
    require(spec['mathlib_commit'] == '56a005855ea17e0b0958f73ec801ae140b0a1679', 'mathlib pin mismatch')
    require(set(spec['files']) == set(SPEC_PINS), 'trusted specification file coverage mismatch')
    for name, pin in SPEC_PINS.items():
        require(spec['files'][name]['sha256'] == pin, 'trusted specification pin changed: '+name)
        require(digest(root/name) == pin, 'original frozen source digest mismatch: '+name)
        require(spec['files'][name]['bytes'] == (root/name).stat().st_size, 'frozen source size mismatch')
    exact_targets(spec['challenge_holes'], 'specification')
    require(spec['frozen_propositions_sha256'] == RAW_PIN, 'trusted raw proposition pin changed')
    require(digest(root/'frozen_propositions.json') == RAW_PIN, 'original frozen proposition digest mismatch')
    require(spec['frozen_model_definitions_sha256'] == MODEL_PIN and spec['frozen_model_count'] == 13, 'trusted model register changed')
    require(digest(root/'frozen_models.json') == MODEL_PIN, 'original frozen model digest mismatch')
    require(len(read_json(root/'frozen_models.json')) == 13, 'frozen model coverage mismatch')
    config = read_json(root/'comparator.json')
    exact_targets(config['theorem_names'], 'configured')
    require(config['challenge_module'] == 'UnrestrictedChallenge' and config['solution_module'] == 'UnrestrictedSolution', 'comparator module mismatch')
    require(set(config['permitted_axioms']) == {'propext', 'Quot.sound', 'Classical.choice'}, 'axiom whitelist mismatch')
    require(tuple(read_json(root/'owned_modules.json')) == OWNED, 'owned module coverage mismatch')
    inventory = read_json(root/'inventory.json')
    exact_targets(inventory['targets'], 'inventory')
    require(tuple(inventory['owned_modules']) == OWNED, 'inventory owned module coverage mismatch')
    require('test_mutations.py' in inventory['sources_sha256'], 'negative-control script missing from source inventory')
    require(set(REQUIRED)-{'inventory.json'} <= set(inventory['sources_sha256']), 'source inventory coverage mismatch')
    require({p.name for p in root.glob('*.lean')} == {m+'.lean' for m in OWNED} | {'UnrestrictedChallenge.lean','Audit.lean'}, 'owned Lean module coverage mismatch')
    expected = inventory if reference is None else reference
    require(inventory['sources_sha256'] == expected['sources_sha256'], 'original source inventory changed')
    require(inventory['targets'] == expected['targets'], 'inventory statement coverage changed')
    require(inventory['helpers'] == expected['helpers'], 'inventory helper coverage changed')
    require(inventory['models'] == expected['models'], 'inventory model coverage changed')
    require(len(inventory['models']) == 13 and sorted(inventory['models'],key=lambda x:x['declaration']) == sorted(read_json(root/'frozen_models.json'),key=lambda x:x['declaration']), 'inventory model coverage mismatch')
    require(len(inventory['helpers']) == HELPER_COUNT and len(set(names(inventory['helpers']))) == HELPER_COUNT, 'inventory helper coverage mismatch')
    for name, pin in expected['sources_sha256'].items():
        path = Path(name)
        require(not path.is_absolute() and '..' not in path.parts, 'unsafe source path')
        require((root/path).is_file() and not (root/path).is_symlink(), 'missing inventoried source: '+name)
        require(digest(root/path) == pin, 'original source inventory digest mismatch: '+name)
    return inventory

def replace_once(path, old, new):
    value = path.read_text()
    require(value.count(old) == 1, 'nonunique mutation anchor: '+path.name)
    path.write_text(value.replace(old, new, 1))

def wrapper(root, statement, proof):
    pattern = (r'(?m)^theorem exponentialCountLower : ExponentialCountLower :=\n'
               r'  ExternalM4UnrestrictedInjection\.exponential_count_lower$')
    path = root/'UnrestrictedSolution.lean'
    value, count = re.subn(pattern, 'theorem exponentialCountLower : '+statement+' := '+proof, path.read_text())
    require(count == 1, 'complete exponentialCountLower wrapper anchor missing')
    path.write_text(value)

def finite_witnesses():
    def prefixes(w):
        p = [0]
        for k in w: p.append(p[-1]+k)
        return p
    def reward(w):
        return sum((Fraction(2**k,3**t) for t,k in enumerate(prefixes(w)[:-1])),Fraction())
    def swap(w,s):
        return tuple(1 if i in s else 2 if i-1 in s else x for i,x in enumerate(w))
    require(swap((2,1),{0}) == (1,2), 'production21 witness changed')
    require(swap((2,1),set()) == (2,1) and swap((),set()) == (), 'empty subset/domain witness changed')
    require(swap((2,1,2,1),{0,2}) == (1,2,1,2), 'adjacent disjoint pair witness changed')
    require(prefixes(swap((2,1),{0})) == [0,1,3], 'intermediate-prefix/closing witness changed')
    require(reward((2,1))-reward((1,2)) == Fraction(2,3), 'literal half-term loss witness changed')
    # At r2 the actual cap is C1=2, closing sum4. Its only positive words are13,22.
    # These exact tiny powers certify floor(theta)=1 and ceil(2theta)=4, cap1=2.
    require(2 < 3 < 4 and 8 < 9 < 16, 'actual slope small-power witnesses changed')
    def floor_theta(t):
        return (3**t).bit_length()-1
    def ceil_theta(t):
        return floor_theta(t)+int(t>0)
    def all_source_words(r):
        if r == 0:
            return ()  # Actual SourceWord has the explicit 0<r conjunct.
        closing = ceil_theta(r)
        cap = [closing-ceil_theta(r-t) for t in range(r)]
        return tuple(w for w in itertools.product(range(1,closing+1),repeat=r)
                     if sum(w)==closing and all(k<=c for k,c in zip(prefixes(w)[:-1],cap)))
    words=all_source_words(2)
    B=sum((Fraction(2**floor_theta(t),3**t) for t in range(2)),Fraction())
    adapted=sum((Fraction(2**(ceil_theta(2)-ceil_theta(2-t)),3**t) for t in range(2)),Fraction())
    require(words==((1,3),(2,2)) and B==Fraction(5,3) and adapted==Fraction(7,3), 'exact literal r2 model witness changed')
    require(all_source_words(0)==() and all_source_words(1)==((2,),), 'empty and boundary literal source witnesses changed')
    require(sum(reward(w)>=B for w in words)==2, 'fixed-reference count witness changed')
    require(sum(reward(w)>=adapted for w in words)==1, 'adapted-reference count witness changed')
    require(sum(reward(w)>B for w in words)==1, 'weak threshold equality witness changed')
    return {'swap21':{'original':[2,1],'selected':[0],'output':[1,2],
             'prefixes':[0,1,3],'literal_loss':'2/3','corrupted_selected_start_output':[2,2]},
            'empty_subset':{'input':[2,1],'output':[2,1]},
            'empty_length':{'word':[],'source_count':0,'reason':'original SourceWord requires positive length'},
            'length_one':{'only_source_word':[2],'reference':'1','reward':'1','count':1},
            'adjacent_disjoint_pairs':{'input':[2,1,2,1],'sites':[0,2],'output':[1,2,1,2]},
            'length_two_reference_distinction':{'source_words':[[1,3],[2,2]],'fixed_B':'5/3',
             'phase_adapted_reference':'7/3','fixed_count':2,'adapted_count':1,'strict_threshold_count':1},
            'scope':'Separate finite exact diagnostics only; not unboundedness, limits, model equivalence, or universal proof assurance.'}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--mode', choices=('source', 'full'), default='full')
    for name in ('toolchain', 'mathlib-cache', 'dependency-cache', 'report'):
        parser.add_argument('--'+name, type=Path)
    args = parser.parse_args()
    report = {'scope': 'all23 required actual-slope all-length fixed-reference count targets',
              'mode': args.mode, 'status': 'running', 'controls': [], 'commands': []}
    env = dict(os.environ)
    for key in ('LEAN_PATH', 'LEAN_SRC_PATH', 'PYTHONOPTIMIZE'):
        env.pop(key, None)
    if args.toolchain:
        env['PATH'] = str(args.toolchain.resolve()/'bin')+os.pathsep+env.get('PATH', '')
    env['MATHLIB_NO_CACHE_ON_UPDATE'] = '1'
    lake = shutil.which('lake', path=env.get('PATH'))
    try:
        reference = source_gate(HERE)
        report['source_inventory_sha256'] = digest(HERE/'inventory.json')
        report['original_source_sha256'] = reference['sources_sha256']
        report['original_frozen_pins'] = SPEC_PINS
        report['required_targets'] = TARGETS
        report['finite_model_witnesses'] = finite_witnesses()
        log_root = args.report.resolve().parent/(args.report.stem+'-logs') if args.report else Path(tempfile.mkdtemp(prefix='unrestricted-negative-logs-'))
        log_root.mkdir(parents=True, exist_ok=True)
        report['logs_directory'] = str(log_root)
        with tempfile.TemporaryDirectory(prefix='unrestricted-negative-controls-') as temporary:
            base = Path(temporary)
            def fixture(label):
                root = base/label
                shutil.copytree(HERE, root, ignore=shutil.ignore_patterns('.lake', '*.olean', '*.ilean', '__pycache__', '*.log', '*.gz'))
                source_gate(root, reference)
                return root
            def run(root, label, command, reject=None):
                path = log_root/(f"{len(report['commands']):03d}-"+re.sub('[^a-z0-9]+', '-', label.lower())+'.log')
                with path.open('w') as out:
                    result = subprocess.run(command, cwd=root, env=env, stdout=out, stderr=subprocess.STDOUT, text=True)
                data = path.read_bytes(); text = data.decode(errors='replace'); packed = path.with_suffix('.log.gz')
                with gzip.open(packed, 'wb') as out:
                    out.write(data)
                path.unlink()
                row = {'label': label, 'command': command, 'exit_code': result.returncode,
                       'log_gzip': str(packed), 'log_sha256': hashlib.sha256(data).hexdigest(),
                       'compressed_sha256': digest(packed), 'expected_failure': reject is not None}
                report['commands'].append(row)
                if result.returncode != 0:
                    snapshots = []
                    for filename in ('UnrestrictedSolution.lean', 'BadPremise.lean',
                                     'UnrestrictedDefinitions.lean', 'SwapPositive.lean', 'SwapCorrupt.lean'):
                        source = root/filename
                        if source.is_file():
                            saved = log_root/(path.stem+'.fixture.'+filename+'.gz')
                            with gzip.open(saved, 'wb') as out:
                                out.write(source.read_bytes())
                            snapshots.append({'name': filename, 'source_sha256': digest(source),
                                              'gzip': str(saved), 'gzip_sha256': digest(saved)})
                    row['fixture_sources'] = snapshots
                if reject is None:
                    require(result.returncode == 0, 'positive prerequisite failed: '+label+'; '+str(packed))
                else:
                    code, reason = reject
                    require(result.returncode == code, 'wrong rejection exit: '+label+'; '+str(packed))
                    require(reason(text), 'wrong rejection reason: '+label+'; '+str(packed))
                    for fatal in ('maximum recursion depth', 'maximum number of heartbeats',
                                  'out of memory', 'std::bad_alloc', 'segmentation fault',
                                  'no space left on device', 'unknown module prefix'):
                        require(fatal not in text.lower(), 'resource/import failure cannot count as rejection: '+label)
                    row['rejection_reason_confirmed'] = True
                return text
            prepare = None
            if args.mode == 'full':
                require(sys.platform.startswith('linux'), 'full controls require Linux sandbox support; not executed')
                require(lake is not None, 'lake unavailable; full controls not executed')
                spec = importlib.util.spec_from_file_location('trusted_unrestricted_positive_verifier', HERE/'verify.py')
                require(spec is not None and spec.loader is not None, 'trusted verifier unavailable')
                verifier = importlib.util.module_from_spec(spec); sys.modules[spec.name] = verifier; spec.loader.exec_module(verifier)
                def prepare(root):
                    verifier.prepare_dependencies(root, dependency_cache=args.dependency_cache, mathlib_cache=args.mathlib_cache)
                positive = fixture('positive-full'); receipt_path = log_root/'positive-full.json'
                command = [sys.executable, str(positive/'verify.py'), '--mode', 'full', '--report', str(receipt_path)]
                command += ['--mathlib-cache', str(args.mathlib_cache.resolve())] if args.mathlib_cache else [
                    '--dependency-cache', str((args.dependency_cache or HERE/'.lake/packages').resolve())]
                if args.toolchain:
                    command += ['--toolchain', str(args.toolchain.resolve())]
                run(positive, 'positive full twenty-three-target pipeline', command)
                receipt = read_json(receipt_path)
                require(receipt.get('mode') == 'full' and receipt.get('status') == 'passed unrestricted full assurance gates', 'FULL23 positive sentinel absent')
                exact_targets(receipt['targets'], 'positive full receipt')
                require(len(receipt.get('helpers', [])) == HELPER_COUNT and receipt['helpers'] == reference['helpers'], 'positive full all-origin helper coverage missing')
                require(receipt['targets'] == reference['targets'], 'positive full exact target metadata coverage missing')
                require(receipt.get('own_theorem_count') == HELPER_COUNT + 23 and receipt.get('own_module_count') == 32, 'positive full owned closure/module coverage missing')
                require(len(receipt.get('models', [])) == 13 and sorted(receipt['models'],key=lambda x:x['declaration']) == reference['models'], 'positive full thirteen frozen model coverage missing')
                for label in ('complete proof closure', 'frozen statement comparison'):
                    require(receipt.get('checker_coverage', {}).get(label) == list(CHECKERS), 'positive full six-checker coverage missing: '+label)
                packed = receipt_path.with_suffix('.json.gz')
                with gzip.open(packed, 'wb') as out:
                    out.write(receipt_path.read_bytes())
                report['positive_full_report_gzip'] = str(packed); report['positive_full_report_sha256'] = digest(receipt_path)
                receipt_path.unlink(); shutil.rmtree(positive)
            def source_rejection(label, mutate, expected):
                root = fixture(label); mutate(root)
                try:
                    source_gate(root, reference)
                except ValueError as error:
                    require(expected in str(error), 'wrong source rejection reason: '+label+': '+str(error))
                    report['controls'].append({'name': label, 'gate': 'original immutable source/hash/coverage', 'result': 'rejected', 'reason': str(error)})
                else:
                    raise ValueError('source mutation accepted: '+label)
                shutil.rmtree(root)
            def change(label, file, old, new, frozen=True):
                expected = ('original frozen source digest mismatch: ' if frozen else 'original source inventory digest mismatch: ')+file
                source_rejection(label, lambda root: replace_once(root/file, old, new), expected)
            change('fixed reference replaced by phase adapted threshold', 'UnrestrictedDefinitions.lean',
                   'sourceCount r (phaseZeroReference slope r)', 'sourceCount r (literalReference slope r)')
            change('closing ceil replaced by floor', 'BridgeDefinitions.lean',
                   'wordPrefix r w (Fin.last r) = Int.ceil ((r : ℝ) * θ) ∧',
                   'wordPrefix r w (Fin.last r) = Int.floor ((r : ℝ) * θ) ∧')
            change('zero letters admitted', 'BridgeDefinitions.lean',
                   'def PositiveWord (r : ℕ) (w : Word r) : Prop := ∀ i, 1 ≤ w i',
                   'def PositiveWord (r : ℕ) (w : Word r) : Prop := ∀ i, 0 ≤ w i')
            change('selected swap start stays two', 'UnrestrictedDefinitions.lean', SWAP_ANCHOR, SWAP_MUTANT)
            change('intermediate prefix index shifted', 'UnrestrictedExpectedTypes.lean',
                   '(if ∃ i ∈ S, i.val + 1 = t.val then (1 : ℤ) else 0)',
                   '(if ∃ i ∈ S, i.val = t.val then (1 : ℤ) else 0)')
            change('equality threshold witnesses excluded', 'BridgeDefinitions.lean',
                   'Nat.card {w : Word r // SourceWord slope r w ∧ q ≤ reward r w}',
                   'Nat.card {w : Word r // SourceWord slope r w ∧ q < reward r w}')
            change('base ten normalization changed', 'UnrestrictedDefinitions.lean',
                   '(Real.log (count r : ℝ) / Real.log 10) / (r : ℝ)',
                   '(Real.log (count r : ℝ) / Real.log 2) / (r : ℝ)')
            change('subset injection dropped from witness', 'UnrestrictedExpectedTypes.lean',
                   'Function.Injective (swapFamily r (canonicalWord r) S) ∧',
                   'True ∧')
            change('rung count replaced by unconditional all length count', 'UnrestrictedExpectedTypes.lean',
                   'StrictRung slope r → count r = 1', 'count r = 1')
            change('limsup lower constant weakened', 'UnrestrictedExpectedTypes.lean',
                   '(Real.log 2 / Real.log 10) / 8 ≤ Filter.limsup normalizedLogCount atTop',
                   '0 ≤ Filter.limsup normalizedLogCount atTop')
            source_rejection('required injection module dropped', lambda root: (root/'UnrestrictedInjection.lean').unlink(), 'missing required module/config: UnrestrictedInjection.lean')
            def drop_row(root, file, field):
                path = root/file; data = read_json(path); data[field] = data[field][:-1]; path.write_text(json.dumps(data, indent=2)+'\n')
            source_rejection('configured nonlimit target skipped', lambda root: drop_row(root, 'comparator.json', 'theorem_names'), 'configured target coverage mismatch')
            source_rejection('inventory target skipped', lambda root: drop_row(root, 'inventory.json', 'targets'), 'inventory target coverage mismatch')
            source_rejection('inventory helper skipped', lambda root: drop_row(root, 'inventory.json', 'helpers'), 'inventory helper coverage changed')
            source_rejection('inventory model skipped', lambda root: drop_row(root, 'inventory.json', 'models'), 'inventory model coverage changed')
            def drop_raw(root, filename, count):
                path = root/filename; data = read_json(path)
                require(len(data) == count, 'original raw register coverage mismatch')
                path.write_text(json.dumps(data[1:], indent=2)+'\n')
            source_rejection('frozen proposition skipped', lambda root: drop_raw(root,'frozen_propositions.json',23), 'original frozen proposition digest mismatch')
            source_rejection('frozen model body skipped', lambda root: drop_raw(root,'frozen_models.json',13), 'original frozen model digest mismatch')
            def drop_owned(root):
                path = root/'owned_modules.json'; path.write_text(json.dumps(read_json(path)[:-1], indent=2)+'\n')
            source_rejection('owned module register skipped', drop_owned, 'owned module coverage mismatch')
            if args.mode == 'full':
                wrong = fixture('wrong-count-statement'); prepare(wrong)
                wrapper(wrong, 'True', 'by trivial')
                run(wrong, 'wrong-statement positive compilation', [lake, 'build'])
                expected = "Challenge and solution theorem statement do not match: 'ExternalM4UnrestrictedChallenge.exponentialCountLower'"
                run(wrong, 'wrong statement rejected by actual comparator', [lake, 'comparator', '--config', 'comparator.json', '--paranoid'], (1, lambda text: expected in text))
                report['controls'].append({'name': 'exponential count wrapper weakened to True', 'gate': 'actual trusted elaborated statement comparator', 'result': 'rejected', 'mutated_solution_sha256': digest(wrong/'UnrestrictedSolution.lean')})
                shutil.rmtree(wrong)
                axiom = fixture('hidden-imported-asymptotic-count-axiom'); prepare(axiom)
                (axiom/'BadPremise.lean').write_text('import UnrestrictedExpectedTypes\nnamespace BadPremise\naxiom hiddenPopulation : ExternalM4UnrestrictedDraft.ExponentialCountLower\nend BadPremise\n')
                with (axiom/'lakefile.toml').open('a') as out:
                    out.write('\n[[lean_lib]]\nname = "BadPremise"\n')
                wrapper(axiom, 'ExponentialCountLower', 'BadPremise.hiddenPopulation')
                solution = axiom/'UnrestrictedSolution.lean'; solution.write_text('import BadPremise\n'+solution.read_text())
                run(axiom, 'custom-axiom positive compilation', [lake, 'build'])
                run(axiom, 'hidden imported axiom rejected by complete audit', [lake, 'env', 'lean', '-DwarningAsError=true', 'Audit.lean'],
                    (1, lambda text: 'forbidden axiom' in text.lower() and 'BadPremise.hiddenPopulation' in text))
                report['controls'].append({'name': 'hidden imported population axiom', 'gate': 'actual all-origin transitive closure audit', 'result': 'rejected', 'mutated_solution_sha256': digest(solution), 'hidden_premise_sha256': digest(axiom/'BadPremise.lean')})
                shutil.rmtree(axiom)
                program = fixture('corrupt-production-swap'); prepare(program)
                run(program, 'production swap prerequisite imports', [lake, 'build', 'BridgeExpectedTypes'])
                original = (program/'UnrestrictedDefinitions.lean').read_text()
                require(original.count(SWAP_ANCHOR) == 1, 'production swap mutation anchor changed')
                positive = program/'SwapPositive.lean'; positive.write_text(original+SWAP_PROOF)
                run(program, 'positive literal production swap proof', [lake, 'env', 'lean', '-DwarningAsError=true', '-R', str(program), str(positive)])
                corrupt = program/'SwapCorrupt.lean'; corrupt.write_text(original.replace(SWAP_ANCHOR, SWAP_MUTANT, 1)+SWAP_PROOF)
                run(program, 'corrupt production swap rejected by Lean kernel proof', [lake, 'env', 'lean', '-DwarningAsError=true', '-R', str(program), str(corrupt)],
                    (1, lambda text: str(corrupt) in text and 'error: unsolved goals' in text and 'case «0»' in text and '⊢ False' in text))
                report['controls'].append({'name': 'production selected swap start one changed to two', 'gate': 'actual Lean kernel proof of production21 to12 operation', 'result': 'rejected', 'positive_source_sha256': digest(positive), 'corrupt_source_sha256': digest(corrupt), 'exact_witness': 'original applySwaps21/{0}=12; corrupt output22; same claimed vector equality fails'})
                shutil.rmtree(program)
                report['status'] = 'passed unrestricted negative controls and positive full twenty-three-target pipeline'
            else:
                report['status'] = 'partial: portable original-source/hash/coverage controls passed'
                report['not_executed'] = ['positive FULL23 pipeline including13models and allownedclosures', 'actual trusted statement comparator rejection', 'actual custom-axiom closure rejection', 'actual corrupted production swap Lean proof rejection', 'source-bound imported-proof replay', 'six independent checker coverage']
                report['semantic_note'] = 'Source controls reject immutable source/hash/coverage changes only, not elaborated theorem statements. Exact finite witnesses are separate from universal proofs.'
        source_gate(HERE, reference)
    except Exception as error:
        report['status'] = 'failed'; report['error'] = str(error)
        raise
    finally:
        if args.report:
            args.report.parent.mkdir(parents=True, exist_ok=True)
            args.report.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k: report[k] for k in ('scope', 'mode', 'status', 'controls', 'logs_directory')}))

if __name__ == '__main__':
    main()
