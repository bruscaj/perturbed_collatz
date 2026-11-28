#!/usr/bin/env python3
"""Hostile optimization controls; source mode is not semantic proof assurance.
Full mode first requires the positive Linux FULL15 replay/comparator/six-checker
pipeline. Fixtures never modify production files. No Python assert is a gate.
"""
from pathlib import Path
import argparse
import gzip
import hashlib
import importlib.util
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from fractions import Fraction

HERE = Path(__file__).resolve().parent
TARGETS = ('ExternalO3OptimizationChallenge.genericStrictCycleCriterion', 'ExternalO3OptimizationChallenge.genericElementaryReduction', 'ExternalO3OptimizationChallenge.genericDeletionOptimum', 'ExternalO3OptimizationChallenge.vertexEncodingAndExtension', 'ExternalO3OptimizationChallenge.edgeEncodingAndWeights', 'ExternalO3OptimizationChallenge.naturalCycleSigns', 'ExternalO3OptimizationChallenge.commonDyadicDenominator', 'ExternalO3OptimizationChallenge.numeratorMinimumWellPosed', 'ExternalO3OptimizationChallenge.finiteOptimizationExact', 'ExternalO3OptimizationChallenge.truncationMassIdentity', 'ExternalO3OptimizationChallenge.discardedMassBound', 'ExternalO3OptimizationChallenge.literalInfimumSandwich', 'ExternalO3OptimizationChallenge.diagonalConvergence', 'ExternalO3OptimizationChallenge.computableExactOptimizer', 'ExternalO3OptimizationChallenge.computableDyadicApproximation')
SPEC_PINS = {'Definitions.lean': 'cf29376721942a78328491cd910690497f95d381711f0d2e758998fbba9374bc', 'ExpectedTypes.lean': '5ce898eb70690f6f77e26a95cbafb5ef268fa93617ab7418a0b25f6878c34968', 'GeneralDefinitions.lean': '9d3f21078449309feb93e42b2d2b5fc8c5f0c48c4ff42ac7b62fc5d911c2decc', 'GeneralExpectedTypes.lean': '65087d9a25b910c2875c128d9c477cab9b5e506629d446f5db193450dad3b8fa', 'RateDefinitions.lean': 'c377f507d249658b9b53b04c6b2c0906ec95dbdeb1f37291d104b7c07f73eb8d', 'RateExpectedTypes.lean': 'd0089dc07e0599ad8d128291c58518a3a704b20571f735924364ea1b9a3032cc', 'OptimizationDefinitions.lean': '92ebe27ca1f036295fe9b1135e81b50c59069fd928710373a6dce492c4905d98', 'OptimizationExpectedTypes.lean': '74a34cb349cbe43130e6644c919c9a8987930612b9f4b75fa6763763e384e020', 'OptimizationAlgorithmTypes.lean': 'ad8c15d56c4847c12679df09c5b7594d057840fdd567615bfd60a805b3afa752', 'OptimizationChallenge.lean': '280d24ad070c2dcb929a0cdaa4176eae07242b4ecab652492c238f5f640553af'}
OWNED = ('Definitions', 'ExpectedTypes', 'Arithmetic', 'PopulationWeights', 'Progressions', 'Cylinders', 'ExitCylinders', 'Gains', 'CountablePartition', 'PartitionGeneral', 'DensityBounds', 'SourceDensity', 'GeneralDefinitions', 'GeneralExpectedTypes', 'GeneralArithmetic', 'GeneralCompatibility', 'GeneralPreimage', 'GeneralStrideWords', 'GeneralBlockWords', 'GeneralCylinderDensity', 'GeneralRefinementLabels', 'GeneralWeights', 'GeneralMarginal', 'GeneralProjection', 'GeneralGains', 'GeneralSourceDensity', 'GeneralDensity', 'GeneralSolution', 'RateDefinitions', 'RateExpectedTypes', 'RateInfimum', 'OptimizationDefinitions', 'OptimizationExpectedTypes', 'OptimizationAlgorithmTypes', 'OptimizationCycles', 'OptimizationEncoding', 'OptimizationArithmetic', 'OptimizationPaths', 'OptimizationDeletion', 'OptimizationMass', 'OptimizationDensity', 'OptimizationCode', 'OptimizationVertexCode', 'OptimizationEdgeCode', 'OptimizationAlgorithm', 'OptimizationCycleCode', 'OptimizationAccuracy', 'OptimizationJoin', 'OptimizationSolution')
RAW_PIN = '3919bf5adbbc70b07552f06d3479616bf828c8fa5c2a11f9135031de6fa86c8b'
CHECKERS = ('Lean default', 'Lean paranoid', 'lean4lean', 'nanoda', 'con-leche', 'con-ron')
REQUIRED = tuple(m+'.lean' for m in OWNED) + ('OptimizationChallenge.lean', 'Audit.lean',
    'verify.py', 'inventory.json', 'specification.json', 'owned_modules.json',
    'comparator.json', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain',
    'frozen_propositions.json', 'cache-imports.txt', 'test_mutations.py')
PROGRAM_ANCHOR = 'decide (3 ^ (k + 1) < 2 ^ wordHalvings p (k + 1) q)'
PROGRAM_MUTANT = 'decide (2 ^ (k + 1) < 2 ^ wordHalvings p (k + 1) q)'

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
    require(len(actual) == 15 and set(actual) == set(TARGETS), label+' target coverage mismatch')

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
    config = read_json(root/'comparator.json')
    exact_targets(config['theorem_names'], 'configured')
    require(config['challenge_module'] == 'OptimizationChallenge' and config['solution_module'] == 'OptimizationSolution', 'comparator module mismatch')
    require(set(config['permitted_axioms']) == {'propext', 'Quot.sound', 'Classical.choice'}, 'axiom whitelist mismatch')
    require(tuple(read_json(root/'owned_modules.json')) == OWNED, 'owned module coverage mismatch')
    inventory = read_json(root/'inventory.json')
    exact_targets(inventory['targets'], 'inventory')
    require(tuple(inventory['owned_modules']) == OWNED, 'inventory owned module coverage mismatch')
    require('test_mutations.py' in inventory['sources_sha256'], 'negative-control script missing from source inventory')
    expected = inventory if reference is None else reference
    require(inventory['sources_sha256'] == expected['sources_sha256'], 'original source inventory changed')
    require(inventory['targets'] == expected['targets'], 'inventory statement coverage changed')
    require(inventory['helpers'] == expected['helpers'], 'inventory helper coverage changed')
    require(len(inventory['helpers']) == 937 and len(set(names(inventory['helpers']))) == 937, 'inventory helper coverage mismatch')
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
    pattern = (r'(?m)^theorem computableExactOptimizer : ComputableExactOptimizer :=\n'
               r'  ExternalO3OptimizationJoin\.computable_exact_optimizer$')
    path = root/'OptimizationSolution.lean'
    value, count = re.subn(pattern, 'theorem computableExactOptimizer : '+statement+' := '+proof, path.read_text())
    require(count == 1, 'complete A01 wrapper mutation anchor missing')
    path.write_text(value)

def finite_witnesses():
    # A literal h=1,M=2,J=2 graph: asc1:1->0 K1; exit2:0->0 K2;
    # exit3:0->1 K2. The positive two-cycle has 3^2>2^3.
    edges = {1: (1, 0, 1, 4), 2: (0, 0, 2, 2), 3: (0, 1, 2, 1)}
    def optimum(base):
        best = 7
        for mask in range(16):
            safe = True
            for n in (1, 2):
                for q in range(4**n):
                    word = [(q//4**i)%4 for i in range(n)]
                    if all(e in edges and not ((mask//2**e)%2) for e in word) and all(
                        edges[word[i]][1] == edges[word[(i+1)%n]][0] for i in range(n)):
                        if not base**n < 2**sum(edges[e][2] for e in word):
                            safe = False
            if safe:
                best = min(best, sum(row[3] for e, row in edges.items() if (mask//2**e)%2))
        return best
    require(optimum(3) == 1 and optimum(2) == 0, 'exact executable small-graph witness changed')
    require(3**2 > 2**3 and 3 < 2**2, 'cycle/loop power witness changed')
    # Generic zero-gain loop: corrected gain is always0. Non-strict failure
    # costs1, whereas the altered strict-failure observable costs0.
    potential = Fraction(7, 3)
    loop_gain = Fraction(0) + potential - potential
    nonstrict_cost = Fraction(1) if 0 <= loop_gain else Fraction(0)
    strict_cost = Fraction(1) if 0 < loop_gain else Fraction(0)
    require(loop_gain == 0 and nonstrict_cost == 1 and strict_cost == 0 and not loop_gain < 0, 'zero-loop equality witness changed')
    require(Fraction(1, 2**(2+2)) == Fraction(1, 16), 'dyadic denominator witness changed')
    require(Fraction(1, 2**3) != Fraction(1, 2**4), 'parallel label weights collapsed')
    # h1 M2 J3: IDs2 and4 share source/target0, but K2/K3 and masses differ.
    parallel = []
    for code in (2, 4):
        tag, vertex = divmod(code, 2)
        K = tag + 1
        source = 2 * (vertex % 2**0)
        mass = Fraction(1, 2**(K + vertex + 1))
        parallel.append({'id': code, 'source': source, 'target': vertex, 'K': K, 'weight': str(mass)})
    require(parallel[0]['source'] == parallel[1]['source'] == 0 and parallel[0]['target'] == parallel[1]['target'] == 0 and parallel[0]['K'] != parallel[1]['K'] and parallel[0]['weight'] != parallel[1]['weight'], 'parallel label decoder witness changed')
    return {'h1_M2_J2': {'optimum_units': 1, 'denominator': 16, 'q': '1/16',
                'corrupt_base_two_units': 0, 'positive_cycle_ids': [1, 3], 'cycle_comparison': '9 > 8',
                'negative_loop_id': 2, 'loop_comparison': '3 < 4'},
            'generic_zero_gain_loop': {'strict_failure_cost': '0', 'literal_nonstrict_failure_cost': '1',
                'safe_without_deletion': False, 'empty_walk_is_cycle': False},
            'parallel_exit_labels_h1_M2_J3': parallel,
            'omitted_exit_destination': {'h': 1, 'M': 2, 'K': 2, 'destination': [3], 'retained': False,
                'dropping_last_destination_check_retains_it': True},
            'offsets': {'input': [0, 0, 0], 'h_M_J': [1, 2, 2], 'accuracy_h0_b': [0, 0], 'accuracy_M_J': [3, 3]},
            'scope': 'exact finite witnesses only; no universal proof or comparator acceptance'}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--mode', choices=('source', 'full'), default='full')
    for name in ('toolchain', 'mathlib-cache', 'dependency-cache', 'report'):
        parser.add_argument('--'+name, type=Path)
    args = parser.parse_args()
    report = {'scope': 'all15 required finite optimization and total computable approximation targets',
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
        log_root = args.report.resolve().parent/(args.report.stem+'-logs') if args.report else Path(tempfile.mkdtemp(prefix='optimization-negative-logs-'))
        log_root.mkdir(parents=True, exist_ok=True)
        report['logs_directory'] = str(log_root)
        with tempfile.TemporaryDirectory(prefix='optimization-negative-controls-') as temporary:
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
                if reject is None:
                    require(result.returncode == 0, 'positive prerequisite failed: '+label+'; '+str(packed))
                else:
                    code, reason = reject
                    require(result.returncode == code, 'wrong rejection exit: '+label+'; '+str(packed))
                    require(reason(text), 'wrong rejection reason: '+label+'; '+str(packed))
                    row['rejection_reason_confirmed'] = True
                return text
            prepare = None
            if args.mode == 'full':
                require(sys.platform.startswith('linux'), 'full controls require Linux sandbox support; not executed')
                require(lake is not None, 'lake unavailable; full controls not executed')
                spec = importlib.util.spec_from_file_location('trusted_optimization_positive_verifier', HERE/'verify.py')
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
                run(positive, 'positive full fifteen-target pipeline', command)
                receipt = read_json(receipt_path)
                require(receipt.get('mode') == 'full' and receipt.get('status') == 'passed optimization full assurance gates', 'FULL15 positive sentinel absent')
                exact_targets(receipt['targets'], 'positive full receipt')
                require(len(receipt.get('helpers', [])) == 937, 'positive full all-origin helper coverage missing')
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
            change('equality failures excluded', 'GeneralDefinitions.lean',
                   'def Bad (h : Depth) (φ : Correction h) (e : Edge h) : Prop := 0 ≤ gain h φ e',
                   'def Bad (h : Depth) (φ : Correction h) (e : Edge h) : Prop := 0 < gain h φ e')
            change('strict feasibility weakened', 'OptimizationDefinitions.lean',
                   'g.baseGain e + ψ (g.target e) - ψ (g.source e) < 0', 'g.baseGain e + ψ (g.target e) - ψ (g.source e) ≤ 0')
            change('zero-length walks admitted as cycles', 'OptimizationDefinitions.lean',
                   '0 < c.length ∧', '0 ≤ c.length ∧')
            change('parallel exit K labels collapsed', 'OptimizationDefinitions.lean',
                   '| .inr (k, _) => k.val + 2', '| .inr (_k, _) => 2')
            change('dyadic weights doubled', 'OptimizationDefinitions.lean',
                   '1 / ((2 : ℕ) ^ weightExponent h M J e : ℚ)',
                   '2 / ((2 : ℕ) ^ weightExponent h M J e : ℚ)')
            change('last exit destination omitted from truncation', 'OptimizationDefinitions.lean',
                   'k + 2 ≤ J ∧ ∀ i, positiveWindow h b i ≤ M',
                   'k + 2 ≤ J ∧ ∀ i, i.val + 1 < h.val → positiveWindow h b i ≤ M')
            change('A01 base offset changed', 'OptimizationAlgorithmTypes.lean',
                   '(m0 + 2) (j0 + 2)', '(m0 + 1) (j0 + 2)')
            change('A02 accuracy cap offset changed', 'OptimizationAlgorithmTypes.lean',
                   'let M := h.val + b + 2', 'let M := h.val + b + 1')
            change('executable cycle base three changed to two', 'OptimizationCode.lean', PROGRAM_ANCHOR, PROGRAM_MUTANT, frozen=False)
            source_rejection('required cycle transport module dropped', lambda root: (root/'OptimizationCycleCode.lean').unlink(), 'missing required module/config: OptimizationCycleCode.lean')
            def drop_row(root, file, field):
                path = root/file; data = read_json(path); data[field] = data[field][:-1]; path.write_text(json.dumps(data, indent=2)+'\n')
            source_rejection('configured A02 target skipped', lambda root: drop_row(root, 'comparator.json', 'theorem_names'), 'configured target coverage mismatch')
            source_rejection('inventory target skipped', lambda root: drop_row(root, 'inventory.json', 'targets'), 'inventory target coverage mismatch')
            source_rejection('inventory helper skipped', lambda root: drop_row(root, 'inventory.json', 'helpers'), 'inventory helper coverage changed')
            def drop_raw(root):
                path = root/'frozen_propositions.json'; data = read_json(path)
                require(len(data) == 16, 'original raw register must retain15 required plus optional entry'); path.write_text(json.dumps(data[1:], indent=2)+'\n')
            source_rejection('frozen proposition skipped', drop_raw, 'original frozen proposition digest mismatch')
            def drop_owned(root):
                path = root/'owned_modules.json'; path.write_text(json.dumps(read_json(path)[:-1], indent=2)+'\n')
            source_rejection('owned module register skipped', drop_owned, 'owned module coverage mismatch')
            if args.mode == 'full':
                wrong = fixture('wrong-A01-statement'); prepare(wrong)
                wrapper(wrong, 'True', 'by trivial')
                run(wrong, 'wrong-statement positive compilation', [lake, 'build'])
                expected = "Challenge and solution theorem statement do not match: 'ExternalO3OptimizationChallenge.computableExactOptimizer'"
                run(wrong, 'wrong statement rejected by actual comparator', [lake, 'comparator', '--config', 'comparator.json', '--paranoid'], (1, lambda text: expected in text))
                report['controls'].append({'name': 'A01 wrapper weakened to True', 'gate': 'actual trusted elaborated statement comparator', 'result': 'rejected', 'mutated_solution_sha256': digest(wrong/'OptimizationSolution.lean')})
                shutil.rmtree(wrong)
                axiom = fixture('hidden-imported-custom-axiom'); prepare(axiom)
                (axiom/'BadPremise.lean').write_text('import OptimizationAlgorithmTypes\nnamespace BadPremise\naxiom hiddenOptimizer : ExternalO3OptimizationDraft.ComputableExactOptimizer\nend BadPremise\n')
                with (axiom/'lakefile.toml').open('a') as out:
                    out.write('\n[[lean_lib]]\nname = "BadPremise"\n')
                wrapper(axiom, 'ComputableExactOptimizer', 'BadPremise.hiddenOptimizer')
                solution = axiom/'OptimizationSolution.lean'; solution.write_text('import BadPremise\n'+solution.read_text())
                run(axiom, 'custom-axiom positive compilation', [lake, 'build'])
                run(axiom, 'hidden imported axiom rejected by complete audit', [lake, 'env', 'lean', '-DwarningAsError=true', 'Audit.lean'],
                    (1, lambda text: 'forbidden axiom' in text.lower() and 'BadPremise.hiddenOptimizer' in text))
                report['controls'].append({'name': 'hidden imported custom axiom', 'gate': 'actual all-origin transitive closure audit', 'result': 'rejected', 'mutated_solution_sha256': digest(solution), 'hidden_premise_sha256': digest(axiom/'BadPremise.lean')})
                shutil.rmtree(axiom)
                program = fixture('corrupt-executable-cycle-base'); prepare(program)
                run(program, 'production program prerequisite imports', [lake, 'build', 'OptimizationAlgorithmTypes'])
                original = (program/'OptimizationCode.lean').read_text()
                require(original.count(PROGRAM_ANCHOR) == 1, 'production program mutation anchor changed')
                proof = '\nexample : ExternalO3OptimizationCode.optimizer (0, 0, 0) = 1 := by decide\n'
                positive = program/'ProgramPositive.lean'; positive.write_text(original+proof)
                run(program, 'positive literal production optimizer proof', [lake, 'env', 'lean', '-DwarningAsError=true', '-R', str(program), str(positive)])
                corrupt = program/'ProgramCorrupt.lean'; corrupt.write_text(original.replace(PROGRAM_ANCHOR, PROGRAM_MUTANT, 1)+proof)
                run(program, 'corrupt executable cycle base rejected by Lean kernel proof', [lake, 'env', 'lean', '-DwarningAsError=true', '-R', str(program), str(corrupt)],
                    (1, lambda text: 'Tactic `decide` proved that the proposition' in text and 'ExternalO3OptimizationCode.optimizer' in text and 'is false' in text))
                report['controls'].append({'name': 'production executable cycle base three changed to two', 'gate': 'actual Lean decidable evaluation of production optimizer', 'result': 'rejected', 'positive_source_sha256': digest(positive), 'corrupt_source_sha256': digest(corrupt), 'exact_witness': 'original optimizer(0,0,0)=1; corrupt=0; positive two-cycle9>8'})
                shutil.rmtree(program)
                report['status'] = 'passed optimization negative controls and positive full fifteen-target pipeline'
            else:
                report['status'] = 'partial: portable original-source/hash/coverage controls passed'
                report['not_executed'] = ['positive FULL15 pipeline', 'actual trusted statement comparator rejection', 'actual custom-axiom closure rejection', 'actual corrupted executable Lean proof rejection', 'source-bound imported-proof replay', 'six independent checker coverage']
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
