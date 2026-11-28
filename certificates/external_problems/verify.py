"""Replay exact finite external-problem evidence and integrity checks."""
import hashlib
import gzip
import io
import zipfile
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


# This exception to the former blanket draft-only guard is backed by the fresh
# source/conclusion release review and the exact historical b5 CI artifacts.
O3_STATUS = 'machine-checked algorithmic answer for the stated run-length-only class'
O3_HEADLINES = ['ExternalO3OptimizationChallenge.computableDyadicApproximation',
                'ExternalO3RateChallenge.infimumTendsToZero',
                'ExternalO3RateChallenge.explicitInverseDepthRate']
CHECKERS = ['Lean default', 'Lean paranoid', 'lean4lean', 'nanoda', 'con-leche', 'con-ron']
B5_COMMIT = 'b5dcda3404b14b43e1985c2e31219ce811e46881'
B5_TREE = '76ee312e9f756a0dceba6ea3d900dd81b7858168'
CI_SHA256 = 'e031b754b5a815e6673ed30fcf65e51cb3823899558536745760684810118d35'
SOURCE_PINS_SHA256 = 'ad1563749726dbb057352855b728a1eddcfbac68e7c5c4a3502b7b2da66126b3'
SOURCE_CLASS = {
    'information': 'current remaining block length and next h-1 full block lengths after actual successive block exits',
    'correction': 'arbitrary real function on positive h-tuples; no boundedness, regularity, computability or integrability restriction',
    'failure': 'comparison at the next Syracuse stride; equality is failure',
    'population': 'relative natural density among positive odd initial seeds, for each fixed depth and correction before taking the depth limit',
    'conventions': 'fixed point1 retained; zero outside source domain; exit valuations integrated out and not correction inputs'}

ALGORITHMIC_ANSWER = {'brackets': 'For every h>=1,b>=0, a total computable program returns A; M=J=h+b+2 and q=A/2^(J+h*M) satisfy q<=p_h<=q+2^(-b).', 'limit': 'p_h tends to0 as h tends to infinity', 'rate': '127/(32768*h)<=p_h<=5/(2*h), hence Theta(1/h)', 'scope': 'The infimum is over actual achieved seed densities for all arbitrary real run-window corrections, not an assumed symbolic surrogate.'}
REVIEW_QUALIFICATIONS = {'independent_human_review': False, 'novelty_certified': False, 'source_author_endorsement': False, 'ai_role_implementation_overlap': True}
O3_CHECKER_DESCRIPTION = 'Both complete proof-closure replay and frozen-statement comparison passed Lean default, Lean paranoid, lean4lean, nanoda, con-leche and con-ron; optimization18 hostile controls passed after a fresh full positive pipeline.'


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def validate_ci_metadata(ci):
    require((ci['source_commit'], ci['source_tree'], ci['run_id']) ==
            (B5_COMMIT, B5_TREE, 46111672437), 'O3 historical source/run mismatch')
    require(ci['all_seven_jobs'] == 'passed', 'O3 seven-job coverage missing')
    require((ci['optimization_targets'], ci['optimization_own_reused_theorem_closures'],
             ci['optimization_owned_modules'], ci['optimization_source_files']) == (15, 952, 49, 63),
            'O3 optimization declaration/source coverage mismatch')
    require(ci['checker_coverage'] == {k: CHECKERS for k in
            ['complete proof closure', 'frozen statement comparison']}, 'O3 six-checker coverage missing')
    require(ci['hostile_controls'] == 18, 'O3 eighteen-control coverage missing')
    require(len(ci['source_pins']) == 63 and sha256(json.dumps(ci['source_pins'], sort_keys=True,
            separators=(',', ':')).encode()) == SOURCE_PINS_SHA256, 'O3 historical63 source pins mismatch')
    require(ci['legacy_checks'] == 43 and ci['all63_files_matched_checked_snapshot_before_documentation_update'] is True,
            'O3 historical regression/source cross-check missing')
    require(ci['positive_full_pipeline_rerun'] == 'passed with all15/952/six modes in both stages',
            'O3 positive full pipeline rerun missing')
    require((ci['export_bytes'], ci['export_sha256']) == (103158206,
        '1bb90a10488f0a22e713b19b2a2d2e2fd728ce33f6101fd950b54901aa9ea01c'), 'O3 proof export pin mismatch')
    require(len(ci['actual_semantic_rejections']) == 3 and all(
        x['exit_code'] == 1 and x['actual_reason_present'] is True for x in ci['actual_semantic_rejections']),
        'O3 semantic rejection evidence missing')


def validate_full_report(report, status, targets=None, closures=None, modules=None):
    require(report['mode'] == 'full' and report['status'] == status, 'O3 full report did not pass')
    require(report['steps'] and all(s['exit_code'] == 0 for s in report['steps']), 'O3 positive gate failure')
    stages = [s for s in report['steps'] if 'replay' in s['label'] or
              ('frozen' in s['label'] and ('comparison' in s['label'] or 'statements' in s['label']))]
    require(len(stages) == 2 and all(all(f'{c} kernel accepts the solution' in s.get('stdout', '')
            for c in CHECKERS) for s in stages), 'O3 actual six-mode replay/comparator acceptance missing')
    if 'checker_coverage' in report:
        require(report['checker_coverage'] == {k: CHECKERS for k in
            ['complete proof closure', 'frozen statement comparison']}, 'O3 report checker coverage mismatch')
    if targets is not None:
        require(len(report['targets']) == targets and len({r['declaration'] for r in report['targets']}) == targets,
                'O3 report target declaration mismatch')
        rows = report['targets'] + report['helpers']
        require(len(rows) == closures and len({r['declaration'] for r in rows}) == closures and
                report['own_theorem_count'] == closures and report['own_module_count'] == modules,
                'O3 report complete closure coverage mismatch')
        require(all(set(r['axioms']) <= {'propext', 'Quot.sound', 'Classical.choice'} for r in rows),
                'O3 report axiom policy mismatch')
        export = next(s for s in report['steps'] if 'export' in s['label'])
        require(set(export['roots']) == {r['declaration'] for r in rows} and len(export['roots']) == closures,
                'O3 exported declaration coverage mismatch')


def validate_o3_assurance(root):
    directory = root/'verification/external_optimization'
    data = (directory/'CI_ARTIFACTS.json').read_bytes()
    require(sha256(data) == CI_SHA256, 'O3 historical CI receipt digest mismatch; fresh release audit required')
    ci = json.loads(data)
    validate_ci_metadata(ci)
    specifications = {
        'external-analysis-h1.zip': ('external-analysis.json', 'passed h1 full assurance gates', 14, 397, 24, 'external-analysis-source-tree.txt'),
        'external-population.zip': ('external-population.json', 'passed population full assurance gates', 22, 517, 28, 'external-population-source-tree.txt'),
        'external-rate.zip': ('external-rate.json', 'passed rate full assurance gates', 11, 765, 45, 'external-rate-source-tree.txt'),
        'external-bridge.zip': ('external-bridge.json', 'passed bridge full assurance gates', 25, 357, 22, 'external-bridge-source-tree.txt'),
        'external-optimization.zip': ('external-optimization.json', 'passed optimization full assurance gates', 15, 952, 49, 'external-optimization-source-tree.txt'),
        'external-support.zip': ('external-support.json', 'passed supporting full assurance gates', None, None, None, 'external-source-tree.txt')}
    require(len(ci['archives']) == 7 and {x['local_archive'] for x in ci['archives']} ==
            set(specifications) | {'release-verification.zip'}, 'O3 seven archive coverage mismatch')
    reports = {}
    for item in ci['archives']:
        name = item['local_archive']
        archive = directory/'ci_artifacts'/name
        blob = archive.read_bytes()
        require(len(blob) == item['bytes'] and sha256(blob) == item['zip_sha256'],
                'O3 historical archive digest mismatch: '+name)
        with zipfile.ZipFile(io.BytesIO(blob)) as z:
            if name == 'release-verification.zip':
                legacy = json.loads(z.read('verification.json'))
                require(legacy['status'] == 'passed' and legacy['mode'] == 'all' and
                        len(legacy['checks']) == 43 and all(s['exit_code'] == 0 for s in legacy['checks']),
                        'O3 legacy job did not pass all43 checks')
                continue
            report_name, status, nt, nc, nm, tree_name = specifications[name]
            require(z.read(tree_name).decode().splitlines()[:2] == [B5_COMMIT, B5_TREE],
                    'O3 archive source/tree mismatch: '+name)
            report = json.loads(z.read(report_name))
            validate_full_report(report, status, nt, nc, nm)
            reports[name] = report
            if name == 'external-optimization.zip':
                export = next(s for s in report['steps'] if 'export' in s['label'])
                require(export['source_sha256'] == ci['source_pins'] and export['bytes'] == ci['export_bytes'] and
                        export['sha256'] == ci['export_sha256'], 'O3 source-bound export mismatch')
                mutations = json.loads(z.read('external-optimization-mutations.json'))
                require(mutations['mode'] == 'full' and mutations['status'] ==
                    'passed optimization negative controls and positive full fifteen-target pipeline' and
                    len(mutations['controls']) == 18 and all(c['result'] == 'rejected' for c in mutations['controls']) and
                    mutations['original_source_sha256'] == ci['source_pins'], 'O3 actual eighteen-control report mismatch')
                positive_data = gzip.decompress(z.read('external-optimization-mutations-logs/positive-full.json.gz'))
                require(sha256(positive_data) == mutations['positive_full_report_sha256'], 'O3 rerun report hash mismatch')
                positive = json.loads(positive_data)
                validate_full_report(positive, status, 15, 952, 49)
                require(next(s for s in positive['steps'] if 'export' in s['label'])['source_sha256'] == ci['source_pins'],
                        'O3 positive rerun source pins mismatch')
                for rejection in ci['actual_semantic_rejections']:
                    row = next(c for c in mutations['commands'] if c['label'] == rejection['label'])
                    log = gzip.decompress(z.read('external-optimization-mutations-logs/'+Path(row['log_gzip']).name))
                    require(row['exit_code'] == 1 and row['expected_failure'] is True and
                            row['rejection_reason_confirmed'] is True and sha256(log) == row['log_sha256'] == rejection['log_sha256'],
                            'O3 actual semantic rejection log mismatch')
    optimization_names = {r['declaration'] for r in reports['external-optimization.zip']['targets']}
    rate_names = {r['declaration'] for r in reports['external-rate.zip']['targets']}
    require(O3_HEADLINES[0] in optimization_names and set(O3_HEADLINES[1:]) <= rate_names,
            'O3 headline declaration not in checked reports')
    # Documentation may have changed since b5; proof/model source drift cannot
    # silently inherit that historical assurance. Preserve all63 original pins.
    for name, project in [('external-optimization.zip', 'external_optimization'), ('external-rate.zip', 'external_rate')]:
        export = next(s for s in reports[name]['steps'] if 'export' in s['label'])
        for filename, pin in export['source_sha256'].items():
            if filename.endswith('.lean'):
                require(sha256((root/'lean'/project/filename).read_bytes()) == pin,
                        'O3 checked proof/model source drift: '+project+'/'+filename)


def validate_status(register, root=ROOT):
    require(len(register['claims']) == 4 and {c['problem'] for c in register['claims']} ==
            {'M4', 'R8', 'R9', 'O3′'}, 'incomplete four-problem register')
    require(register['source_commit'] == '5840497a23fc0d64127b850aea68862d7c93f2b7', 'primary source pin changed')
    ids = {'M4': 'EXT-M4', 'R8': 'EXT-R8', 'R9': 'EXT-R9', 'O3′': 'EXT-O3PRIME'}
    require(all(c['id'] == ids[c['problem']] for c in register['claims']), 'problem/claim identity changed')
    for claim in register['claims']:
        if claim['problem'] != 'O3′':
            require(claim['headline_formal_declarations'] == [] and claim['status'] == 'draft candidate' and
                    claim['headline_checker_coverage'] == 'none', 'analytic headline changed; fresh release audit required')
            foundation = claim['finite_bridge_foundation']
            require((foundation['targets'], foundation['closures'], foundation['source_commit']) == (25, 357, B5_COMMIT) and
                    foundation['source_tree'] == B5_TREE and foundation['analytic_headline_proved'] is False and
                    foundation['assurance'] == 'full machine gates passed at the historical b5 snapshot; no analytic headline theorem', 'finite bridge foundation scope/assurance mismatch')
            if claim['problem'] == 'M4':
                extension = claim['unrestricted_fixed_reference_c1_extension']
                require((extension['targets'], extension['closures']) == (23, 504) and
                        extension['status'] == 'source/type/axiom checked; independent gates pending' and
                        extension['intended_m4_solved'] is False, 'separate c1 extension scope/assurance mismatch')
            continue
        require(claim['status'] == O3_STATUS and claim['headline_formal_declarations'] == O3_HEADLINES,
                'O3 headline status/declaration mismatch; fresh release audit required')
        require(claim['source_class'] == SOURCE_CLASS, 'O3 source information class changed')
        require(claim['algorithmic_answer'] == ALGORITHMIC_ANSWER, 'O3 algorithmic answer scope/bounds changed')
        require(claim['review_qualifications'] == REVIEW_QUALIFICATIONS, 'O3 review/novelty qualification changed')
        require(claim['headline_checker_coverage'] == O3_CHECKER_DESCRIPTION, 'O3 headline checker description changed')
        assurance = claim['headline_assurance']
        require((assurance['source_commit'], assurance['source_tree'], assurance['run_id']) ==
                (B5_COMMIT, B5_TREE, 46111672437) and assurance['receipt'] == 'verification/external_optimization/CI_ARTIFACTS.json' and
                assurance['finite_checker_alone_proves_infinite_theorem'] is False,
                'O3 assurance source or finite/infinite distinction changed')
    validate_o3_assurance(root)


def main():
    output = {}
    for name in ("bridge", "o3"):
        command = [sys.executable, str(HERE / f"{name}.py")]
        normal = subprocess.run(command, check=True, capture_output=True, text=True)
        optimized = subprocess.run([command[0], "-O", command[1]], check=True,
                                   capture_output=True, text=True)
        actual = json.loads(normal.stdout)
        if actual != json.loads(optimized.stdout):
            raise ValueError(f"{name}: optimized behavior differs")
        expected = json.loads((HERE / f"{name}.json").read_text())
        if actual != expected:
            raise ValueError(f"{name}: committed finite evidence differs")
        output[name] = actual
    project = ROOT / "lean/external_problems"
    freeze = json.loads((project / "freeze.json").read_text())
    for name in ("Definitions.lean", "ExpectedTypes.lean", "Challenge.lean"):
        data = (project / name).read_bytes()
        pin = freeze["files"][name]
        if len(data) != pin["bytes"] or hashlib.sha256(data).hexdigest() != pin["sha256"]:
            raise ValueError(f"frozen supporting statement changed: {name}")
    register = json.loads((ROOT / "papers/external_problems/status.json").read_text())
    validate_status(register)
    output["frozen_supporting_spec_hashes"] = "match"
    output["limits"] = "This finite-checker report certifies no infinite theorem, novelty or human review; the separate analytic package has its own source-pinned assurance receipts."
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
