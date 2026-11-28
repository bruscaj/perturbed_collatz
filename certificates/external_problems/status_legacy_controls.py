"""Original31 metadata/receipt controls, with isolated temporary evidence only.
No Lean execution, Git history or private source dependency.
"""

def run(root, evidence_dir):
    """Focused metadata/receipt mutation checks; not Lean proof replay."""
    from pathlib import Path
    import copy,gzip,hashlib,importlib.util,json,subprocess,sys,tempfile,zipfile
    ROOT=Path(root)
    HERE=Path(evidence_dir)
    spec=importlib.util.spec_from_file_location('external_status_guard',ROOT/'certificates/external_problems/verify.py')
    v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
    register=json.loads((ROOT/'papers/external_problems/status.json').read_text())
    ci=json.loads((ROOT/'verification/external_optimization/CI_ARTIFACTS.json').read_text())
    controls=[]
    def rejected(label,action,reason):
     try:action()
     except ValueError as e:
      if reason not in str(e):raise RuntimeError(label+': wrong failure '+str(e))
      controls.append(dict(label=label,result='rejected',reason=str(e)))
     else:raise RuntimeError(label+': mutation accepted')

    def claim_mutation(label,problem,mutate,reason):
     x=copy.deepcopy(register);mutate(next(c for c in x['claims'] if c['problem']==problem))
     rejected(label,lambda:v.validate_status(x),reason)

    def ci_mutation(label,mutate,reason):
     x=copy.deepcopy(ci);mutate(x);rejected(label,lambda:v.validate_ci_metadata(x),reason)

    v.validate_status(register)
    claim_mutation('intended M4 headline upgrade','M4',lambda c:c.update(status=v.O3_STATUS),'analytic headline changed')
    claim_mutation('R8 headline declaration invented','R8',lambda c:c.update(headline_formal_declarations=['Invented.pressure']),'analytic headline changed')
    claim_mutation('R9 headline checker invented','R9',lambda c:c.update(headline_checker_coverage='six modes'),'analytic headline changed')
    claim_mutation('c1 support promoted to intended M4 solution','M4',lambda c:c['unrestricted_fixed_reference_c1_extension'].update(intended_m4_solved=True),'separate c1 extension')
    claim_mutation('c1 independent assurance invented','M4',lambda c:c['unrestricted_fixed_reference_c1_extension'].update(status='all gates passed'),'separate c1 extension')
    claim_mutation('O3 answer relabeled as M4 claim','O3′',lambda c:c.update(id='EXT-M4'),'problem/claim identity changed')
    claim_mutation('O3 fourth headline invented','O3′',lambda c:c['headline_formal_declarations'].append('Invented.closedForm'),'O3 headline status/declaration')
    claim_mutation('O3 A02 omitted','O3′',lambda c:c['headline_formal_declarations'].pop(0),'O3 headline status/declaration')
    claim_mutation('O3 source information enlarged','O3′',lambda c:c['source_class'].update(information='run lengths plus exit valuations'),'O3 source information class')
    claim_mutation('O3 false faster rate','O3′',lambda c:c['algorithmic_answer'].update(rate='p_h<=2^(-h)'),'O3 algorithmic answer')
    claim_mutation('O3 historical source forged','O3′',lambda c:c['headline_assurance'].update(source_commit='0'*40),'O3 assurance source')
    claim_mutation('finite checker claimed as infinite proof','O3′',lambda c:c['headline_assurance'].update(finite_checker_alone_proves_infinite_theorem=True),'O3 assurance source')
    claim_mutation('human acceptance invented','O3′',lambda c:c['review_qualifications'].update(independent_human_review=True),'O3 review/novelty')
    claim_mutation('novelty certified invented','O3′',lambda c:c['review_qualifications'].update(novelty_certified=True),'O3 review/novelty')
    ci_mutation('CI source commit forged',lambda c:c.update(source_commit='0'*40),'historical source/run')
    ci_mutation('one mandatory job missing',lambda c:c.update(all_seven_jobs='six passed'),'seven-job coverage')
    ci_mutation('CI target count reduced',lambda c:c.update(optimization_targets=14),'declaration/source coverage')
    ci_mutation('CI closure count reduced',lambda c:c.update(optimization_own_reused_theorem_closures=951),'declaration/source coverage')
    ci_mutation('CI pin omitted',lambda c:c['source_pins'].pop('OptimizationCode.lean'),'historical63 source pins')
    ci_mutation('CI replay mode omitted',lambda c:c['checker_coverage']['complete proof closure'].pop(),'six-checker coverage')
    ci_mutation('CI comparator mode omitted',lambda c:c['checker_coverage']['frozen statement comparison'].pop(),'six-checker coverage')
    ci_mutation('CI control count reduced',lambda c:c.update(hostile_controls=17),'eighteen-control coverage')
    ci_mutation('semantic failure not actually confirmed',lambda c:c['actual_semantic_rejections'][0].update(actual_reason_present=False),'semantic rejection evidence')
    with zipfile.ZipFile(ROOT/'verification/external_optimization/ci_artifacts/external-optimization.zip') as z:
     full=json.loads(z.read('external-optimization.json'))
    for label,mutate,reason in [
     ('archived A02 target dropped',lambda p:p['targets'].pop(),'target declaration mismatch'),
     ('archived helper dropped',lambda p:p['helpers'].pop(),'complete closure coverage'),
     ('archived checker summary reduced',lambda p:p['checker_coverage']['frozen statement comparison'].pop(),'report checker coverage'),
     ('archived replay acceptance removed',lambda p:next(s for s in p['steps'] if 'replay' in s['label']).update(stdout='sandbox failed'),'actual six-mode'),
     ('archived axiom policy broken',lambda p:p['targets'][0]['axioms'].append('Invented.oracle'),'axiom policy')]:
     x=copy.deepcopy(full);mutate(x)
     rejected(label,lambda:v.validate_full_report(x,'passed optimization full assurance gates',15,952,49),reason)

    with tempfile.TemporaryDirectory(prefix='o3-status-guard-controls-') as tmp:
     root=Path(tmp);d=root/'verification/external_optimization';a=d/'ci_artifacts';a.mkdir(parents=True)
     (d/'CI_ARTIFACTS.json').write_bytes((ROOT/'verification/external_optimization/CI_ARTIFACTS.json').read_bytes())
     for item in ci['archives']:
      name=item['local_archive'];(a/name).symlink_to(ROOT/'verification/external_optimization/ci_artifacts'/name)
     # Clone-only receipt mutation: original byte pin must reject before parsing claims.
     c=copy.deepcopy(ci);c['checker_coverage']['complete proof closure'].pop()
     (d/'CI_ARTIFACTS.json').write_text(json.dumps(c))
     rejected('on-disk historical receipt forged',lambda:v.validate_o3_assurance(root),'CI receipt digest mismatch')
     (d/'CI_ARTIFACTS.json').write_bytes((ROOT/'verification/external_optimization/CI_ARTIFACTS.json').read_bytes())
     target=a/'external-optimization.zip';blob=target.read_bytes();target.unlink();target.write_bytes(blob[:-1]+bytes([blob[-1]^1]))
     rejected('on-disk historical archive corrupted',lambda:v.validate_o3_assurance(root),'historical archive digest mismatch')
     target.unlink();target.symlink_to(ROOT/'verification/external_optimization/ci_artifacts/external-optimization.zip')
     opt=root/'lean/external_optimization';opt.mkdir(parents=True)
     for name in ci['source_pins']:
      if name.endswith('.lean'):(opt/name).symlink_to(ROOT/'lean/external_optimization'/name)
     rate=root/'lean/external_rate';rate.mkdir(parents=True)
     with zipfile.ZipFile(ROOT/'verification/external_optimization/ci_artifacts/external-rate.zip') as rz:
      rr=json.loads(rz.read('external-rate.json'))
     for name in next(s for s in rr['steps'] if 'export' in s['label'])['source_sha256']:
      if name.endswith('.lean'):(rate/name).symlink_to(ROOT/'lean/external_rate'/name)
     v.validate_o3_assurance(root)
     target=opt/'OptimizationCode.lean';blob=target.read_bytes();target.unlink();target.write_bytes(blob+b'\n-- unverified source drift\n')
     rejected('on-disk checked program source drift',lambda:v.validate_o3_assurance(root),'checked proof/model source drift')

    outputs=[]
    for optimize in [False,True]:
     cmd=[sys.executable]+(['-O'] if optimize else[])+[str(ROOT/'certificates/external_problems/verify.py')]
     p=subprocess.run(cmd,cwd=ROOT,capture_output=True,text=True)
     (HERE/('status_guard_optimized.log' if optimize else 'status_guard_normal.log')).write_text(p.stdout+p.stderr)
     if p.returncode:raise RuntimeError('Positive finite-checker failed')
     outputs.append(json.loads(p.stdout))
    expected={'bridge':json.loads((ROOT/'certificates/external_problems/bridge.json').read_text()),'o3':json.loads((ROOT/'certificates/external_problems/o3.json').read_text()),'frozen_supporting_spec_hashes':'match','limits':'This finite-checker report certifies no infinite theorem, novelty or human review; the separate analytic package has its own source-pinned assurance receipts.'}
    if outputs[0]!=outputs[1] or outputs[0]!=expected:raise RuntimeError('Original finite outputs changed')
    for name,pin in {'bridge.json':'e578b59ae98f572ab53aba9ed5033dd4da29166592c4ee34f5af014731393139','o3.json':'db9bc2aa762013fa377bbc1268033ef49b338bc2e92894f27dfb19e3cd6db5da'}.items():
     if hashlib.sha256((ROOT/'certificates/external_problems'/name).read_bytes()).hexdigest()!=pin:
      raise RuntimeError('Pinned original finite output changed: '+name)
    sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
    receipt=dict(status='focused metadata guard positive/negative checks passed; not Lean replay',controls=controls,control_count=len(controls),control_runtime_optimized=sys.flags.optimize,positive_historical_seven_job_guard=True,finite_outputs_unchanged=True,python_optimized_output_equal=True,public_sha256={n:sha(ROOT/n) for n in ['papers/external_problems/status.json','certificates/external_problems/verify.py']},historical_ci_sha256=sha(ROOT/'verification/external_optimization/CI_ARTIFACTS.json'),limitations=['Validates historical pinned receipts/logs and current proof-source identity; does not rerun independent kernels.','Metadata mutations are not mathematical counterexamples or new Lean proof controls.'])
    (HERE/('legacy31_receipt.optimized.json' if sys.flags.optimize else 'legacy31_receipt.normal.json')).write_text(json.dumps(receipt,indent=2)+'\n')
    return dict(v=v,register=register,controls=controls,receipt=receipt)
