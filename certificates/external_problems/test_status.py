"""Portable85 release-metadata controls; not the21 Lean hostile controls.
Uses only public files/immutable CI archives and temporary mutation fixtures.
No Lean, network, Git checkout/history or private runtime dependencies.
"""

def main():
    from pathlib import Path
    import sys,json,copy,hashlib,gzip,zipfile,tempfile,ast,subprocess,argparse
    sys.dont_write_bytecode=True
    import status_legacy_controls
    HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--report',type=Path);args=parser.parse_args()
    work=tempfile.TemporaryDirectory(prefix='external-status-evidence-');EVIDENCE=Path(work.name)
    sha=lambda b:hashlib.sha256(b).hexdigest()
    production=ROOT/'certificates/external_problems/verify.py';source_before=production.read_bytes()
    legacy=status_legacy_controls.run(ROOT,EVIDENCE);v=legacy['v'];register=legacy['register'];controls=list(legacy['controls']);positives=[];failures=[]

    def require(ok,message):
     if not ok:raise RuntimeError(message)
    def rejected(label,action,reason,category):
     try:action()
     except ValueError as e:
      if reason in str(e):controls.append({'label':label,'result':'rejected','reason':str(e),'category':category})
      else:failures.append({'label':label,'failure':'wrong rejection','actual':str(e),'expected':reason})
     except Exception as e:failures.append({'label':label,'failure':'unexpected exception','actual':repr(e)})
     else:failures.append({'label':label,'failure':'mutation accepted','expected':reason})
    def change_claim(label,mutate,reason):
     d=copy.deepcopy(register);mutate(next(c for c in d['claims'] if c['problem']=='M4'))
     rejected(label,lambda:v.validate_status(d),reason,'scope/status')

    def full_stdout(z,p):
     out={};evidence=[]
     for s in p['steps']:
      if 'stdout_gzip' in s:
       parts=Path(s['stdout_gzip']).parts
       matches=['/'.join(parts[i:]) for i in range(len(parts)) if '/'.join(parts[i:]) in z.namelist()]
       require(matches,'missing complete log');member=matches[0];blob=z.read(member);raw=gzip.decompress(blob)
       if 'stdout_gzip_sha256' in s:require(sha(blob)==s['stdout_gzip_sha256'],'compressed stdout hash')
      else:member=None;raw=s.get('stdout','').encode()
      if 'stdout_bytes' in s:require(len(raw)==s['stdout_bytes'],'complete stdout bytes')
      if 'stdout_sha256' in s:require(sha(raw)==s['stdout_sha256'],'complete stdout hash')
      out[s['label']]=raw.decode();evidence.append({'label':s['label'],'member':member,'raw_bytes':len(raw),'sha256':sha(raw)})
     return out,evidence

    def fixture(root):
     d=root/'verification/external_unrestricted';a=d/'ci_artifacts';a.mkdir(parents=True);src=ROOT/'verification/external_unrestricted'
     (d/'CI_ARTIFACTS.json').write_bytes((src/'CI_ARTIFACTS.json').read_bytes());ci=json.loads((d/'CI_ARTIFACTS.json').read_text())
     for item in ci['archives']:(a/item['local_archive']).symlink_to(src/'ci_artifacts'/item['local_archive'])
     p=root/'lean/external_unrestricted';p.mkdir(parents=True)
     for name in ci['unrestricted']['source_pins']:(p/name).symlink_to(ROOT/'lean/external_unrestricted'/name)
     (p/'inventory.json').write_bytes((ROOT/'lean/external_unrestricted/inventory.json').read_bytes())
     return d,p,ci

    def disk_mutation(path,blob,action):
     old=path.read_bytes();link=path.readlink() if path.is_symlink() else None
     path.unlink();path.write_bytes(blob)
     try:return action()
     finally:
      path.unlink()
      if link is None:path.write_bytes(old)
      else:path.symlink_to(link)

    # Public embedded source-text pins avoid Git history and Python-version AST hashes.
    parsed=ast.parse(source_before.decode())
    function_source=lambda name:ast.get_source_segment(source_before.decode(),next(x for x in parsed.body if isinstance(x,ast.FunctionDef) and x.name==name))
    for name,pin in {'validate_ci_metadata':'0962d46f96d5b03d58073bbcb35fd67f8705940dbfcf0917826b03268976f619','validate_o3_assurance':'333513af3a0453ff1e7a4f1b90b2c82f17593f042386bf3381f819e5e6a89f4b'}.items():
     require(sha(function_source(name).encode())==pin,'Historical O3 guard source changed: '+name)
    full_source=function_source('validate_full_report')
    old_expression="in s.get('stdout', '')\n"
    new_expression="in\n            (stdout_texts[s['label']] if stdout_texts is not None else s.get('stdout', ''))\n"
    require(full_source.count(', *, stdout_texts=None')==1 and full_source.count(new_expression)==1,'Optional stdout source normalization anchor changed')
    full_source=full_source.replace(', *, stdout_texts=None','',1).replace(new_expression,old_expression,1)
    require(sha(full_source.encode())=='7209586362ea5d0f7fd25d525fed865ee70c2a5b3e0c25c649f243b5cc44cc47','Historical default full-report behavior changed')
    positives.append('Pinned O3 functions and default full-report behavior unchanged; original31 controls retained')
    for label,mutation,reason in [
     ('M4 c1 scope enlarged to all thresholds',lambda c:c['unrestricted_fixed_reference_c1_extension'].update(scope='all c entropy solved'),'separate c1 extension'),
     ('M4 c1 project redirected',lambda c:c['unrestricted_fixed_reference_c1_extension'].update(project='lean/external_rate'),'separate c1 extension'),
     ('M4 c1 target count reduced',lambda c:c['unrestricted_fixed_reference_c1_extension'].update(targets=22),'separate c1 extension'),
     ('M4 c1 closure count reduced',lambda c:c['unrestricted_fixed_reference_c1_extension'].update(closures=503),'separate c1 extension'),
     ('M4 c1 receipt source forged',lambda c:c['unrestricted_fixed_reference_c1_extension']['assurance'].update(source_commit='0'*40),'separate c1 extension source'),
     ('M4 c1 receipt tree forged',lambda c:c['unrestricted_fixed_reference_c1_extension']['assurance'].update(source_tree='0'*40),'separate c1 extension source'),
     ('M4 c1 receipt run forged',lambda c:c['unrestricted_fixed_reference_c1_extension']['assurance'].update(run_id=1),'separate c1 extension source'),
     ('M4 c1 receipt path forged',lambda c:c['unrestricted_fixed_reference_c1_extension']['assurance'].update(receipt='unverified.json'),'separate c1 extension source'),
     ('M4 finite bridge called analytic proof',lambda c:c['finite_bridge_foundation'].update(analytic_headline_proved=True),'finite bridge foundation')]:change_claim(label,mutation,reason)

    ci_dir=ROOT/'verification/external_unrestricted';ci=json.loads((ci_dir/'CI_ARTIFACTS.json').read_text());archive_evidence=[]
    for item in ci['archives']:
     blob=(ci_dir/'ci_artifacts'/item['local_archive']).read_bytes();require(len(blob)==item['bytes'] and sha(blob)==item['zip_sha256'],'archive pin mismatch')
     with zipfile.ZipFile(ci_dir/'ci_artifacts'/item['local_archive']) as z:
      if item['local_archive']=='release-verification.zip':
       d=json.loads(z.read('verification.json'));require(d['status']=='passed' and len(d['checks'])==43 and all(c['exit_code']==0 for c in d['checks']),'legacy43 changed');archive_evidence.append({'archive':item['local_archive'],'checks':43});continue
      name='external-analysis.json' if item['local_archive']=='external-analysis-h1.zip' else item['local_archive'].replace('.zip','.json')
      p=json.loads(z.read(name));outs,logs=full_stdout(z,p)
      stages=[s for s in p['steps'] if 'replay' in s['label'] or ('frozen' in s['label'] and ('comparison' in s['label'] or 'statements' in s['label']))]
      require(len(stages)==2 and all(all(c+' kernel accepts the solution' in outs[s['label']] for c in v.CHECKERS) for s in stages),'actual mode logs absent')
      archive_evidence.append({'archive':item['local_archive'],'source_tree':z.read(next(n for n in z.namelist() if n.endswith('source-tree.txt'))).decode().splitlines(),'stdout_logs':logs,'checker_stages':2})
      if item['local_archive']=='external-unrestricted.zip':
       main=p;actual_outs=outs;mut=json.loads(z.read('external-unrestricted-mutations.json'));positive_raw=gzip.decompress(z.read('external-unrestricted-mutations-logs/positive-full.json.gz'));require(sha(positive_raw)==mut['positive_full_report_sha256'],'positive hash')
       positive=json.loads(positive_raw);pouts,plogs=full_stdout(z,positive);v.validate_full_report(positive,'passed unrestricted full assurance gates',23,504,32,stdout_texts=pouts)
       require(main['targets']==positive['targets'] and main['helpers']==positive['helpers'] and main['models']==positive['models'],'positive coverage mismatch')
       semantic=[]
       for r in ci['unrestricted']['actual_semantic_rejections']:
        row=next(c for c in mut['commands'] if c['label']==r['label']);raw=gzip.decompress(z.read('external-unrestricted-mutations-logs/'+Path(row['log_gzip']).name))
        require(row['exit_code']==1 and row['expected_failure'] is True and row['rejection_reason_confirmed'] is True and sha(raw)==row['log_sha256']==r['log_sha256'] and all(s in raw.decode() for s in r['reason']),'semantic log mismatch')
        semantic.append({'label':r['label'],'sha256':sha(raw),'exit_code':1,'actual_reasons':r['reason']})
       fixture_texts={};fixture_pins=[]
       for command in mut['commands']:
        for f in command.get('fixture_sources',[]):
         compressed=z.read('external-unrestricted-mutations-logs/'+Path(f['gzip']).name);raw=gzip.decompress(compressed)
         require(sha(compressed)==f['gzip_sha256'] and sha(raw)==f['source_sha256'],'semantic fixture source digest')
         fixture_texts[(command['label'],f['name'])]=raw.decode();fixture_pins.append({'command':command['label'],'name':f['name'],'sha256':sha(raw)})
       require(len(fixture_pins)==9,'fixture count')
       require('theorem exponentialCountLower : True := by trivial' in fixture_texts[('wrong statement rejected by actual comparator','UnrestrictedSolution.lean')],'actual True wrapper absent')
       require('axiom hiddenPopulation : ExternalM4UnrestrictedDraft.ExponentialCountLower' in fixture_texts[('hidden imported axiom rejected by complete audit','BadPremise.lean')],'actual imported axiom absent')
       require('theorem exponentialCountLower : ExponentialCountLower := BadPremise.hiddenPopulation' in fixture_texts[('hidden imported axiom rejected by complete audit','UnrestrictedSolution.lean')],'actual axiom wrapper absent')
       swap_label='corrupt production swap rejected by Lean kernel proof';good=fixture_texts[(swap_label,'SwapPositive.lean')];bad=fixture_texts[(swap_label,'SwapCorrupt.lean')]
       production_defs=(ROOT/'lean/external_unrestricted/UnrestrictedDefinitions.lean').read_text();anchor='fun i => if i ∈ S then 1 else if'
       require(good.startswith(production_defs) and good.count(anchor)==1 and bad==good.replace(anchor,'fun i => if i ∈ S then 2 else if',1),'production swap fixture changed beyond exact1to2')
       require(next(c for c in mut['commands'] if c['label']=='positive literal production swap proof')['exit_code']==0,'positive production swap prerequisite failed')
       unrestricted_evidence={'positive_stdout_logs':plogs,'main_targets':len(main['targets']),'positive_targets':len(positive['targets']),'models':len(main['models']),'closures':main['own_theorem_count'],'modules':main['own_module_count'],'controls':len(mut['controls']),'actual_semantic_logs':semantic,'fixture_pins':fixture_pins}
    positives.append('All8 original digest/size-pinned ZIPs, seven source/tree formal reports and actual six-mode complete stdout in both stages; legacy43')
    positives.append('Main+positive23/13/504/32 exact coverage;21 controls and3 hashed actual semantic rejection logs')
    for label,mutate,reason in [
     ('739 main target omitted',lambda p:p['targets'].pop(),'target declaration mismatch'),
     ('739 main helper omitted',lambda p:p['helpers'].pop(),'complete closure coverage'),
     ('739 main own module count reduced',lambda p:p.update(own_module_count=31),'complete closure coverage'),
     ('739 main custom axiom injected',lambda p:p['targets'][0]['axioms'].append('Invented.hidden'),'axiom policy'),
     ('739 main export root omitted',lambda p:next(s for s in p['steps'] if 'export' in s['label'])['roots'].pop(),'exported declaration coverage'),
     ('739 main checker summary omitted',lambda p:p['checker_coverage']['frozen statement comparison'].pop(),'report checker coverage')]:
     d=copy.deepcopy(main);mutate(d);rejected(label,lambda:v.validate_full_report(d,'passed unrestricted full assurance gates',23,504,32,stdout_texts=actual_outs),reason,'full-report coverage')
    for stage in [s['label'] for s in main['steps'] if 'replay' in s['label'] or ('frozen' in s['label'] and ('comparison' in s['label'] or 'statements' in s['label']))]:
     for checker in v.CHECKERS:
      outs=dict(actual_outs);require(checker+' kernel accepts the solution' in outs[stage],'Test acceptance anchor missing');outs[stage]=outs[stage].replace(checker+' kernel accepts the solution','REMOVED ACCEPTANCE')
      rejected('739 actual '+checker+' acceptance removed from '+stage,lambda:v.validate_full_report(main,'passed unrestricted full assurance gates',23,504,32,stdout_texts=outs),'actual six-mode','actual stdout consumption')

    with tempfile.TemporaryDirectory(prefix='unrestricted-status-controls-') as tmp:
     root=Path(tmp);d,p,fixture_ci=fixture(root);v.validate_unrestricted_assurance(root);positives.append('Fully materialized pristine isolated current guard fixture passes before mutations')
     inv_path=p/'inventory.json';original_inv=json.loads(inv_path.read_text())
     for label,mutate,reason in [
      ('current inventory owned module dropped',lambda i:i['owned_modules'].pop(),'owned32 module coverage'),
      ('current inventory owned module duplicated',lambda i:i['owned_modules'].__setitem__(-1,i['owned_modules'][0]),'owned32 module coverage'),
      ('current inventory owned module invented',lambda i:i['owned_modules'].append('Invented'),'owned32 module coverage'),
      ('current inventory source pin omitted',lambda i:i['sources_sha256'].pop('UnrestrictedCounts.lean'),'inventory/source closure'),
      ('current inventory target omitted',lambda i:i['targets'].pop(),'inventory/source closure'),
      ('current inventory helper omitted',lambda i:i['helpers'].pop(),'inventory/source closure'),
      ('current inventory model omitted',lambda i:i['models'].pop(),'exact13 model'),
      ('current inventory model body corrupted',lambda i:i['models'][0].update(raw_body='True'),'exact13 model')]:
      inv=copy.deepcopy(original_inv);mutate(inv)
      disk_mutation(inv_path,json.dumps(inv).encode(),lambda:rejected(label,lambda:v.validate_unrestricted_assurance(root),reason,'current inventory'))
     for filename in ['UnrestrictedDefinitions.lean','UnrestrictedInjection.lean','comparator.json','verify.py','owned_modules.json','frozen_models.json','lakefile.toml','ARGUMENT.md','provenance.json']:
      target=p/filename;disk_mutation(target,target.read_bytes()+b'\n ',lambda:rejected('checked source/config drift '+filename,lambda:v.validate_unrestricted_assurance(root),'checked source/configuration drift','source/config hash'))
     receipt=d/'CI_ARTIFACTS.json';bad=copy.deepcopy(fixture_ci);bad['unrestricted']['model_bodies']=12
     disk_mutation(receipt,json.dumps(bad).encode(),lambda:rejected('historical739 receipt model count forged',lambda:v.validate_unrestricted_assurance(root),'receipt digest mismatch','immutable receipt hash'))
     for item in fixture_ci['archives']:
      target=d/'ci_artifacts'/item['local_archive'];blob=target.read_bytes()
      disk_mutation(target,blob[:-1]+bytes([blob[-1]^1]),lambda item=item:rejected('739 archive corrupted '+item['local_archive'],lambda:v.validate_unrestricted_assurance(root),'historical archive digest mismatch','archive hash'))
     # README is the sole source drift exception, and its inventory digest must be refreshed.
     readme=p/'README.md';changed=readme.read_bytes()+b'\nPrivate test of allowed explanatory README drift.\n'
     disk_mutation(readme,changed,lambda:rejected('README drift without refreshed inventory',lambda:v.validate_unrestricted_assurance(root),'inventory/source closure','README exception boundary'))
     updated=copy.deepcopy(original_inv);updated['sources_sha256']['README.md']=sha(changed)
     def allowed_doc():
      disk_mutation(inv_path,json.dumps(updated).encode(),lambda:v.validate_unrestricted_assurance(root))
     disk_mutation(readme,changed,allowed_doc);positives.append('Only README drift with exact inventory digest update passes; ARGUMENT/provenance/config/proofs cannot drift')
     v.validate_unrestricted_assurance(root)

    require(production.read_bytes()==source_before,'Production guard changed during control run')
    result={'status':'PASS focused release guard controls; not new Lean replay' if not failures else 'FAIL focused guard controls',
     'runtime_optimized':sys.flags.optimize,'controls':controls,'control_count':len(controls),'failures':failures,'positive_checks':positives,
     'archive_complete_stdout_audit':archive_evidence,'unrestricted_evidence':unrestricted_evidence,
     'source_sha256':{str(x.relative_to(ROOT)):sha(x.read_bytes()) for x in [production,ROOT/'papers/external_problems/status.json',ROOT/'claims.json',ci_dir/'CI_ARTIFACTS.json',ROOT/'lean/external_unrestricted/inventory.json']},
     'test_source_sha256':sha(Path(__file__).read_bytes()),'legacy31_source_sha256':sha((HERE/'status_legacy_controls.py').read_bytes()),
     'limits':['Metadata/hash/coverage/parser controls, not mathematical counterexamples or new independent-kernel runs.','Historical739 eight-job evidence is source pinned; current metadata heads still require regression.','M4 rung entropy/R8/R9 remain draft analytic candidates; c1 all-length extension is separate.']}
    if not failures:
        require(len(controls)==85,'Expected all85 meaningful controls to reject')
    if args.report:
     args.report.parent.mkdir(parents=True,exist_ok=True);args.report.write_text(json.dumps(result,indent=2)+'\n')
    summary={k:v for k,v in result.items() if k not in ['controls','archive_complete_stdout_audit','unrestricted_evidence','source_sha256']}
    summary['controls_sha256']=sha(json.dumps(controls,sort_keys=True,separators=(',',':')).encode())
    summary['limits']+=['Complete per-control and archive inspection rows are available with --report PATH.']
    print(json.dumps(summary,sort_keys=True))
    work.cleanup()
    if failures:raise SystemExit(1)

if __name__ == "__main__":
    main()
