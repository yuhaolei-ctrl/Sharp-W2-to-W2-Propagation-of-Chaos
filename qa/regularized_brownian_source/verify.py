from pathlib import Path
import sys,subprocess,hashlib,json
from datetime import datetime, timezone
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT))
from scripts.audit import strip_lean_noncode,declarations,parse_axioms,ALLOWED_AXIOMS,TOKEN_RE
OUT=Path(__file__).parent
names=['RegularizedBrownianSourceCoordinates','RegularizedBrownianSourceData','RegularizedBrownianSourceBound','RegularizedBrownianSourceSwitch']
report={'scope':'Four actual regularized-current source modules: prescribed-reference data and one-source initial profile from original Wasserstein assumptions; sharp original-kernel propagated energy; exact source-energy identification on the prescribed switch curve; not a complete manuscript proof','complete_manuscript_proof':False,'generated_utc':datetime.now(timezone.utc).isoformat(),'modules':[]}
dependencies=['InitialSourceMarginalRegularized','InitialSourceMarginalConfiguration','InitialCurrentBrownianSource','PrescribedEntropyProfile','BrownianPeriodicHierarchyInitial','BrownianEnergyPeriodization','PrescribedSwitchBrownianSource','PrescribedSwitchBrownianLaw']
dep_hashes={n:hashlib.sha256((ROOT/'SharpWasserstein'/f'{n}.lean').read_bytes()).hexdigest() for n in dependencies}
report['pinned_direct_foundations']=dep_hashes
all_decls=[]
for name in names:
    p=ROOT/'SharpWasserstein'/f'{name}.lean'
    source=p.read_text(); clean=strip_lean_noncode(source)
    assert not TOKEN_RE.search(clean), name
    ds=declarations(clean,str(p.relative_to(ROOT))); all_decls+=ds
    sha=hashlib.sha256(p.read_bytes()).hexdigest()
    compile_cmd=[sys.executable,'lean_local.py','-o',f'.lake/build/lib/lean/SharpWasserstein/{name}.olean',str(p.relative_to(ROOT))]
    cp=subprocess.run(compile_cmd,cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (OUT/f'{name}.compile.log').write_text(cp.stdout)
    assert cp.returncode==0,(name,cp.stdout)
    print(name,'compile 0',flush=True)
    rp=subprocess.run([sys.executable,'lean_local.py','--kernel','-v',f'SharpWasserstein.{name}'],cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (OUT/f'{name}.kernel.log').write_text(rp.stdout)
    assert rp.returncode==0,(name,rp.stdout)
    assert hashlib.sha256(p.read_bytes()).hexdigest()==sha,name
    print(name,'independent kernel replay 0',flush=True)
    report['modules'].append({'file':str(p.relative_to(ROOT)),'sha256':sha,'declaration_count':len(ds),'compile_exit_code':cp.returncode,'independent_kernel_replay_exit_code':rp.returncode})
axiomsrc='\n'.join('import SharpWasserstein.'+n for n in names)+'\n\n'+'\n'.join('#print axioms '+d['name'] for d in all_decls)+'\n'
(OUT/'Axioms.lean').write_text(axiomsrc)
ap=subprocess.run([sys.executable,'lean_local.py','--stdin'],input=axiomsrc,cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
(OUT/'axioms.log').write_text(ap.stdout)
assert ap.returncode==0,ap.stdout
parsed=parse_axioms(ap.stdout)
assert set(parsed)=={d['name'] for d in all_decls}
assert all(set(v)<=ALLOWED_AXIOMS for v in parsed.values())
assert dep_hashes=={n:hashlib.sha256((ROOT/'SharpWasserstein'/f'{n}.lean').read_bytes()).hexdigest() for n in dependencies}
report['declarations']=parsed
report['allowed_axioms']=sorted(ALLOWED_AXIOMS)
report['forbidden_token_scanner_clear']=True
report['lean_version']=subprocess.check_output([sys.executable,'lean_local.py','--version'],cwd=ROOT,text=True).strip()
(OUT/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
print('PASS',len(names),'modules',len(all_decls),'declarations',flush=True)
