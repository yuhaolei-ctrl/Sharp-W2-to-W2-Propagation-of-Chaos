#!/usr/bin/env python3
"""Build the pinned Lean 4.32 Brownian/Wiener source closure locally.

Only this explicit dependency closure is compiled; no downloaded build script
is executed. The original sources and external Mathlib cache remain untouched.
The report records source hashes and compile results, not a full proof claim.
"""
from pathlib import Path
import argparse, hashlib, json, subprocess, sys
from audit import strip_lean_noncode, TOKEN_RE
import re
ROOT=Path(__file__).resolve().parents[1]
SOURCES={
 'BrownianMotion': ROOT/'external_sources/brownian-motion-bbf1359d13a51c5da77ad3db520f1da76ffe669e',
 'KolmogorovExtension4': ROOT/'external_sources/kolmogorov_extension4-f33cbc388e5d444606dffa7eec507a26b62c15bb',
}

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--dry-run',action='store_true');ap.add_argument('--skip-mathlib',action='store_true');ap.add_argument('--replay',action='store_true');args=ap.parse_args()
 seen=set();ordered=[];mathlib=set()
 def visit(module):
  if module in seen:return
  seen.add(module);namespace=module.split('.')[0]
  if namespace=='Mathlib':mathlib.add(module);return
  if namespace not in SOURCES:raise ValueError('Unrecognized external dependency '+module)
  source=SOURCES[namespace].joinpath(*module.split('.')).with_suffix('.lean')
  clean=strip_lean_noncode(source.read_text())
  if TOKEN_RE.search(clean):raise ValueError('Forbidden executable proof token in '+module)
  for dep in re.findall(r'^\s*(?:(?:public|private)\s+)?import\s+([\w.]+)',clean,re.M):visit(dep)
  ordered.append((module,source))
 visit('BrownianMotion.Gaussian.BrownianMotion')
 if args.dry_run:
  print(json.dumps({'external_modules':[m for m,_ in ordered],'mathlib_imports':sorted(mathlib)},indent=2));return 0
 if not args.skip_mathlib:
  subprocess.run([sys.executable,str(ROOT/'scripts/bootstrap_mathlib.py'),*sorted(mathlib)],cwd=ROOT,check=True)
 reportpath=ROOT/'qa/brownian_build.json'
 previous=json.loads(reportpath.read_text()) if reportpath.exists() else {'modules':[]}
 old={x['module']:x for x in previous['modules']}
 report={'status':'running','source_release':'v4.32.0','complete_manuscript_proof':False,'modules':[]}
 for module,src in ordered:
  sha=hashlib.sha256(src.read_bytes()).hexdigest();out=ROOT/'.lake/build/lib/lean'/Path(*module.split('.')).with_suffix('.olean')
  entry={'module':module,'source':str(src.relative_to(ROOT)),'source_sha256':sha}
  cached=out.is_file() and old.get(module,{}).get('source_sha256')==sha and old.get(module,{}).get('compile_exit_code')==0
  if cached:entry.update(compile_exit_code=0,cached=True)
  else:
   print('Compiling '+module,flush=True);out.parent.mkdir(parents=True,exist_ok=True)
   log=ROOT/'qa'/('external_'+module+'.build.log')
   with log.open('w') as stream:
    cp=subprocess.run([sys.executable,str(ROOT/'lean_local.py'),'-R',str(SOURCES[module.split('.')[0]]),'-o',str(out),str(src)],cwd=ROOT,stdout=stream,stderr=subprocess.STDOUT)
   entry.update(compile_exit_code=cp.returncode,log=str(log.relative_to(ROOT)))
  report['modules'].append(entry)
  if entry['compile_exit_code']:
   report['status']='failed';reportpath.write_text(json.dumps(report,indent=2)+'\n');print((ROOT/entry['log']).read_text(),flush=True);return 1
  reportpath.write_text(json.dumps(report,indent=2)+'\n')
 report['status']='compiled_not_yet_kernel_replayed';reportpath.write_text(json.dumps(report,indent=2)+'\n')
 if args.replay:
  replay=ROOT/'qa/BrownianKernelReplay.lean'
  names=', '.join(json.dumps(m) for m,_ in ordered)
  replay.write_text('import LeanChecker\n\n#eval do\n  Lean.initSearchPath (← Lean.findSysroot)\n  for name in ['+names+'] do\n    IO.println ("replaying " ++ name)\n    replayFromImports name.toName\n')
  log=ROOT/'qa/brownian_kernel_replay.log'
  with log.open('w') as stream:
   cp=subprocess.run([sys.executable,str(ROOT/'lean_local.py'),str(replay)],cwd=ROOT,stdout=stream,stderr=subprocess.STDOUT)
  replayed=set(re.findall(r'^replaying ([\w.]+)$',log.read_text(),re.M))
  report['kernel_replay_exit_code']=cp.returncode
  report['missing_replay_modules']=sorted({m for m,_ in ordered}-replayed)
  report['status']='kernel_replayed' if cp.returncode==0 and not report['missing_replay_modules'] else 'replay_failed'
  reportpath.write_text(json.dumps(report,indent=2)+'\n')
  if report['status']=='replay_failed':print(log.read_text(),flush=True);return 1
 print('Compiled '+str(len(ordered))+' pinned external modules; status: '+report['status'],flush=True);return 0
if __name__=='__main__':raise SystemExit(main())
