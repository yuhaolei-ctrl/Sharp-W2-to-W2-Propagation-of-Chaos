#!/usr/bin/env python3
"""Build the local proof closure. No missing proof is accepted as success."""
from pathlib import Path
import argparse, hashlib, json, re, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
ROOT=Path(__file__).resolve().parent

def path_of(module): return ROOT.joinpath(*module.split('.')).with_suffix('.lean')
def dependencies(module):
 return [s for s in re.findall(r'^import\s+([\w.]+)',path_of(module).read_text(),re.M) if s=='SharpWasserstein' or s.startswith('SharpWasserstein.')]
def collect(module, graph):
 if module in graph: return
 graph[module]=dependencies(module)
 for dep in graph[module]:collect(dep,graph)
def output_of(module):return ROOT/'.lake/build/lib/lean'/Path(*module.split('.')).with_suffix('.olean')
def run(module, replay, fresh):
 src=path_of(module); out=output_of(module); out.parent.mkdir(parents=True,exist_ok=True)
 item={'module':module,'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest()}
 needs=fresh or not out.exists() or out.stat().st_mtime<src.stat().st_mtime or any(output_of(dep).stat().st_mtime>out.stat().st_mtime for dep in dependencies(module))
 start=time.monotonic()
 if needs:
  print('Compiling '+module,flush=True)
  cp=subprocess.run([sys.executable,str(ROOT/'lean_local.py'),'-o',str(out),str(src)],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
  (ROOT/'qa'/f'{module}.build.log').write_text(cp.stdout)
  item['compile_exit_code']=cp.returncode
  if cp.returncode: print(cp.stdout,flush=True);return item
 else: item['compile_exit_code']=0;item['cached']=True
 item['compile_seconds']=round(time.monotonic()-start,3)
 if replay:
  print('Replaying '+module,flush=True)
  cp=subprocess.run([sys.executable,str(ROOT/'lean_local.py'),'--kernel','-v',module],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
  (ROOT/'qa'/f'{module}.replay.log').write_text(cp.stdout)
  item['replay_exit_code']=cp.returncode
  if cp.returncode:print(cp.stdout,flush=True)
 return item

def main():
 a=argparse.ArgumentParser(description=__doc__);a.add_argument('module',nargs='?',default='SharpWasserstein');a.add_argument('--jobs',type=int,default=2);a.add_argument('--replay',action='store_true');a.add_argument('--fresh',action='store_true');args=a.parse_args()
 graph={};collect(args.module,graph)
 all_imports={dep for mod in graph for dep in re.findall(r'^import\s+([\w.]+)',path_of(mod).read_text(),re.M)}
 if any(dep.startswith(('BrownianMotion.','KolmogorovExtension4.')) for dep in all_imports):
  subprocess.run([sys.executable,str(ROOT/'scripts/bootstrap_brownian.py'),*(['--replay'] if args.replay else [])],cwd=ROOT,check=True)
 bootstrap=ROOT/"scripts/bootstrap_mathlib.py"
 if bootstrap.exists():
  mathlib_imports=sorted({dep for mod in graph for dep in
   re.findall(r'^import\s+([\w.]+)',path_of(mod).read_text(),re.M) if dep.startswith('Mathlib.')})
  subprocess.run([sys.executable,str(bootstrap),*mathlib_imports],cwd=ROOT,check=True)
 pending=set(graph);done=set();running={}
 aggregate_replay=args.replay and args.module=='SharpWasserstein'
 report={'validation_scope':'source compilation and independent kernel replay; exact main target is checked by scripts/audit.py --require-main','target':args.module,'status':'running','modules':[]};qa=ROOT/'qa';qa.mkdir(exist_ok=True);reportpath=qa/('build_'+args.module.replace('.','_')+'.json')
 with ThreadPoolExecutor(max_workers=args.jobs) as pool:
  while pending or running:
   for mod in sorted(pending):
    if set(graph[mod])<=done and len(running)<args.jobs:
     running[pool.submit(run,mod,args.replay and not aggregate_replay,args.fresh)]=mod;pending.remove(mod)
   if not running:raise RuntimeError('Dependency cycle')
   completed,_=wait(running,return_when=FIRST_COMPLETED)
   for future in completed:
    mod=running.pop(future);item=future.result();report['modules'].append(item)
    if item['compile_exit_code'] or item.get('replay_exit_code',0):
     report['status']='failed';reportpath.write_text(json.dumps(report,indent=2)+'\n');return 1
    done.add(mod)
   reportpath.write_text(json.dumps(report,indent=2)+'\n')
 if aggregate_replay:
  # The stock CLI treats names as prefixes and launches every match in
  # parallel. Invoke its unchanged replay function sequentially instead.
  print('Replaying all modules sequentially with LeanChecker',flush=True)
  replay_source=qa/'KernelReplay.lean'
  module_names=', '.join(json.dumps(mod) for mod in sorted(graph))
  replay_source.write_text('import LeanChecker\n\n#eval do\n  Lean.initSearchPath (← Lean.findSysroot)\n  for name in ['+module_names+'] do\n    IO.println ("replaying " ++ name)\n    replayFromImports name.toName\n')
  cp=subprocess.run([sys.executable,str(ROOT/'lean_local.py'),str(replay_source)],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
  (qa/'SharpWasserstein.replay.log').write_text(cp.stdout)
  replayed=set(re.findall(r'^replaying ([\w.]+)$',cp.stdout,re.M))
  if cp.returncode or not set(graph)<=replayed:
   report['status']='failed';report['replay_exit_code']=cp.returncode
   report['missing_replay_modules']=sorted(set(graph)-replayed)
   reportpath.write_text(json.dumps(report,indent=2)+'\n');print(cp.stdout,flush=True);return 1
  for item in report['modules']:
   item['replay_exit_code']=0;item['replay_mode']='sequential LeanChecker.replayFromImports'
 report['status']='passed';reportpath.write_text(json.dumps(report,indent=2)+'\n');print(f'Passed {len(done)} modules. Full manuscript status remains tracked separately.',flush=True);return 0
if __name__=='__main__':raise SystemExit(main())
