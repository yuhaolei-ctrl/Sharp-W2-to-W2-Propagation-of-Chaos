import datetime,hashlib,json,pathlib,re,subprocess,sys
root=pathlib.Path.cwd(); out=root/'qa/rough_eulerian_time_weak'
mods=['RoughEulerianTimePrimitive','RoughEulerianTimeSmoothing','RoughEulerianTimeKernel','RoughEulerianTimeWeak']
ns='SharpWasserstein.RoughEulerianTime.'
result={'timestamp_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Genuine L1 primitive Fubini/integration by parts, normalized time kernel, differentiated original compact-test weak equation with actual joint Riesz flux; no completed smoothed law or rough transport theorem claimed.','modules':[],'declarations':[],'allowed_axioms':['propext','Classical.choice','Quot.sound']}
axioms=['import SharpWasserstein.RoughEulerianTimeWeak']
for name in mods:
 p=root/'SharpWasserstein'/f'{name}.lean'; src=p.read_text()
 bad=re.search(r'\b(sorry|axiom|unsafe|native_decide)\b',src)
 if bad: raise RuntimeError(f'forbidden source token {name}:{bad.group()}')
 declarations=[]
 for ln,line in enumerate(src.splitlines(),1):
  m=re.match(r'\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:def|abbrev|theorem|lemma|instance|structure)\s+([A-Za-z_][A-Za-z_0-9]*)',line)
  if m:
   full=ns+m.group(1);declarations.append({'name':full,'source':str(p.relative_to(root)),'line':ln});axioms.append('#print axioms '+full)
 result['declarations']+=declarations
 for mode in ['compile','kernel']:
  cmd=['python3','lean_local.py']+(['-o',f'.lake/build/lib/lean/SharpWasserstein/{name}.olean',f'SharpWasserstein/{name}.lean'] if mode=='compile' else ['--kernel',f'SharpWasserstein.{name}'])
  log=out/f'{name}-{mode}.log'
  with log.open('w') as f: proc=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT)
  print(name,mode,proc.returncode,flush=True)
  if proc.returncode: raise RuntimeError(log)
 o=root/'.lake/build/lib/lean/SharpWasserstein'/f'{name}.olean'
 result['modules'].append({'module':'SharpWasserstein.'+name,'source':str(p.relative_to(root)),'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'olean_sha256':hashlib.sha256(o.read_bytes()).hexdigest(),'compile_exit':0,'kernel_replay_exit':0})
p=out/'Axioms.lean';p.write_text('\n'.join(axioms)+'\n')
proc=subprocess.run(['python3','lean_local.py',str(p.relative_to(root))],capture_output=True,text=True)
(out/'axioms.log').write_text(proc.stdout+proc.stderr)
if proc.returncode: raise RuntimeError('axiom inspection failed')
allowed=set(result['allowed_axioms'])
for d in result['declarations']:
 name=d['name'];m=re.search("'"+re.escape(name)+"' depends on axioms: \\[(.*?)\\]",proc.stdout,re.S)
 if m: used={x.strip() for x in m.group(1).split(',') if x.strip()}
 elif "'"+name+"' does not depend on any axioms" in proc.stdout: used=set()
 else: raise RuntimeError('unparsed axioms '+name)
 if not used<=allowed: raise RuntimeError((name,used))
 d['axioms']=sorted(used)
result['commands']={'compile':'python3 lean_local.py -o .lake/build/lib/lean/SharpWasserstein/<Module>.olean SharpWasserstein/<Module>.lean','kernel':'python3 lean_local.py --kernel SharpWasserstein.<Module>','axioms':'python3 lean_local.py qa/rough_eulerian_time_weak/Axioms.lean'}
(out/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASSED',len(mods),'modules',len(result['declarations']),'declarations; standard axioms only',flush=True)
