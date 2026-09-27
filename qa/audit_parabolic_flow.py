"""Independent replay and axiom audit of parabolic energy and flow derivative additions."""
from pathlib import Path
import sys, subprocess, json, hashlib
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from audit import strip_lean_noncode, TOKEN_RE, declarations, parse_axioms, ALLOWED_AXIOMS
modules = ['PeriodicDriftGradientBound', 'PeriodicDriftResidual', 'PeriodicJacobianLimit', 'PeriodicCoefficientBounds', 'PeriodicParabolicEnergy', 'FlowInitialDerivativeLinear', 'FlowInitialDerivativeRemainder', 'FlowInitialDerivative', 'FlowInitialDerivativeGlobal', 'FlowInitialDerivativeSmooth', 'PeriodicConvolutionWeak']
all_decls, report = [], {}
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
for name in modules:
    p = ROOT / 'SharpWasserstein' / (name + '.lean')
    clean = strip_lean_noncode(p.read_text())
    assert not TOKEN_RE.search(clean), name
    all_decls.extend(declarations(clean, str(p.relative_to(ROOT))))
    result = subprocess.run([sys.executable, 'lean_local.py', '--kernel', '-v',
                             'SharpWasserstein.' + name], cwd=ROOT, capture_output=True, text=True)
    output = result.stdout + result.stderr
    (ROOT / 'qa' / ('ParabolicFlowReplay_' + name + '.log')).write_text(output)
    print(name, result.returncode, flush=True)
    assert result.returncode == 0 and 'error:' not in output, output
    report[name] = {'source_sha256': sha(p),
                   'olean_sha256': sha(ROOT / '.lake/build/lib/lean/SharpWasserstein' / (name+'.olean')),
                   'independent_kernel_replay': True}
audit_file = ROOT / 'qa/ParabolicFlowAxioms.lean'
audit_file.write_text(''.join('import SharpWasserstein.' + name + '\n' for name in modules) +
                      '\n'.join('#print axioms ' + d['name'] for d in all_decls) + '\n')
r = subprocess.run([sys.executable, 'lean_local.py', str(audit_file)], cwd=ROOT,
                   capture_output=True, text=True)
output = r.stdout+r.stderr
(ROOT/'qa/ParabolicFlowAxioms.log').write_text(output)
assert r.returncode == 0 and 'error:' not in output, output
axioms = parse_axioms(output)
assert len(axioms) == len(all_decls), (len(axioms), len(all_decls))
assert set(axioms) == {d['name'] for d in all_decls}
used = set().union(*(set(v) for v in axioms.values()))
assert used <= ALLOWED_AXIOMS, used
(ROOT/'qa/parabolic_flow_verification.json').write_text(json.dumps({
    'scope': 'Actual closed-space periodic parabolic energy inequality with vanishing Galerkin residual; actual Jacobian integral convergence; genuine all-time autonomous flow initial derivative; actual convolution density time derivative from WeakEvolution. The marginal hierarchy, propagated tangent source, dynamic transport connection and MainTheorem remain open.',
    'complete_manuscript_proof': False,
    'forbidden_tokens': [],
    'forbidden_token_scan_scope': 'The listed project source module, with nested comments and strings removed. Dependencies are checked by axiom closure; generated QA and vendor sources are outside token scan.',
    'independent_kernel_replay': True,
    'audited_declarations': len(all_decls),
    'axioms': sorted(used),
    'modules': report,
    'declarations': axioms,
}, indent=2)+'\n')
print(f'PASS: {len(modules)} modules, {len(all_decls)} declarations, {sorted(used)}', flush=True)
