#!/usr/bin/env python3
"""Reproduce the frozen weighted periodic marginal group's kernel/axiom audit."""
import hashlib, importlib.util, json, pathlib, re, subprocess, sys
ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = ROOT / "qa" / "weighted_periodic_marginal"
MODS = ["WeightedPeriodicMarginal"]
OUT.mkdir(exist_ok=True)
spec = importlib.util.spec_from_file_location("audit", ROOT / "scripts" / "audit.py")
audit = importlib.util.module_from_spec(spec); spec.loader.exec_module(audit)
lines = ["import SharpWasserstein." + m for m in MODS]
records = []
for m in MODS:
    source = ROOT / "SharpWasserstein" / (m + ".lean")
    declarations = audit.declarations(audit.strip_lean_noncode(source.read_text()), str(source))
    lines += ["#print axioms " + d["name"] for d in declarations]
    records.append({"module": m, "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(), "declarations": len(declarations)})
(OUT / "Axioms.lean").write_text("\n".join(lines) + "\n")
for record in records:
    command = [sys.executable, "lean_local.py", "--kernel", "SharpWasserstein." + record["module"]]
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    (OUT / (record["module"] + ".kernel.log")).write_text(result.stdout + result.stderr)
    record["kernel_exit"] = result.returncode
    if result.returncode:
        raise SystemExit(result.returncode)
command = [sys.executable, "lean_local.py", str(OUT / "Axioms.lean")]
result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
log = result.stdout + result.stderr
(OUT / "axioms.log").write_text(log)
assert result.returncode == 0, log
axioms = {a.strip() for block in re.findall(r"\[(.*?)\]", log, re.S) for a in block.split(",")}
assert axioms <= {"propext", "Classical.choice", "Quot.sound"}, axioms
assert log.count("depends on axioms:") == sum(r["declarations"] for r in records)
manifest = {"modules": records, "declarations": sum(r["declarations"] for r in records), "axioms": sorted(axioms), "axiom_audit_exit": result.returncode, "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip()}
(OUT / "verification.json").write_text(json.dumps(manifest, indent=2) + "\n")
print(json.dumps(manifest, indent=2))
