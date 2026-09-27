#!/usr/bin/env python3
"""Compile missing Mathlib dependency closures into a copy-on-write overlay.

Usage: python3 scripts/bootstrap_mathlib.py Mathlib.Analysis.ODE.Gronwall
The external pinned cache is read-only. Existing artifacts are symlinked locally.
Each compiled source and SHA-256 is recorded in qa/mathlib_dependencies.json.
Recursive imports are built before their users. An advisory file lock serializes
overlay and ledger writes across concurrent callers. Use --dry-run to list the
uncached dependency closure without modifying the overlay or ledger.
"""
from pathlib import Path
import argparse
import fcntl
import hashlib
import json
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
MATHLIB = ROOT.parents[1] / "rethlas/agents/generation/tmp/mathlib4-4.32.0"
SOURCE_CACHE = MATHLIB / ".lake/build/lib/lean"
LOCAL_CACHE = ROOT / ".lake/build/lib/lean"
VENDORED_SOURCE = ROOT / "vendor/mathlib"


def module_source(relative: Path) -> tuple[Path, Path]:
    """Allow explicit locally recorded proof repairs without mutating upstream."""
    vendored = VENDORED_SOURCE / relative.with_suffix(".lean")
    return (vendored, VENDORED_SOURCE) if vendored.is_file() else (
        MATHLIB / relative.with_suffix(".lean"), MATHLIB)


def real_directory(relative: Path) -> None:
    """Expand just one overlay directory; leave all of its children as links."""
    target = LOCAL_CACHE / relative
    if target.is_symlink():
        target.unlink()
    target.mkdir(parents=True, exist_ok=True)
    source = SOURCE_CACHE / relative
    if source.exists():
        for child in source.iterdir():
            link = target / child.name
            if not link.exists() and not link.is_symlink():
                link.symlink_to(child, target_is_directory=child.is_dir())


def imports(source: Path) -> list[str]:
    """Read imports after removing nested Lean comments and line comments."""
    text = source.read_text()
    clean, pos, depth = [], 0, 0
    while pos < len(text):
        if text.startswith("/-", pos):
            depth += 1
            pos += 2
        elif depth and text.startswith("-/", pos):
            depth -= 1
            pos += 2
        elif not depth and text.startswith("--", pos):
            end = text.find("\n", pos)
            pos = len(text) if end == -1 else end
        else:
            clean.append(text[pos] if not depth or text[pos] == "\n" else " ")
            pos += 1
    if depth:
        raise ValueError(f"Unclosed Lean comment in {source}")
    return [module for line in "".join(clean).splitlines()
            if (match := re.match(r"^\s*(?:(?:public|private)\s+)?import\s+(.+)$", line))
            for module in match.group(1).split() if module.startswith("Mathlib.")]


def run(modules: list[str], dry_run: bool) -> None:
    record_path = ROOT / "qa/mathlib_dependencies.json"
    old = json.loads(record_path.read_text()) if record_path.exists() else []
    records = old if isinstance(old, list) else [old]
    seen, visiting, plan = set(), set(), []

    def visit(module: str) -> None:
        if module in seen:
            return
        if module in visiting:
            raise ValueError(f"Cyclic Lean imports at {module}")
        parts = module.split(".")
        if parts[0] != "Mathlib" or not all(p.isidentifier() for p in parts):
            raise ValueError(f"Expected a Mathlib module name: {module}")
        relative = Path(*parts)
        source, source_root = module_source(relative)
        if not source.is_file():
            raise FileNotFoundError(source)
        output = LOCAL_CACHE / relative.with_suffix(".olean")
        external = SOURCE_CACHE / relative.with_suffix(".olean")
        source_hash = hashlib.sha256(source.read_bytes()).hexdigest()
        valid_local = output.is_file() and any(
            r.get("module") == module and r.get("sha256") == source_hash
            for r in records)
        # The pinned external cache is trusted as a dependency-closed build.
        # Locally compiled files require a matching source hash in our ledger.
        if (external.is_file() and source_root == MATHLIB) or valid_local:
            seen.add(module)
            return
        visiting.add(module)
        for dependency in imports(source):
            visit(dependency)
        visiting.remove(module)
        seen.add(module)
        plan.append(module)

    for module in modules:
        visit(module)
    print(f"Missing Mathlib modules: {len(plan)}", flush=True)
    if dry_run:
        print("\n".join(plan), flush=True)
        return
    real_directory(Path("Mathlib"))
    for index, module in enumerate(plan, 1):
        print(f"[{index}/{len(plan)}] Compiling {module}", flush=True)
        parts = module.split(".")
        relative = Path(*parts)
        source, source_root = module_source(relative)
        source_hash = hashlib.sha256(source.read_bytes()).hexdigest()
        output = LOCAL_CACHE / relative.with_suffix(".olean")
        for depth in range(1, len(parts)):
            real_directory(Path(*parts[:depth]))
        for suffix in [".olean", ".olean.server", ".olean.private", ".ilean", ".ir"]:
            artifact = LOCAL_CACHE / relative.with_suffix(suffix)
            if artifact.is_symlink():
                artifact.unlink()
        args = [sys.executable, str(ROOT / "lean_local.py"), "-R", str(source_root),
                "-o", str(output), str(source)]
        subprocess.run(args, cwd=ROOT, check=True)
        records = [r for r in records if r.get("module") != module]
        record = {
            "module": module, "source": str(source),
            "sha256": source_hash,
            "command": f"python3 scripts/bootstrap_mathlib.py {module}",
            "compiler_command": args,
            "cache_overlay": "Copy-on-write directories with external-cache symlink children; external artifacts remain unchanged."
        }
        if source_root == VENDORED_SOURCE:
            upstream = MATHLIB / relative.with_suffix(".lean")
            record["upstream_source"] = str(upstream)
            record["upstream_sha256"] = hashlib.sha256(upstream.read_bytes()).hexdigest()
            record["source_patch_ledger"] = "qa/mathlib_source_patches.json"
        records.append(record)
        record_path.parent.mkdir(exist_ok=True)
        temporary = record_path.with_suffix(".json.tmp")
        temporary.write_text(json.dumps(records, indent=2) + "\n")
        temporary.replace(record_path)
    for module in modules:
        print(f"Ready: {module}", flush=True)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("modules", nargs="*")
    options = parser.parse_args()
    modules = options.modules or [
        "Mathlib.Analysis.ODE.Gronwall",
        "Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym",
        "Mathlib.MeasureTheory.Measure.Tilted",
        "Mathlib.MeasureTheory.Measure.LogLikelihoodRatio",
    ]
    if options.dry_run:
        run(modules, dry_run=True)
        return
    lock_path = ROOT / "qa/mathlib_bootstrap.lock"
    lock_path.parent.mkdir(exist_ok=True)
    with lock_path.open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        run(modules, dry_run=False)


if __name__ == "__main__":
    main()
