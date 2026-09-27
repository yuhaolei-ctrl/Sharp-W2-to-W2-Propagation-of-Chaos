#!/usr/bin/env python3
"""Audit component proofs and, when present, the exact original main target.

Run after `python3 build.py --fresh --replay`. The scan covers the umbrella and
all .lean files below SharpWasserstein/, not Mathlib, generated qa files, or
Python tooling. Nested comments and string literals are removed before token
checks. This small declaration extractor supports the simple namespace/section
syntax used by this project; unsupported private declarations fail closed.
"""

from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
MANUSCRIPT = ROOT.parents[1] / "rethlas/manuscripts/sharp_wasserstein_bounded_kernel_open/sharp_wasserstein_propagation.tex"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = ("sorry", "admit", "axiom", "unsafe", "native_decide")
IDENT = r"[^\s(){}\[\]:,;=]+"
TOKEN_RE = re.compile(r"(?<![\w'])" + "(?:" + "|".join(FORBIDDEN) + r")(?![\w'])")
COMMAND_RE = re.compile(
    r"^\s*(?:@\[[^\]\n]*\]\s*)*"
    r"(?P<mods>(?:(?:private|protected|noncomputable|partial|public)\s+)*)"
    r"(?P<kind>namespace|section|end|theorem|lemma|def|abbrev|structure|inductive|opaque)"
    r"(?:\s+(?P<name>" + IDENT + r"))?"
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def strip_lean_noncode(source: str) -> str:
    """Replace comments/strings by spaces, preserving offsets and line numbers."""
    out = list(source)
    size = len(source)

    def erase(start: int, end: int) -> None:
        for pos in range(start, end):
            if source[pos] not in "\r\n":
                out[pos] = " "

    i = 0
    while i < size:
        if source.startswith("--", i):
            end = source.find("\n", i)
            if end < 0:
                end = size
            erase(i, end)
            i = end
        elif source.startswith("/-", i):
            start, depth = i, 1
            i += 2
            while i < size and depth:
                if source.startswith("/-", i):
                    depth += 1
                    i += 2
                elif source.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise ValueError("Unterminated nested Lean comment")
            erase(start, i)
        else:
            raw = re.match(r'r(#+)"', source[i:]) if source[i] == "r" else None
            if raw and (i == 0 or not (source[i - 1].isalnum() or source[i - 1] == "_")):
                start = i
                closing = '"' + raw.group(1)
                end = source.find(closing, i + len(raw.group(0)))
                if end < 0:
                    raise ValueError("Unterminated raw Lean string")
                i = end + len(closing)
                erase(start, i)
            elif source[i] == '"':
                start = i
                i += 1
                while i < size:
                    if source[i] == "\\":
                        i += 2
                    elif source[i] == '"':
                        i += 1
                        break
                    else:
                        i += 1
                else:
                    raise ValueError("Unterminated Lean string")
                erase(start, min(i, size))
            else:
                i += 1
    return "".join(out)


def declarations(clean: str, relative_path: str) -> list[dict]:
    """Extract named declarations, tracking sections separately from namespaces."""
    frames: list[tuple[str, str, str]] = []
    namespace = ""
    found = []
    for lineno, line in enumerate(clean.splitlines(), 1):
        match = COMMAND_RE.match(line)
        if not match:
            continue
        kind, name = match.group("kind"), match.group("name") or ""
        mods = match.group("mods").split()
        if kind in {"namespace", "section"}:
            if kind == "namespace" and not name:
                raise ValueError(f"{relative_path}:{lineno}: unnamed namespace")
            frames.append((kind, name, namespace))
            if kind == "namespace":
                namespace = name.removeprefix("_root_.") if name.startswith("_root_.") else \
                    ".".join(filter(None, (namespace, name)))
        elif kind == "end":
            if not frames:
                raise ValueError(f"{relative_path}:{lineno}: unmatched end")
            frame_kind, frame_name, previous_namespace = frames.pop()
            if name and name != frame_name:
                raise ValueError(f"{relative_path}:{lineno}: end {name} closes {frame_kind} {frame_name}")
            namespace = previous_namespace
        else:
            if not name:
                raise ValueError(f"{relative_path}:{lineno}: unnamed {kind}")
            if "private" in mods:
                raise ValueError(f"{relative_path}:{lineno}: private declarations need a kernel-name extractor")
            full = name.removeprefix("_root_.") if name.startswith("_root_.") else \
                ".".join(filter(None, (namespace, name)))
            found.append({"name": full, "kind": kind, "source": relative_path, "line": lineno})
    if any(kind == "namespace" for kind, _, _ in frames):
        raise ValueError(f"{relative_path}: unclosed namespace in simple declaration extractor")
    return found


def parse_axioms(output: str) -> dict[str, list[str]]:
    result: dict[str, list[str]] = {}
    pattern = re.compile(
        r"'(?P<name>[^\n]+?)'\s+(?:depends on axioms:\s*\[(?P<axioms>[^\]]*)\]"
        r"|does not depend on any axioms)", re.MULTILINE
    )
    for match in pattern.finditer(output):
        name = match.group("name")
        if name in result:
            raise ValueError(f"Duplicate axiom output for {name}")
        result[name] = [item.strip() for item in (match.group("axioms") or "").split(",") if item.strip()]
    return result


def self_test() -> None:
    fixture = '''/- sorry /- admit -/ axiom -/
namespace Example
section Inner
@[simp] theorem check : True := by trivial -- native_decide
end Inner
def text := "unsafe \\\" sorry -- /-"
def raw := r##"axiom " sorry"##
def danger : True := by sorry
end Example
'''
    clean = strip_lean_noncode(fixture)
    assert len(clean) == len(fixture)
    assert clean.count("\n") == fixture.count("\n")
    assert [m.group() for m in TOKEN_RE.finditer(clean)] == ["sorry"]
    ds = declarations(clean, "fixture.lean")
    assert [d["name"] for d in ds] == ["Example.check", "Example.text", "Example.raw", "Example.danger"]
    assert parse_axioms("'Example.check' depends on axioms: [propext,\n Classical.choice]\n"
                        "'Example.text' does not depend on any axioms\n") == {
                            "Example.check": ["propext", "Classical.choice"], "Example.text": []}
    assert parse_axioms("'Example.name\u0027' depends on axioms: [Quot.sound]\n") == {
        "Example.name\u0027": ["Quot.sound"]}
    for invalid in ("/- never closed", '"never closed'):
        try:
            strip_lean_noncode(invalid)
        except ValueError:
            pass
        else:
            raise AssertionError("Malformed non-code was not rejected")
    print("Scanner, namespace/section extraction, and axiom-output self-tests passed.")


def audit(report: dict, checked_closure: bool = False, require_main: bool = False) -> None:
    umbrella = ROOT / "SharpWasserstein.lean"
    if not umbrella.exists():
        raise ValueError("Umbrella SharpWasserstein.lean does not exist; build the complete component closure first")
    report["provenance"] = {
        "manuscript": {"path": str(MANUSCRIPT), "sha256": sha256(MANUSCRIPT)},
        "lean_toolchain": {"path": "lean-toolchain", "sha256": sha256(ROOT / "lean-toolchain"),
                           "contents": (ROOT / "lean-toolchain").read_text().strip()},
        "lakefile": {"path": "lakefile.toml", "sha256": sha256(ROOT / "lakefile.toml")},
    }
    all_sources = [umbrella, *sorted((ROOT / "SharpWasserstein").rglob("*.lean"))]
    sources = all_sources
    if checked_closure:
        checkpoint_manifest = json.loads((ROOT / "qa/build_SharpWasserstein.json").read_text())
        selected = {entry["module"] for entry in checkpoint_manifest["modules"]}
        sources = [p for p in all_sources if str(p.relative_to(ROOT)).removesuffix(".lean").replace("/", ".") in selected]
        report["unverified_project_sources"] = [str(p.relative_to(ROOT)) for p in all_sources if p not in sources]
        report["audit_scope"] = "Only the source-hash-matched, kernel-replayed umbrella closure; all listed unverified sources are excluded"
    report["scanner_scope"] = {
        "included": [str(p.relative_to(ROOT)) for p in sources],
        "excluded": ["Mathlib and external dependencies", "qa generated Lean files", "Python tooling"],
        "method": "Token scan after removing nested /- -/ comments, -- comments, and string literals",
        "forbidden_tokens": list(FORBIDDEN),
        "limitations": "Simple project syntax only; this lexical scan is not a Lean parser. Kernel axiom inspection is a separate check.",
    }
    all_declarations = []
    modules: dict[str, list[str]] = {}
    report["sources"] = []
    forbidden_hits = []
    for path in sources:
        relative = str(path.relative_to(ROOT))
        text = path.read_text()
        clean = strip_lean_noncode(text)
        module = relative.removesuffix(".lean").replace("/", ".")
        modules[module] = re.findall(r"^\s*import\s+(SharpWasserstein(?:\.[\w]+)*)", clean, re.MULTILINE)
        ds = declarations(clean, relative)
        all_declarations.extend(ds)
        report["sources"].append({"path": relative, "sha256": sha256(path),
                                  "declaration_counts": dict(Counter(d["kind"] for d in ds))})
        for match in TOKEN_RE.finditer(clean):
            forbidden_hits.append({"source": relative, "line": clean.count("\n", 0, match.start()) + 1,
                                   "token": match.group()})
    report["forbidden_token_hits"] = forbidden_hits
    if forbidden_hits:
        raise ValueError("Forbidden Lean tokens found in executable project source")
    names = [d["name"] for d in all_declarations]
    duplicates = [name for name, count in Counter(names).items() if count != 1]
    if duplicates:
        raise ValueError("Duplicate extracted declaration names: " + ", ".join(duplicates))
    targets = [d for d in all_declarations if d["name"] == "SharpWasserstein.MainTheorem"]
    if len(targets) != 1 or targets[0]["kind"] != "def":
        raise ValueError("MainTheorem must remain exactly one def declaration of the original proposition")
    main_proofs = [d for d in all_declarations if d["name"] == "SharpWasserstein.main_theorem"]
    if require_main and (len(main_proofs) != 1 or main_proofs[0]["kind"] != "theorem"):
        raise ValueError("The exact main_theorem proof is required in the audited closure")
    main_present = len(main_proofs) == 1 and main_proofs[0]["kind"] == "theorem"
    report["main_target"] = {**targets[0], "proof_status": "pending exact type check" if main_present else "open proposition; no proof asserted"}
    visited = set()

    def visit(module: str) -> None:
        if module in visited:
            return
        if module not in modules:
            raise ValueError(f"Missing local source for {module}")
        visited.add(module)
        for dependency in modules[module]:
            visit(dependency)

    visit("SharpWasserstein")
    if visited != set(modules):
        raise ValueError("Umbrella omits project modules: " + ", ".join(sorted(set(modules) - visited)))
    stale = []
    for path in sources:
        compiled = ROOT / ".lake/build/lib/lean" / path.relative_to(ROOT).with_suffix(".olean")
        if not compiled.exists() or compiled.stat().st_mtime_ns < path.stat().st_mtime_ns:
            stale.append(str(path.relative_to(ROOT)))
    report["stale_or_missing_compiled_sources"] = stale
    if stale:
        raise ValueError("Build current sources before axiom inspection: " + ", ".join(stale))
    build_manifest = ROOT / "qa/build_SharpWasserstein.json"
    if not build_manifest.exists():
        raise ValueError("Missing umbrella build manifest; run python3 build.py --fresh --replay")
    if build_manifest.exists():
        manifest = json.loads(build_manifest.read_text())
        entries = {entry["module"]: entry for entry in manifest.get("modules", [])}
        hashes_match = all(entries.get(module, {}).get("source_sha256") == sha256(
            ROOT.joinpath(*module.split(".")).with_suffix(".lean")) for module in modules)
        report["build_manifest"] = {"path": str(build_manifest.relative_to(ROOT)),
                                    "sha256": sha256(build_manifest), "status": manifest.get("status"),
                                    "all_source_hashes_match": hashes_match,
                                    "all_modules_kernel_replayed": all(
                                        entries.get(module, {}).get("replay_exit_code") == 0 for module in modules)}
        if manifest.get("status") != "passed" or not hashes_match:
            raise ValueError("Existing umbrella build report is failed or does not match current source hashes")
        if not report["build_manifest"]["all_modules_kernel_replayed"]:
            raise ValueError("Independent kernel replay must have succeeded for every project module")
    version = subprocess.run([sys.executable, str(ROOT / "lean_local.py"), "--version"],
                             cwd=ROOT, capture_output=True, text=True)
    report["lean_version"] = version.stdout.strip()
    if version.returncode:
        raise ValueError("Could not query the pinned Lean version: " + version.stderr)
    audit_path = ROOT / ("qa/CheckpointAxiomAudit.lean" if checked_closure else "qa/AxiomAudit.lean")
    target_check = ("example : SharpWasserstein.MainTheorem := SharpWasserstein.main_theorem\n\n"
                    if main_present else "")
    audit_path.write_text("import SharpWasserstein\n\n" + target_check + "\n".join(
        "#print axioms " + declaration["name"] for declaration in all_declarations) + "\n")
    command = [sys.executable, str(ROOT / "lean_local.py"), str(audit_path)]
    compilation = subprocess.run(command, cwd=ROOT, stdout=subprocess.PIPE,
                                 stderr=subprocess.STDOUT, text=True)
    log_path = ROOT / ("qa/checkpoint_axiom_audit.log" if checked_closure else "qa/axiom_audit.log")
    log_path.write_text(compilation.stdout)
    report["axiom_inspection"] = {"command": command, "exit_code": compilation.returncode,
                                 "generated_source": str(audit_path.relative_to(ROOT)),
                                 "source_sha256": sha256(audit_path),
                                 "log": str(log_path.relative_to(ROOT)),
                                 "allowed_axioms": sorted(ALLOWED_AXIOMS)}
    if compilation.returncode:
        raise ValueError("Lean axiom inspection failed; see qa/axiom_audit.log")
    parsed = parse_axioms(compilation.stdout)
    missing = sorted(set(names) - set(parsed))
    unexpected_names = sorted(set(parsed) - set(names))
    if missing or unexpected_names:
        raise ValueError(f"Incomplete axiom output: missing={missing}; unexpected={unexpected_names}")
    unexpected_axioms = {name: sorted(set(axioms) - ALLOWED_AXIOMS)
                        for name, axioms in parsed.items() if set(axioms) - ALLOWED_AXIOMS}
    report["axiom_inspection"]["unexpected_axioms"] = unexpected_axioms
    report["declaration_counts"] = dict(Counter(d["kind"] for d in all_declarations))
    report["audited_declaration_count"] = len(all_declarations)
    report["source_file_count"] = len(sources)
    report["declarations"] = [{**d, "axioms": parsed[d["name"]]} for d in all_declarations]
    if unexpected_axioms:
        raise ValueError("Unexpected axioms found in project declarations")
    for entry in report["sources"]:
        if sha256(ROOT / entry["path"]) != entry["sha256"]:
            raise ValueError("Project source changed during audit: " + entry["path"])
    if main_present:
        snapshot_path = ROOT / "qa/manuscript_coverage_snapshot_2026-09-17.json"
        snapshot = json.loads(snapshot_path.read_text())
        review_path = ROOT / "qa/manuscript_coverage_audit_2026-09-17.md"
        statement_review = ROOT / "qa/main_statement_review.md"
        if snapshot["manuscript_sha256"] != sha256(MANUSCRIPT) or snapshot["audit_sha256"] != sha256(review_path):
            raise ValueError("The manuscript or its independent correspondence review changed after review")
        original_checkpoint = json.loads((ROOT / "qa/history/verification_checkpoint_before_main_completion_2026-09-17.json").read_text())
        original_target = next(entry for entry in original_checkpoint["sources"]
                               if entry["path"] == "SharpWasserstein/Dynamics.lean")
        if original_target["sha256"] != sha256(ROOT / original_target["path"]):
            raise ValueError("The original Dynamics/MainTheorem source was changed")
        report["main_target"].update({
            "proof_status": "proved; exact original proposition type-checked",
            "proof_declaration": main_proofs[0],
            "exact_type_check": target_check.strip(),
            "axioms": parsed["SharpWasserstein.main_theorem"],
            "original_target_source_unchanged": True,
            "original_target_source_sha256": original_target["sha256"],
        })
        report["complete_main_theorem_proof"] = True
        report["manuscript_correspondence"] = {
            "scope": "The original propagation estimate and revised proof lemmas; cited nonlinear existence theory is background, not part of the Lean target",
            "review": "qa/manuscript_coverage_audit_2026-09-17.md",
            "statement_review": "qa/main_statement_review.md",
            "review_sha256": sha256(review_path),
            "statement_review_sha256": sha256(statement_review),
            "snapshot_sha256": sha256(snapshot_path),
            "reviewed_manuscript_sha256": snapshot["manuscript_sha256"],
        }
    report["status"] = "passed_main_theorem_audit" if main_present else "passed_component_audit"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true", help="test the scanner/parser only; do not inspect Lean modules")
    parser.add_argument("--checked-closure", action="store_true", help="audit only the last checked umbrella closure and explicitly list excluded in-progress files; write a separate checkpoint report")
    parser.add_argument("--require-main", action="store_true", help="fail unless the original MainTheorem has an audited theorem proof of exactly that type")
    args = parser.parse_args()
    if args.self_test:
        self_test()
        return 0
    qa = ROOT / "qa"
    qa.mkdir(exist_ok=True)
    report = {"status": "running", "complete_main_theorem_proof": False,
              "audit_scope": "Project declarations and exact original MainTheorem proof, if present; prose correspondence is reviewed separately",
              "timestamp_utc": datetime.now(timezone.utc).isoformat(),
              "audit_script_sha256": sha256(Path(__file__))}
    try:
        audit(report, checked_closure=args.checked_closure, require_main=args.require_main)
    except (ValueError, OSError, KeyError, json.JSONDecodeError) as error:
        report["status"] = "failed"
        report["error"] = str(error)
        print("Audit failed: " + str(error), file=sys.stderr)
    (qa / ("verification_checkpoint.json" if args.checked_closure else "verification.json")).write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    if report["status"] not in {"passed_component_audit", "passed_main_theorem_audit"}:
        return 1
    result = ("the exact original MainTheorem is proved with standard axioms only."
              if report["complete_main_theorem_proof"] else "the original MainTheorem remains unproved.")
    print(f"Audit passed for {report['audited_declaration_count']} declarations; " + result)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
