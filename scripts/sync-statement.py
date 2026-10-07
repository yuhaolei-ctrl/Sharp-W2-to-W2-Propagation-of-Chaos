#!/usr/bin/env python3
"""Keep the definitions of `Challenge.lean` and `SharpWasserstein/Statement.lean` identical.

Comparator requires every definition reached from a compared statement to be identical in the
Challenge and Solution environments. The Solution obtains these definitions from
`SharpWasserstein.Statement`, which is generated from `Challenge.lean` by dropping the theorems
(the statements with deliberate holes) and replacing the module documentation.

Usage:
  python3 scripts/sync-statement.py          # rewrite SharpWasserstein/Statement.lean
  python3 scripts/sync-statement.py --check  # fail if it is out of date
"""
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
CHALLENGE = ROOT / "Challenge.lean"
STATEMENT = ROOT / "SharpWasserstein" / "Statement.lean"

STATEMENT_DOC = """/-!
# Definitions of the public statement

The definitions used by the statement in `Challenge.lean`, copied verbatim (this file is generated
by `scripts/sync-statement.py`). The development and `Solution.lean` use these declarations, so
that Comparator finds the same definitions in the Challenge and Solution environments.
-/"""


def generate(text: str) -> str:
    # Replace the module documentation (the first `/-! ... -/` block).
    text = re.sub(r"/-!.*?-/", lambda _: STATEMENT_DOC, text, count=1, flags=re.S)
    # Drop every theorem together with its preceding docstring. A theorem runs until the next
    # blank line followed by a top-level command or `end`.
    blocks = re.split(r"\n(?=\n)", text)
    out = []
    for block in blocks:
        body = block.lstrip("\n")
        stripped = re.sub(r"^/--.*?-/\s*", "", body, flags=re.S)
        if stripped.startswith("theorem "):
            continue
        out.append(block)
    return "\n".join(out).rstrip("\n") + "\n"


def main() -> int:
    expected = generate(CHALLENGE.read_text(encoding="utf-8"))
    if "--check" in sys.argv[1:]:
        current = STATEMENT.read_text(encoding="utf-8") if STATEMENT.exists() else ""
        if current != expected:
            print(f"{STATEMENT.relative_to(ROOT)} is out of date; run scripts/sync-statement.py")
            return 1
        print("Statement definitions are in sync with Challenge.lean.")
        return 0
    STATEMENT.write_text(expected, encoding="utf-8")
    print(f"wrote {STATEMENT.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
