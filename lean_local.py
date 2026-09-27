#!/usr/bin/env python3
"""Use the workspace's pinned Lean 4.32.0 and read-only Mathlib cache."""
from pathlib import Path
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
WORKSPACE = ROOT.parents[1]
GENERATION = WORKSPACE / 'rethlas/agents/generation'
RUNTIME = GENERATION / 'tmp/lean-4.32.0-us1emG/lean-4.32.0-darwin_aarch64/bin'
MATHLIB = GENERATION / 'tmp/mathlib4-4.32.0'
PACKAGES = GENERATION / 'results/endpoint_entropy_energy_d_2_to_10/lean_d3_d9_full/.lake/packages'
search = [ROOT / '.lake/build/lib/lean', MATHLIB / '.lake/build/lib/lean']
search += sorted(PACKAGES.glob('*/.lake/build/lib/lean'))
env = dict(os.environ)
env['PATH'] = str(RUNTIME) + os.pathsep + env.get('PATH', '')
env['LEAN_PATH'] = os.pathsep.join(map(str, search))
args = sys.argv[1:]
tool = 'lean'
if args and args[0] == '--kernel':
    tool, args = 'leanchecker', args[1:]
if tool == 'lean':
    args = ['-j', '1', *args]
raise SystemExit(subprocess.call([str(RUNTIME / tool), *args], cwd=ROOT, env=env))
