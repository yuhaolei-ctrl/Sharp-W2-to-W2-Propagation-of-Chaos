# Sharp Wasserstein propagation: Lean proof

`SharpWasserstein.main_theorem : SharpWasserstein.MainTheorem` proves the
original finite-horizon propagation estimate. The original proposition in
`Dynamics.lean` is unchanged. Its conclusion constant is chosen before the
interaction kernel, supplied reference evolution, and particle family.

The proof retains correlated exchangeable P₂ initial data, the all-level
initial Wasserstein hierarchy, self-interaction, sqrt(2) Brownian noise,
and the unnormalized Euclidean quadratic transport cost. No initial entropy,
transport inequality, density regularity, or independent initial particles
are assumed.

The final audit passed for **512 source files / 3,776 named declarations**:
compilation, independent kernel replay, exact original target type, and
standard-axiom closure. There are no proof placeholders or new axioms.

The actual main proof is in [Main.lean](SharpWasserstein/Main.lean).
[THEOREM_STATUS.md](THEOREM_STATUS.md) maps the revised manuscript's statements
to their Lean proofs. [CHANGELOG.md](CHANGELOG.md) records substantive changes.

The accompanying manuscript is kept in the research workspace at
`rethlas/manuscripts/sharp_wasserstein_lean_proof/`; it is not part of this
Lean repository.

## Reproduce

The workspace pins Lean 4.32.0 and Mathlib commit
`887cc46427636bbdd235160a112f9a30ae81d040`.

```sh
cd sharp_wasserstein
python3 build.py --fresh --replay --jobs 2
python3 scripts/audit.py --require-main
```

For incremental recompilation, omit `--fresh`. The independent kernel replay
still checks every module in the complete umbrella closure. The audit requires
an exact type check of `main_theorem` against the original `MainTheorem`, scans
all project Lean sources for proof placeholders and new axioms, and checks the
transitive axioms of every named declaration. Only `propext`, `Classical.choice`,
and `Quot.sound` are allowed.

The final full audit is [qa/verification.json](qa/verification.json); the
corresponding compile/kernel manifest is
[qa/build_SharpWasserstein.json](qa/build_SharpWasserstein.json). Earlier
checkpoint and scoped reports are retained as historical records; their
incomplete-status fields describe those earlier snapshots.

`lean_local.py` and `lakefile.toml` use the original workspace's Lean and
Mathlib cache under `rethlas/agents/generation/`. A fresh clone needs that
workspace layout and its pinned dependencies before the commands above can
run. Bootstrap scripts build missing Mathlib modules in a local overlay and
replay the pinned external Brownian/Kolmogorov closure. Provenance and
licenses are retained under `external_sources/`. The repository includes
source and audit records, not a standalone Lean runtime or compiled cache.

## Scope

The rate theorem concerns the supplied weak particle and McKean–Vlasov
probability solutions in the manuscript. Actual Brownian particle construction,
linear weak uniqueness, reference-law identification, moments, and all proof
estimates are formalized. General nonlinear McKean–Vlasov existence theory is
cited background in the note and is not a separate formalized conclusion.

The revised auxiliary lemmas use exactly the hypotheses supplied by the proof:
bounded jointly continuous entropy-cost drifts, a genuine common-label
realization for rough finite-action transport, and an equivariant initial
representing field for tangent propagation. The interpolation's common labels
and current equivariance are themselves proved; neither is added to the main
theorem's assumptions.
