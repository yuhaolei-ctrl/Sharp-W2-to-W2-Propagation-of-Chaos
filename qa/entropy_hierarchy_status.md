# Entropy hierarchy formalization

`SharpWasserstein/EntropyHierarchy.lean` compiles without warnings and passes
independent `leanchecker` replay.

Commands run:

```text
python3 lean_local.py -o .lake/build/lib/lean/SharpWasserstein/EntropyHierarchy.olean SharpWasserstein/EntropyHierarchy.lean
python3 lean_local.py --kernel -v SharpWasserstein.EntropyHierarchy
```

The sequence is `h : ℕ → ℝ`, with increment `h (m + 1) - h m`.
`FiniteEntropyConditions h N` states `h 0 = 0`, a nonnegative first
increment, and monotone increments for indices below `N`.

The module proves block telescoping and entropy nonnegativity; the bounds
`δ_(m+1) ≤ h_(2m)/m` when `0 < m` and `2*m ≤ N`, and
`δ_(m+1) ≤ h_N/(N-m)` when `m < N`; the external bound
`((N-m)/N)^2*m*δ_(m+1) ≤ 4*A*m^2/N^2` for `1 ≤ m ≤ N` from
`N > 0`, `A ≥ 0`, and the all-level quadratic entropy profile; and the
algebraic internal and combined source estimates.

The composed theorem `source_energy_from_entropy_profile` additionally assumes
the scalar bounds on the internal energy `I`, external energy `X`, and total
energy `E` delivered by the bounded-sum, conditional Pinsker, and
squared-velocity arguments. It derives
`E ≤ 2*C*(1+5*A)*m^2/N^2` for `C ≥ 0`.

This module does **not** prove that a sequence of probabilistic relative
entropies satisfies `FiniteEntropyConditions`; it does **not** formalize the
entropy chain rule, conditional mutual information, Pinsker, or Hoeffding.

Axiom inspection of the low/high increment, uniform external, and composed
source theorems reports only `propext`, `Classical.choice`, and `Quot.sound`.
No new axioms, `sorry`, or `native_decide` are used.
