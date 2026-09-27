# Actual transport convergence of spatial regularization

This scoped checkpoint adds three modules, ending in
`SharpWasserstein.RoughEulerianSmoothingEndpoint`. The earlier five spatial
regularization modules remain frozen and are separately audited under
`qa/rough_eulerian_smoothing`.

`convolvedLaw_eq_map_add` identifies the actual compact-convolution density
law with the law of `X+Z`, with independent original label `X` and normalized
bump noise `Z`. The proof uses nonnegative Tonelli integrals and translation
invariance of the actual Euclidean Lebesgue measure, including singular
original laws.

`convolutionCoupling_isCoupling`, `convolutionCoupling_cost_integrable`, and
`convolutionCoupling_cost_le` construct the actual coupling `(X+Z,X)` and
prove its finite Euclidean cost is at most `ε²`. This part needs only an
original probability law, not its second moment.

`regularizationCoupling_isCoupling` constructs the exact mixture of that
coupling with an independent Gaussian-floor/original coupling. If the original
law has an integrable squared Euclidean norm, the mixture cost is integrable
and `regularizationCoupling_cost_le` proves

```
cost ≤ ε² + δ (2 m₂(GaussianFloorLaw) + 2 m₂(original)).
```

The Gaussian moment is finite by a separately proved integral bound. The
coefficient has no dimension-dependent norm conversion. The original law
need not be compactly supported or smooth.

`wassersteinSq_euclidean_coupling_le` pushes an actual coupling through the
configuration Euclidean equivalence, using the exact full sum-of-squares cost.
`regularizedLaw_wassersteinSq_le` and
`regularizedLaw_wassersteinSq_tendsto` give the actual manuscript transport
distance bound and convergence as `εₙ→0`, `δₙ→0`, with `εₙ>0` and
`0≤δₙ≤1`. The endpoint theorem allows δ=0; the strictly positive floor is only
needed for the smooth velocity construction in the earlier checkpoint.

All functions and coupling measures are explicit. No transport convergence,
coupling identity, or cost bound is assumed. This does not yet prove time
smoothing, its weak equation, or the final rough length estimate.

Run `python3 qa/rough_eulerian_smoothing_endpoint/verify.py` from the project
root. The script recompiles, independently replays kernel objects, checks every
named declaration for only standard axioms, and records source/object hashes.
See `verification.json` and the retained logs for the exact verified scope.
