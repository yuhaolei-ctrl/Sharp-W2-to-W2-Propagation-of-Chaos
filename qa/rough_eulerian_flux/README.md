# Rough finite-action measurable-flux bridge

All five new `RoughEulerianTransport*.lean` modules compile cleanly and independently replay through Lean's kernel. All 47 inspected declarations (including the continuity-equation structure constructor/projections) depend only on `propext`, `Classical.choice`, and `Quot.sound`. `verification.json` records source/object hashes and statuses; compile/kernel logs and `axioms.log` are retained. Reproduce with `python3 qa/rough_eulerian_flux/verify.py`. The five source files are now frozen.

The single final import is `SharpWasserstein.RoughEulerianTransportContinuity`.

## What is proved

The final theorem `RoughEulerianTransport.exists_flux_of_finite_tangent_energy` constructs an actual strongly measurable field U(t,x) in L²(dt⊗μ_t), with

    ∫∫ |U(t,x)|² dμ_t dt ≤ ∫ energy(μ_t,σ_t) dt,

and, for every actual compact smooth spatial test φ and 0≤a≤b≤T,

    ∫φ dμ_b − ∫φ dμ_a = ∫_a^b ∫ gradient φ · U(t,x) dμ_t dt.

The scalar source σ_t is a linear functional on the existing genuine `WeightedTangent.Test` space. The energy is the existing actual weighted compact-test supremum, not a scalar proxy. The divergence sign is σ=−div(μ U). All norms are full Euclidean norms, with constant one and no dimension or particle-number loss.

Crucially, no measurability of the timewise canonical vector representatives is assumed. The construction instead takes one Riesz representative in the L² space of the actual joint measure. Measurable-time localized compact tests belong to its test space, so the pairing theorem really yields the original interval continuity equation. Singular spatial laws are permitted.

## Exact hypotheses

* T≥0 and a narrowly continuous curve μ:ℝ→ProbabilityMeasure(Point d).
* The genuine scalar compact-test continuity equation, encoded as `CompactDistributionContinuity μ σ T`, with its interval integrability requirement.
* Almost everywhere finite `WeightedTangent.FiniteEnergy (μ t) (σ t)` on [0,T].
* Integrability of its real energy over [0,T].

The more general `exists_measurable_finiteAction_flux` accepts any integrable majorant E of every genuine pointwise quadratic test objective. It keeps the integrated bound ∫E unchanged. No moment bound is needed for this measurable-flux result itself.

`RoughEulerianTransportEnergy` additionally proves lower semicontinuity and measurability of the actual extended energy from narrow law continuity and continuity of every scalar source pairing. When the energy is finite everywhere, its real version is measurable. These energy theorems also avoid any vector-field measurability assumption.

`RoughEulerianTransportKernel` derives a genuine Markov kernel from a narrowly continuous probability curve using bounded continuous approximations to closed-set indicators. Its measurability is proved, not included as a new hypothesis.

## Main APIs

* `probabilityCurveKernel`, `measurable_measure_of_continuous_probability`
* `spaceTimeFlux_pairing`, `spaceTimeFlux_energy_le`
* `spaceTimeFlux_localized_pairing`, `spaceTimeFlux_set_pairing`
* `lowerSemicontinuous_extendedEnergy`, `measurable_extendedEnergy`, `measurable_finite_energy`
* `curveFlux_stronglyMeasurable`, `curveFlux_energy_le`, `curveFlux_continuity_equation`
* `exists_measurable_finiteAction_flux`, `exists_flux_of_finite_tangent_energy`

All are in namespace `SharpWasserstein.RoughEulerianTransport`.

## Remaining transport work

This is the measurable-flux bridge, not the rough W₂ length theorem. The existing `EulerianTransportCompact` theorem still requires smooth, jointly continuous, uniformly bounded/Lipschitz velocities with derivative bounds. No use of that theorem for the rough U is asserted here.

A viable next construction is to extend compact-test continuity to bounded smooth tests by cutoffs and L² domination, compress space by smooth Euclidean contractions into compact sets, smooth the resulting laws and flux jointly in space/time, and add a small stationary positive reference density. The smoothed velocity ratio must be proved to meet the existing smooth theorem's global bounds; plain Gaussian convolution alone does not guarantee these bounds. Weighted Cauchy–Schwarz should give the exact action contraction. Actual endpoint couplings and a limiting argument must then pass the Wasserstein estimate to the original curve.

The present horizon requires ∫E<∞. The manuscript's E(s) behaving like 1/s near zero does not satisfy that hypothesis on [0,T]. Applying this construction on positive-time subintervals, proving the length estimate there, and using the already established endpoint continuity is the intended route. A weighted time reparametrization would be another route, but is not proved here. Genuine marginal-source linkage and the sharp marginal energy bound remain separate from this group.
