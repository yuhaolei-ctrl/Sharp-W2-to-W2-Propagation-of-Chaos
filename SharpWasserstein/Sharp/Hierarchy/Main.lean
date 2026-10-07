/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import SharpWasserstein.Sharp.Hierarchy.Profile
public import SharpWasserstein.BrownianEnergyPeriodization

/-!
# Proposition 3.7: the sharp profile of the propagated source

Let `a`, `K` be smooth coefficients satisfying Assumption A with the Euclidean constants
`L_a, L₁, L₂, M` (`IsSmoothCoefficients`). Let `ρ_{N,0}` be an exchangeable law of `N` particles,
`V` a square-integrable permutation-equivariant field, and let `E_k(r)` be the tangent energy of
the `k`-th marginal of the source `σ_{N,r}` obtained by transporting `-div(ρ_{N,0} V)` with the
linearized particle flow (`eq:propagated`). Proposition 3.7 (`prop:profile`) states:
if `E_k(0) ≤ A k²/N²` for `1 ≤ k ≤ N`, then `E_k(r) ≤ A e^{ωr} k²/N²` for `r ≥ 0`, with
`ω = D + 3λ`, `D = 2Λ + 2L₁ + 1`, `λ = 2G`, `G = 2L₁² + L₂² + 2M²`, `Λ = L_a + L₁ + L₂`.

In the development the energy `E_k(r)` is `BrownianEnergyPeriodization.prefixEnergy`: the full
Euclidean tangent energy of the `k`-th marginal of the Brownian-propagated source of the initial
field `u`, for the dynamics driven by the kernel `kernelOf a K`. The main theorem
`prefixEnergy_quadratic_bound_sharp` bounds exactly this object, so that it replaces the
development's `BrownianEnergyPeriodization.prefixEnergy_quadratic_bound` (whose rate was
`4 · comparisonConstant d M L₁ L₂`, depending on the dimension and on sup-norm constants).

The proof follows the route of the development: the coefficients are replaced by their sine
periodizations, which keep the Euclidean constants (`SplitKernel.sine`); for periodic
coefficients the hierarchy of Section 5 is proved for the periodic tangent energies of every
period multiple (`brownian_periodic_omega_bound_initial_flux`), and the full energy is the limit
over period multiples (`full_energy_le_of_split_periods`); finally the bound passes to the
original coefficients by the convergence of the sine-periodized flows and the lower
semicontinuity of the energy (`BrownianEnergyPeriodization.prefixEnergy_le_of_sine_bounds`). The
qualitative sup-norm bounds `Mb, Lb₁, Lb₂` on the kernel, needed to form the objects, do not
enter the estimate.

## Main statements

* `full_energy_le_of_split_periods`: recovery of the full energy from periodic energies.
* `periodic_prefixEnergy_omega_bound`: Proposition 3.7 for periodic coefficients.
* `prefixEnergy_quadratic_bound_sharp_of_splitKernel`, `prefixEnergy_quadratic_bound_sharp`:
  Proposition 3.7.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace NNReal

namespace SharpWasserstein.Sharp.Hierarchy

open WeightedTangent PropagatedSourceEquation PeriodicParticleTangentLimit InitialSourceMarginal
open BrownianPeriodicHierarchy PropagatedSourcePermutation NoiseAverage BrownianEnergyPeriodization

/-- The full tangent energy is at most `C` as soon as every periodic energy, for every period
`Q > 0` shared by `a` and `K`, is at most `C`. Only the multiples of one common period `P` are
used (Appendix A, through the compression argument of the development). -/
theorem full_energy_le_of_split_periods {d n : ℕ} [MeasurableSpace (Point n)]
    [BorelSpace (Point n)] {a : Position d → Position d}
    {K : Position d → Position d → Position d} {P : ℝ} (hP : 0 < P)
    (ha : ∀ i x, a (x + Pi.single i P) = a x)
    (hx : ∀ i x y, K (x + Pi.single i P) y = K x y)
    (hy : ∀ i x y, K x (y + Pi.single i P) = K x y)
    (μ : Measure (Point n)) [IsFiniteMeasure μ] (σ : Test n →ₗ[ℝ] ℝ)
    (hσ : FiniteEnergy μ σ) {C : ℝ}
    (hC : ∀ Q : ℝ, 0 < Q →
      (∀ i x, a (x + Pi.single i Q) = a x) →
      (∀ i x y, K (x + Pi.single i Q) y = K x y) →
      (∀ i x y, K x (y + Pi.single i Q) = K x y) →
      WeightedPeriodicTangentPhysical.energy Q μ σ ≤ C) : energy μ σ ≤ C := by
  apply PeriodicEnergyExhaustion.full_energy_le_of_periodic_multiples μ σ hσ
    (A := P / (2 * Real.pi)) (div_pos hP (mul_pos (by norm_num) Real.pi_pos))
  intro j
  have hmul : 2 * Real.pi * (P / (2 * Real.pi) * ((j : ℝ) + 1)) = ((j + 1 : ℕ) : ℝ) * P := by
    push_cast
    field_simp
  rw [hmul]
  exact hC _ (mul_pos (by positivity) hP)
    (fun i x => KernelPeriodMultiples.first (b := oneBodyKernel a) (fun i x _ => ha i x)
      (j + 1) i x x)
    (KernelPeriodMultiples.first hx (j + 1)) (KernelPeriodMultiples.second hy (j + 1))

variable {d N : ℕ} {a : Position d → Position d} {K : Position d → Position d → Position d}
  {La L₁ L₂ M : ℝ} {Mb Lb₁ Lb₂ : ℝ}
  (hN : 0 < N) (hb : BoundedSmoothKernel (kernelOf a K))
  (hbound : KernelBounds (kernelOf a K) Mb Lb₁ Lb₂)
  (hMb : 0 ≤ Mb) (hLb₁ : 0 ≤ Lb₁) (hLb₂ : 0 ≤ Lb₂) {T : ℝ} (hT : 0 ≤ T)
  (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ] (hμ : HasSecondMoment μ)
  {u : Point (N*d) → Point (N*d)} (hu : MemLp u 2 (μ.map (configurationEuclidean d N)))

include hμ in
/-- **Proposition 3.7 for periodic coefficients.** If `a` and `K` have a common coordinate
period, the full Euclidean energy of the `k`-th marginal of the propagated source satisfies
`E_k(t) ≤ A e^{ωt} k²/N²`. -/
theorem periodic_prefixEnergy_omega_bound {P A : ℝ} (hP : 0 < P)
    (hex : Exchangeable μ)
    (hue : ∀ e : Equiv.Perm (Fin N), ∀ᵐ x ∂μ.map (configurationEuclidean d N),
      u (euclideanPermutation e x) = euclideanPermutation e (u x))
    (hA : 0 ≤ A) (h : SplitKernel a K La L₁ L₂ M)
    (ha : ∀ i x, a (x + Pi.single i P) = a x)
    (hx : ∀ i x y, K (x + Pi.single i P) y = K x y)
    (hy : ∀ i x y, K x (y + Pi.single i P) = K x y)
    (σ₀ : Test (N*d) →ₗ[ℝ] ℝ)
    (hσ₀ : ∀ φ : Test (N*d), σ₀ φ =
      ∫ x, ⟪gradient φ.val x, u x⟫_ℝ ∂μ.map (configurationEuclidean d N))
    (hinit : ∀ k, 1 ≤ k → k ≤ N →
      energy (levelLaw d N (μ.map (configurationEuclidean d N)) k)
        (levelSource d N (μ.map (configurationEuclidean d N)) σ₀ k) ≤
          A * (k : ℝ) ^ 2 / (N : ℝ) ^ 2)
    {k : ℕ} (hkpos : 1 ≤ k) (hk : k ≤ N) {t : ℝ} (ht : t ∈ Icc 0 T) :
    prefixEnergy hN hb hbound hMb hLb₁ hLb₂ hT (μ.map (configurationEuclidean d N)) hk u hu t ≤
      A * Real.exp (omega La L₁ L₂ M * t) * (k : ℝ) ^ 2 / (N : ℝ) ^ 2 := by
  let ν := carryingLaw hN hb hbound hMb hLb₁ hLb₂ hT (μ.map (configurationEuclidean d N)) t
  let σ := propagatedSource hN hb hbound hMb hLb₁ hLb₂ hT (μ.map (configurationEuclidean d N))
    u hu t
  change energy (ν.map (marginalProjection hk)) (imageSource ν σ (marginalProjection hk)) ≤ _
  apply full_energy_le_of_split_periods hP ha hx hy (ν.map (marginalProjection hk))
    (imageSource ν σ (marginalProjection hk)) (imageSource_finite _ _ _)
  intro Q hQ haQ hxQ hyQ
  have hh := brownian_periodic_omega_bound_initial_flux (M₀ := ⟨Mb, hMb⟩)
    ((particleDrift_lipschitz hN hb hbound hLb₁ hLb₂).continuous.comp continuous_snd)
    (fun _ => particleDrift_norm_bound hN hbound hMb)
    (fun _ => particleDrift_lipschitz hN hb hbound hLb₁ hLb₂)
    ((drift_lipschitz hN hb hbound hLb₁ hLb₂).continuous.comp continuous_snd)
    (fun _ => drift_norm_le hN hbound hMb) (fun _ => drift_lipschitz hN hb hbound hLb₁ hLb₂)
    hT hb μ hμ hu hQ hN hex hue h haQ hxQ hyQ hA σ₀ hσ₀ hinit k hkpos hk t ht
  simpa only [brownianPeriodicEnergy, levelLaw, levelSource, levelProjection_eq hk,
    ν, σ, carryingLaw, propagatedSource] using hh

include hμ in
/-- **Proposition 3.7 (`prop:profile`)** for a split pair `(a, K)`: the full Euclidean tangent
energy `E_k(t)` of the `k`-th marginal of the source propagated from an exchangeable law and an
equivariant initial field, whose initial marginal energies are at most `A k²/N²`, satisfies
`E_k(t) ≤ A e^{ωt} k²/N²` with `ω = D + 3λ`. -/
theorem prefixEnergy_quadratic_bound_sharp_of_splitKernel (h : SplitKernel a K La L₁ L₂ M)
    (hex : Exchangeable μ)
    (hue : ∀ e : Equiv.Perm (Fin N), ∀ᵐ x ∂μ.map (configurationEuclidean d N),
      u (euclideanPermutation e x) = euclideanPermutation e (u x))
    {A : ℝ} (hA : 0 ≤ A) (σ₀ : Test (N*d) →ₗ[ℝ] ℝ)
    (hσ₀ : ∀ φ : Test (N*d), σ₀ φ =
      ∫ x, ⟪gradient φ.val x, u x⟫_ℝ ∂μ.map (configurationEuclidean d N))
    (hinit : ∀ k, 1 ≤ k → k ≤ N →
      energy (levelLaw d N (μ.map (configurationEuclidean d N)) k)
        (levelSource d N (μ.map (configurationEuclidean d N)) σ₀ k) ≤
          A * (k : ℝ) ^ 2 / (N : ℝ) ^ 2)
    {k : ℕ} (hkpos : 1 ≤ k) (hk : k ≤ N) {t : ℝ} (ht : t ∈ Icc 0 T) :
    prefixEnergy hN hb hbound hMb hLb₁ hLb₂ hT (μ.map (configurationEuclidean d N)) hk u hu t ≤
      A * Real.exp (omega La L₁ L₂ M * t) * (k : ℝ) ^ 2 / (N : ℝ) ^ 2 := by
  have : IsProbabilityMeasure (μ.map (configurationEuclidean d N)) :=
    Measure.isProbabilityMeasure_map
      (configurationEuclidean d N).continuous.measurable.aemeasurable
  apply prefixEnergy_le_of_sine_bounds hN hb hbound hMb hLb₁ hLb₂ hT
    (μ.map (configurationEuclidean d N)) hk u hu ht
  apply Eventually.of_forall
  intro n
  have hR : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  exact periodic_prefixEnergy_omega_bound (a := a ∘ SinePeriodization.coordinates ((n : ℝ) + 1))
    (K := SinePeriodization.kernel ((n : ℝ) + 1) K) hN
    (PeriodicParticle.interaction_smooth hb n)
    (PeriodicParticle.interaction_bounds hb hbound hLb₁ hLb₂ n) hMb hLb₁ hLb₂ hT μ hμ hu
    (P := 2 * Real.pi * ((n : ℝ) + 1)) (by positivity) hex hue hA (h.sine hR)
    (sine_oneBody_periodic hR.ne' a)
    (SinePeriodization.kernel_periodic_first hR.ne' K)
    (SinePeriodization.kernel_periodic_second hR.ne' K)
    σ₀ hσ₀ hinit hkpos hk ht

include hμ in
/-- **Proposition 3.7 (`prop:profile`).** Let `a`, `K` be smooth coefficients with the
Euclidean constants `L_a, L₁, L₂, M` of Assumption A, driving the particle system through the
kernel `kernelOf a K` (with any admissible qualitative sup-norm bounds `Mb, Lb₁, Lb₂`). Let `μ`
be an exchangeable law with finite second moment and `u` a square-integrable equivariant field,
whose source `σ₀ = -div(μ u)` has marginal energies `E_k(0) ≤ A k²/N²`. Then the full Euclidean
tangent energy of the `k`-th marginal of the propagated source satisfies
`E_k(t) ≤ A e^{ωt} k²/N²` for `0 ≤ t ≤ T`, with `ω = D + 3λ` (`omega La L₁ L₂ M`).

This is a drop-in replacement for `BrownianEnergyPeriodization.prefixEnergy_quadratic_bound`
(for `b = kernelOf a K`): it bounds the same object and takes the same arguments, with the
additional hypothesis `hS` right after `hu`; the rate `4 · comparisonConstant d Mb Lb₁ Lb₂` is
replaced by `omega La L₁ L₂ M`, which does not involve the sup-norm data `Mb, Lb₁, Lb₂`. -/
theorem prefixEnergy_quadratic_bound_sharp (hS : IsSmoothCoefficients a K La L₁ L₂ M)
    (hex : Exchangeable μ)
    (hue : ∀ e : Equiv.Perm (Fin N), ∀ᵐ x ∂μ.map (configurationEuclidean d N),
      u (euclideanPermutation e x) = euclideanPermutation e (u x))
    {A : ℝ} (hA : 0 ≤ A) (σ₀ : Test (N*d) →ₗ[ℝ] ℝ)
    (hσ₀ : ∀ φ : Test (N*d), σ₀ φ =
      ∫ x, ⟪gradient φ.val x, u x⟫_ℝ ∂μ.map (configurationEuclidean d N))
    (hinit : ∀ k, 1 ≤ k → k ≤ N →
      energy (levelLaw d N (μ.map (configurationEuclidean d N)) k)
        (levelSource d N (μ.map (configurationEuclidean d N)) σ₀ k) ≤
          A * (k : ℝ) ^ 2 / (N : ℝ) ^ 2)
    {k : ℕ} (hkpos : 1 ≤ k) (hk : k ≤ N) {t : ℝ} (ht : t ∈ Icc 0 T) :
    prefixEnergy hN hb hbound hMb hLb₁ hLb₂ hT (μ.map (configurationEuclidean d N)) hk u hu t ≤
      A * Real.exp (omega La L₁ L₂ M * t) * (k : ℝ) ^ 2 / (N : ℝ) ^ 2 :=
  prefixEnergy_quadratic_bound_sharp_of_splitKernel hN hb hbound hMb hLb₁ hLb₂ hT μ hμ hu
    (SplitKernel.of_smooth hS) hex hue hA σ₀ hσ₀ hinit hkpos hk ht

end SharpWasserstein.Sharp.Hierarchy
