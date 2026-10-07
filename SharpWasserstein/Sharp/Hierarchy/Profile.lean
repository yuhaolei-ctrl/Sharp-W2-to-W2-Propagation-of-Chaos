/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import SharpWasserstein.Sharp.Hierarchy.FiniteHierarchy
public import SharpWasserstein.Sharp.Hierarchy.Comparison
public import SharpWasserstein.BrownianPeriodicHierarchyInitial

/-!
# The profile bound for periodic coefficients

This file assembles Lemma 5.3 (`FiniteHierarchy`), Proposition 5.4 and Section 5.4
(`Comparison`) for the Brownian particle flow of the development, when `a` and `K` share a
coordinate period `P`. The energies are the periodic tangent energies (tests of period `P`) of the
marginals of the propagated source; the passage to the full energies is in
`SharpWasserstein.Sharp.Hierarchy.Main`.

This is the analogue of `BrownianPeriodicHierarchy.brownian_periodic_quadratic_bound` of the
development, with the sharp rate `ω = D + 3λ` of the paper in place of `4 · comparisonConstant`.

## Main statements

* `brownianFiniteEnergy_deriv_le_sharp`, `brownianFiniteEnergy_terminal_deriv_le_sharp`:
  Lemma 5.3 for the Galerkin energies of the exhaustion of the development.
* `brownian_periodic_omega_bound`, `brownian_periodic_omega_bound_initial_flux`: Proposition 3.7
  for the periodic energies.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace NNReal

namespace SharpWasserstein.Sharp.Hierarchy

open WeightedTangent PropagatedSourceEquation NoiseAverage PeriodicParticleTangentLimit
open PeriodicMarginalCoefficientEvolution RegularizedTrialConvergence BrownianPeriodicHierarchy
open PropagatedSourcePermutation VolterraFourier

variable {d N : ℕ} {a : Position d → Position d} {K : Position d → Position d → Position d}
  {La L₁ L₂ M : ℝ} {M₀ K₀ M' K' : ℝ≥0}
  (hv : Continuous (Function.uncurry
    (fun _ : ℝ => (particleDrift (kernelOf a K) : Configuration d N → _))))
  (hb : ∀ _ : ℝ, ∀ x : Configuration d N, ‖particleDrift (kernelOf a K) x‖ ≤ M₀)
  (hl : ∀ _ : ℝ, LipschitzWith K₀ (particleDrift (kernelOf a K) : Configuration d N → _))
  (hv' : Continuous (Function.uncurry
    (fun _ : ℝ => equivDrift (configurationEuclidean d N) (particleDrift (kernelOf a K)))))
  (hb' : ∀ _ : ℝ, ∀ y,
    ‖equivDrift (configurationEuclidean d N) (particleDrift (kernelOf a K)) y‖ ≤ M')
  (hl' : ∀ _ : ℝ,
    LipschitzWith K' (equivDrift (configurationEuclidean d N) (particleDrift (kernelOf a K))))
  {T : ℝ} (hT : 0 ≤ T) (hbs : BoundedSmoothKernel (kernelOf a K))
  (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ] (hμ : HasSecondMoment μ)
  {u : Point (N*d) → Point (N*d)} (hu : MemLp u 2 (μ.map (configurationEuclidean d N)))

include hv hb hl hμ in
/-- **Lemma 5.3** (`m < N`) for the Galerkin energies `ε_{m,j}` of the exhaustion, as ordinary
derivatives on `(0, T)`. -/
theorem brownianFiniteEnergy_deriv_le_sharp {P : ℝ} (hP : 0 < P) {m : ℕ}
    (hm : m < N) (hmpos : 1 ≤ m) (hex : Exchangeable μ)
    (hue : ∀ e : Equiv.Perm (Fin N), ∀ᵐ x ∂μ.map (configurationEuclidean d N),
      u (euclideanPermutation e x) = euclideanPermutation e (u x))
    (h : SplitKernel a K La L₁ L₂ M)
    (ha : ∀ i x, a (x + Pi.single i P) = a x)
    (hx : ∀ i x y, K (x + Pi.single i P) y = K x y)
    (hy : ∀ i x y, K x (y + Pi.single i P) = K x y)
    (j : ℕ) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    deriv (brownianFiniteEnergy hv' hb' hl' hT hbs μ hu P m j) t ≤
      driftRate La L₁ L₂ * brownianFiniteEnergy hv' hb' hl' hT hbs μ hu P m j t +
      jumpRate L₁ L₂ M N m * (brownianPeriodicEnergy hv' hb' hl' hT hbs μ hu P (m + 1) t -
        brownianFiniteEnergy hv' hb' hl' hT hbs μ hu P m j t) +
      gapConstant N h m * (brownianPeriodicEnergy hv' hb' hl' hT hbs μ hu P m t -
        brownianFiniteEnergy hv' hb' hl' hT hbs μ hu P m j t) := by
  obtain ⟨e', he, hi⟩ := brownian_trialEnergy_derivative_le_sharp hv hb hl hv' hb' hl' hT hbs μ
    hμ hu hP hm hmpos hex hue h ha hx hy (exhaustion ((Fin (m*d) → ℤ) × Bool) j) (penalty_pos j)
    ⟨ht.1.le, ht.2.le⟩
  have hd : HasDerivAt (brownianFiniteEnergy hv' hb' hl' hT hbs μ hu P m j) e' t := by
    apply (he.congr_of_mem (fun r _ => ?_) ⟨ht.1.le, ht.2.le⟩).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)
    exact sourceFiniteEnergy_level_eq P hm.le _ _ j r
  rw [hd.deriv]
  dsimp only at hi
  rw [observed_nextEnergy hm] at hi
  simpa only [brownianFiniteEnergy, sourceFiniteEnergy_level_eq P hm.le,
    brownianPeriodicEnergy, periodicEnergy_level_eq P hm.le,
    periodicEnergy_level_eq P (Nat.succ_le_of_lt hm)] using hi

include hv hb hl hμ in
/-- **Lemma 5.3** at the top level `m = N`. -/
theorem brownianFiniteEnergy_terminal_deriv_le_sharp {P : ℝ} (hP : 0 < P) (hN : 1 ≤ N)
    (h : SplitKernel a K La L₁ L₂ M)
    (ha : ∀ i x, a (x + Pi.single i P) = a x)
    (hx : ∀ i x y, K (x + Pi.single i P) y = K x y)
    (hy : ∀ i x y, K x (y + Pi.single i P) = K x y)
    (j : ℕ) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    deriv (brownianFiniteEnergy hv' hb' hl' hT hbs μ hu P N j) t ≤
      driftRate La L₁ L₂ * brownianFiniteEnergy hv' hb' hl' hT hbs μ hu P N j t +
      gapConstant N h N * (brownianPeriodicEnergy hv' hb' hl' hT hbs μ hu P N t -
        brownianFiniteEnergy hv' hb' hl' hT hbs μ hu P N j t) := by
  obtain ⟨e', he, hi⟩ := brownian_trialEnergy_terminal_derivative_le_sharp hv hb hl hv' hb' hl'
    hT hbs μ hμ hu hP hN h ha hx hy (exhaustion ((Fin (N*d) → ℤ) × Bool) j) (penalty_pos j)
    ⟨ht.1.le, ht.2.le⟩
  have hd : HasDerivAt (brownianFiniteEnergy hv' hb' hl' hT hbs μ hu P N j) e' t := by
    apply (he.congr_of_mem (fun r _ => ?_) ⟨ht.1.le, ht.2.le⟩).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)
    exact sourceFiniteEnergy_level_eq P le_rfl _ _ j r
  rw [hd.deriv]
  dsimp only at hi
  simpa only [brownianFiniteEnergy, sourceFiniteEnergy_level_eq P (le_rfl : N ≤ N),
    brownianPeriodicEnergy, periodicEnergy_level_eq P (le_rfl : N ≤ N)] using hi

include hv hb hl hμ in
/-- **Proposition 3.7 for periodic coefficients and periodic energies.** If the marginal
energies of the propagated source at time `0` satisfy `E_m(0) ≤ A m²/N²`, then the periodic
marginal energies satisfy `E_m(t) ≤ A e^{ωt} m²/N²` on `[0, T]`, with `ω = D + 3λ`. -/
theorem brownian_periodic_omega_bound {P : ℝ} (hP : 0 < P) (hN : 0 < N)
    (hex : Exchangeable μ)
    (hue : ∀ e : Equiv.Perm (Fin N), ∀ᵐ x ∂μ.map (configurationEuclidean d N),
      u (euclideanPermutation e x) = euclideanPermutation e (u x))
    (h : SplitKernel a K La L₁ L₂ M)
    (ha : ∀ i x, a (x + Pi.single i P) = a x)
    (hx : ∀ i x y, K (x + Pi.single i P) y = K x y)
    (hy : ∀ i x y, K x (y + Pi.single i P) = K x y)
    {A : ℝ} (hA : 0 ≤ A)
    (hinit : ∀ m, 1 ≤ m → m ≤ N →
      let ν := Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) 0
      let σ := Brownian.sourceAt hv' hb' hl' hT (particleDrift_smooth hbs)
        (particleDrift_allDerivativesBounded hbs) (μ.map (configurationEuclidean d N)) u hu 0
      WeightedTangent.energy (levelLaw d N ν m) (levelSource d N ν σ m) ≤
        A * (m : ℝ) ^ 2 / (N : ℝ) ^ 2) :
    ∀ m, 1 ≤ m → m ≤ N → ∀ t ∈ Icc 0 T,
      brownianPeriodicEnergy hv' hb' hl' hT hbs μ hu P m t ≤
        A * Real.exp (omega La L₁ L₂ M * t) * (m : ℝ) ^ 2 / (N : ℝ) ^ 2 := by
  let ν := fun r => Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) r
  let σ := fun r => Brownian.sourceAt hv' hb' hl' hT (particleDrift_smooth hbs)
    (particleDrift_allDerivativesBounded hbs) (μ.map (configurationEuclidean d N)) u hu r
  let B := Real.exp ((K' : ℝ) * T) ^ 2 * (∫ x, ‖u x‖ ^ 2 ∂(μ.map (configurationEuclidean d N)))
  have hh := source_omega_bound_of_finite_derivatives P
    (fun m r => levelLaw d N (ν r) m) (fun m r => levelSource d N (ν r) (σ r) m)
    hN hA (driftRate_le_omega La L₁ L₂ M) hT
    (jumpRate L₁ L₂ M N) (gapConstant N h)
    (fun m _ hm => jumpRate_nonneg L₁ L₂ M hm.le)
    (fun m hm1 hm => profile_supersolution La L₁ L₂ M hm1 hm.le)
    (fun _ _ _ _ _ => levelSource_finite _ _ _ _ _)
    (fun m _ hm j => brownianFiniteEnergy_continuousOn hv hb hl hv' hb' hl' hT hbs μ hμ hu hP hm j)
    (f' := fun m j => deriv (brownianFiniteEnergy hv' hb' hl' hT hbs μ hu P m j))
    (fun m _ hm j r hr =>
      brownianFiniteEnergy_hasDerivAt hv hb hl hv' hb' hl' hT hbs μ hμ hu hP hm j hr)
    (B := fun _ _ => B) (fun _ _ _ => intervalIntegrable_const)
    (fun m _ _ r hr => (brownian_level_energy_bound_flux hv' hb' hl' hT
      (particleDrift_smooth hbs) (particleDrift_allDerivativesBounded hbs)
      (μ.map (configurationEuclidean d N)) u hu m hr).2)
    (fun m hmpos hm j r hr => brownianFiniteEnergy_deriv_le_sharp hv hb hl hv' hb' hl' hT hbs μ
      hμ hu hP hm hmpos hex hue h ha hx hy j hr)
    (fun j r hr => brownianFiniteEnergy_terminal_deriv_le_sharp hv hb hl hv' hb' hl' hT hbs μ hμ
      hu hP hN h ha hx hy j hr)
    hinit
  intro m hm hmN t ht
  have h' := hh m hm hmN t ht
  simp only [sub_zero] at h'
  convert h' using 1
  rfl

include hv hb hl hμ in
/-- **Proposition 3.7 for periodic coefficients and periodic energies**, with the initial source
given as the distribution of an initial field `u`, as in the development. -/
theorem brownian_periodic_omega_bound_initial_flux {P : ℝ} (hP : 0 < P) (hN : 0 < N)
    (hex : Exchangeable μ)
    (hue : ∀ e : Equiv.Perm (Fin N), ∀ᵐ x ∂μ.map (configurationEuclidean d N),
      u (euclideanPermutation e x) = euclideanPermutation e (u x))
    (h : SplitKernel a K La L₁ L₂ M)
    (ha : ∀ i x, a (x + Pi.single i P) = a x)
    (hx : ∀ i x y, K (x + Pi.single i P) y = K x y)
    (hy : ∀ i x y, K x (y + Pi.single i P) = K x y)
    {A : ℝ} (hA : 0 ≤ A) (σ₀ : Test (N*d) →ₗ[ℝ] ℝ)
    (hσ₀ : ∀ φ : Test (N*d), σ₀ φ =
      ∫ x, ⟪gradient φ.val x, u x⟫_ℝ ∂μ.map (configurationEuclidean d N))
    (hinit : ∀ m, 1 ≤ m → m ≤ N →
      energy (levelLaw d N (μ.map (configurationEuclidean d N)) m)
        (levelSource d N (μ.map (configurationEuclidean d N)) σ₀ m) ≤
          A * (m : ℝ) ^ 2 / (N : ℝ) ^ 2) :
    ∀ m, 1 ≤ m → m ≤ N → ∀ t ∈ Icc 0 T,
      brownianPeriodicEnergy hv' hb' hl' hT hbs μ hu P m t ≤
        A * Real.exp (omega La L₁ L₂ M * t) * (m : ℝ) ^ 2 / (N : ℝ) ^ 2 := by
  apply brownian_periodic_omega_bound hv hb hl hv' hb' hl' hT hbs μ hμ hu hP hN hex hue h
    ha hx hy hA
  intro m hm hmN
  dsimp only
  rw [Brownian.sourceAt_zero_of_divergence hv' hb' hl' hT
    (particleDrift_smooth hbs) (particleDrift_allDerivativesBounded hbs) _ hu σ₀ hσ₀]
  exact (levelEnergy_measure_congr _ _ (Brownian.lawAt_zero hv' hb' hl' hT _) σ₀ m).trans_le
    (hinit m hm hmN)

end SharpWasserstein.Sharp.Hierarchy
