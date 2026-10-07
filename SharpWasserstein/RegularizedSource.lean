module

public import SharpWasserstein.Compat
public import SharpWasserstein.RegularizedEntropyProfile
public import SharpWasserstein.MarginalSourceTangent

@[expose] public section

/-! # The actual regularized generator source
The initial Wasserstein profile now yields the real weighted negative-Sobolev
source estimate. No entropy profile, conditional Pinsker inequality, source
energy, or finite KL is assumed. The sign agrees with `(L₀* - Lᴺ*) r`.
-/
noncomputable section
open MeasureTheory InformationTheory
open scoped NNReal ENNReal BigOperators
namespace SharpWasserstein

theorem configurationTestObjective_neg {d N : ℕ} (μ : Measure (Configuration d N))
    (σ : ConfigurationTest d N →ₗ[ℝ] ℝ) (φ : ConfigurationTest d N) :
    configurationTestObjective μ (-σ) φ = configurationTestObjective μ σ (-φ) := by
  unfold configurationTestObjective
  simp only [LinearMap.neg_apply, map_neg]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [coordinateDerivative, Submodule.coe_neg, fderiv_neg,
    neg_apply, neg_sq]

theorem configurationTestObjective_range_neg {d N : ℕ} (μ : Measure (Configuration d N))
    (σ : ConfigurationTest d N →ₗ[ℝ] ℝ) :
    Set.range (configurationTestObjective μ (-σ)) = Set.range (configurationTestObjective μ σ) := by
  ext a
  constructor
  · rintro ⟨φ, rfl⟩
    exact ⟨-φ, (configurationTestObjective_neg μ σ φ).symm⟩
  · rintro ⟨φ, rfl⟩
    refine ⟨-φ, ?_⟩
    rw [configurationTestObjective_neg, neg_neg]

theorem configurationFiniteEnergy_neg_iff {d N : ℕ} (μ : Measure (Configuration d N))
    (σ : ConfigurationTest d N →ₗ[ℝ] ℝ) :
    ConfigurationFiniteEnergy μ (-σ) ↔ ConfigurationFiniteEnergy μ σ := by
  unfold ConfigurationFiniteEnergy
  rw [configurationTestObjective_range_neg]

theorem configurationTangentEnergy_neg {d N : ℕ} (μ : Measure (Configuration d N))
    (σ : ConfigurationTest d N →ₗ[ℝ] ℝ) :
    configurationTangentEnergy μ (-σ) = configurationTangentEnergy μ σ := by
  unfold configurationTangentEnergy
  rw [configurationTestObjective_range_neg]

namespace DecoupledFlow
variable {d : ℕ} {v : ℝ → Position d → Position d} {M K L : ℝ≥0} {T : ℝ}
  (hv : Continuous (Function.uncurry v)) (hb : ∀ t x, ‖v t x‖ ≤ M)
  (hl : ∀ t, LipschitzWith K (v t))

/-- Actual marginal generator source with the sharp quadratic particle profile,
derived directly from the initial transport bound and the constructed Brownian flow. -/
theorem exists_regularized_marginal_source {m N : ℕ} {B C₀ : ℝ}
    [MeasurableSpace (WeightedTangent.Point (m * d))]
    [BorelSpace (WeightedTangent.Point (m * d))]
    (hm0 : 0 < m) (hm : m < N)
    (P : Measure (Configuration d N)) [IsProbabilityMeasure P]
    (r : Measure (Position d)) [IsProbabilityMeasure r]
    (hP : HasSecondMoment P) (hr : Integrable positionSq r) (hex : Exchangeable P)
    (he : ∀ t, LipschitzWith L (GaussianBridge.euclideanDrift v t)) (hT : 0 < T)
    (hC₀ : 0 ≤ C₀)
    (hinit : ∀ j, ∀ hj : j ≤ N, wassersteinSq (marginal hj P) (tensorLaw r j) ≤
      ENNReal.ofReal (C₀ * (j : ℝ)^2 / (N : ℝ)^2))
    {b : Position d → Position d → Position d} (hB : 0 ≤ B)
    (hbmeas : Measurable (Function.uncurry b)) (hbnd : ∀ u w a, |b u w a| ≤ B) :
    let R := brownianLaw hv hb hl hT.le P
    let q := singleBrownianLaw hv hb hl hT.le r
    let H := RegularizationRates.bridgeCost L T * C₀
    ∃ ζ : ConfigurationTest d m →ₗ[ℝ] ℝ,
      (∀ φ : ConfigurationTest d m, ζ φ =
        ∫ x, generator (fun z i => nonlinearDrift b q (z i)) φ.val x -
          generator (fun z i a => marginalScalarDrift hm R b i a z) φ.val x ∂marginal hm.le R) ∧
      ConfigurationFiniteEnergy (marginal hm.le R) ζ ∧
      configurationTangentEnergy (marginal hm.le R) ζ ≤
        (2 * (d * internalSourceConstant B) * (1 + H) + 16 * d * B ^ 2 * H) *
          (m : ℝ)^2 / (N : ℝ)^2 := by
  dsimp only
  have hH : 0 ≤ RegularizationRates.bridgeCost L T * C₀ := by
    unfold RegularizationRates.bridgeCost
    positivity
  obtain ⟨σ, _, hp, hf, hs⟩ := exists_marginalSourceDistribution hm0 hm
    (brownianLaw_exchangeable hv hb hl hT.le P hex)
    (brownianLaw_entropy_finite hv hb hl P r hP hr he hT).ne hH hB hbmeas hbnd
    (regularized_entropy_profile hv hb hl P r hP hr he hT hC₀ hinit)
  refine ⟨-σ, ?_, (configurationFiniteEnergy_neg_iff _ _).mpr hf, ?_⟩
  · intro φ
    rw [LinearMap.neg_apply, hp, ← integral_neg]
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  · rwa [configurationTangentEnergy_neg]

/-- The full-particle source is included, with no artificial (N+1)-particle
conditional law and with its generator sign matching the manuscript. -/
theorem exists_regularized_full_source {N : ℕ} {B C₀ : ℝ}
    [MeasurableSpace (WeightedTangent.Point (N * d))]
    [BorelSpace (WeightedTangent.Point (N * d))]
    (hN : 0 < N)
    (P : Measure (Configuration d N)) [IsProbabilityMeasure P]
    (r : Measure (Position d)) [IsProbabilityMeasure r]
    (hP : HasSecondMoment P) (hr : Integrable positionSq r)
    (he : ∀ t, LipschitzWith L (GaussianBridge.euclideanDrift v t)) (hT : 0 < T)
    (hC₀ : 0 ≤ C₀)
    (hinit : ∀ j, ∀ hj : j ≤ N, wassersteinSq (marginal hj P) (tensorLaw r j) ≤
      ENNReal.ofReal (C₀ * (j : ℝ)^2 / (N : ℝ)^2))
    {b : Position d → Position d → Position d} (hB : 0 ≤ B)
    (hbmeas : Measurable (Function.uncurry b)) (hbnd : ∀ u w a, |b u w a| ≤ B) :
    let R := brownianLaw hv hb hl hT.le P
    let q := singleBrownianLaw hv hb hl hT.le r
    ∃ ζ : ConfigurationTest d N →ₗ[ℝ] ℝ,
      (∀ φ : ConfigurationTest d N, ζ φ =
        ∫ x, generator (fun z i => nonlinearDrift b q (z i)) φ.val x -
          generator (particleDrift b) φ.val x ∂R) ∧
      ConfigurationFiniteEnergy R ζ ∧
      configurationTangentEnergy R ζ ≤
        (d * internalSourceConstant B) * (1 + RegularizationRates.bridgeCost L T * C₀) := by
  dsimp only
  have hH : 0 ≤ RegularizationRates.bridgeCost L T * C₀ := by
    unfold RegularizationRates.bridgeCost
    positivity
  obtain ⟨σ, hp, hf, hs⟩ := exists_fullSourceDistribution hN
    (brownianLaw_entropy_finite hv hb hl P r hP hr he hT).ne hH hB hbmeas hbnd
    (regularized_entropy_profile hv hb hl P r hP hr he hT hC₀ hinit)
  refine ⟨-σ, ?_, (configurationFiniteEnergy_neg_iff _ _).mpr hf, ?_⟩
  · intro φ
    rw [LinearMap.neg_apply, hp, ← integral_neg]
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  · rwa [configurationTangentEnergy_neg]

end DecoupledFlow
end SharpWasserstein
