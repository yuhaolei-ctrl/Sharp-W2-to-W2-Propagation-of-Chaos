import SharpWasserstein.InitialSourceMarginalCurrent
import SharpWasserstein.InitialSourceMarginalPrefix
import SharpWasserstein.RegularizedSourceRates

/-! One regularized full discrepancy distribution has the sharp all-level
initial energy profile. Marginal compatibility is proved from its actual
cylinder action before any independently obtained energy estimate is used. -/
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff BigOperators NNReal ENNReal
namespace SharpWasserstein.InitialSourceMarginal
open WeightedTangent InitialSourcePermutation DecoupledFlow
variable {d : ℕ} {v : ℝ → Position d → Position d} {M K L : ℝ≥0} {s U : ℝ}
  (hv : Continuous (Function.uncurry v)) (hb : ∀ t x,‖v t x‖ ≤ M)
  (hl : ∀ t,LipschitzWith K (v t))

/-- The full regularized source is chosen once. Every genuine canonical-source
marginal, including the full level, satisfies the common quadratic initial
profile with the explicit horizon constant. -/
theorem exists_regularized_consistent_source {N : ℕ} {B C₀ : ℝ}
    (hN : 0 < N) (P : Measure (Configuration d N)) [IsProbabilityMeasure P]
    (r : Measure (Position d)) [IsProbabilityMeasure r]
    (hP : HasSecondMoment P) (hr : Integrable positionSq r) (hex : Exchangeable P)
    (he : ∀ t,LipschitzWith L (GaussianBridge.euclideanDrift v t))
    (hs : 0 < s) (hsU : s ≤ U) (hC₀ : 0 ≤ C₀)
    (hinit : ∀ j,∀ hj : j ≤ N,wassersteinSq (marginal hj P) (tensorLaw r j) ≤
      ENNReal.ofReal (C₀*(j:ℝ)^2/(N:ℝ)^2))
    {b : Position d → Position d → Position d} (hB : 0 ≤ B)
    (hbmeas : Measurable (Function.uncurry b)) (hbnd : ∀ u w a,|b u w a| ≤ B) :
    let R := brownianLaw hv hb hl hs.le P
    let q := singleBrownianLaw hv hb hl hs.le r
    ∃ σ : ConfigurationTest d N →ₗ[ℝ] ℝ,
      (∀ φ : ConfigurationTest d N,σ φ = ∫ x,
        generator (fun z i => nonlinearDrift b q (z i)) φ.val x -
          generator (particleDrift b) φ.val x ∂R) ∧
      ConfigurationFiniteEnergy R σ ∧
      ∀ m,∀ _hm0 : 0 < m,∀ hm : m ≤ N,
        ConfigurationFiniteEnergy (marginal hm R) (configurationMarginalSource hm R σ) ∧
        configurationTangentEnergy (marginal hm R) (configurationMarginalSource hm R σ) ≤
          RegularizationRates.sourceHorizonConstant d B C₀ L U*(1+1/s)*(m:ℝ)^2/(N:ℝ)^2 := by
  dsimp only
  obtain ⟨σ,hσ,hfinite,hfull⟩ := exists_regularized_full_source hv hb hl hN P r hP hr he hs hC₀ hinit hB hbmeas hbnd
  refine ⟨σ,hσ,hfinite,fun m hm0 hm => ⟨configurationMarginalSource_finite hm _ σ,?_⟩⟩
  by_cases hmN : m=N
  · subst m
    rw [configurationMarginalSource_self _ _ b σ hσ
      (initialCurrent_memLp hN _ _ hbmeas hbnd),marginal_self]
    have hrate := RegularizationRates.full_source_coefficient_le_singular
      (d := d) hB hC₀ L.coe_nonneg hs hsU
    have hNr : (N:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    simpa only [mul_div_cancel_right₀ _ (pow_ne_zero 2 hNr)] using hfull.trans hrate
  · have hlt : m<N := lt_of_le_of_ne hm hmN
    obtain ⟨ζ,hζ,hζfinite,hζbound⟩ := exists_regularized_marginal_source hv hb hl hm0 hlt
      P r hP hr hex he hs hC₀ hinit hB hbmeas hbnd
    have hid := configurationMarginalSource_eq hlt _
      (brownianLaw_exchangeable hv hb hl hs.le P hex) _ hB hbmeas hbnd σ hσ ζ hζ
    rw [hid]
    apply hζbound.trans
    have hrate := RegularizationRates.source_coefficient_le_singular
      (d := d) hB hC₀ L.coe_nonneg hs hsU
    gcongr

/-- The same one-source profile stated literally for the existing weighted
`marginalDistribution`, after arithmetic coordinate reindexing only. -/
theorem exists_regularized_weighted_marginal_profile {N : ℕ} {B C₀ : ℝ}
    (hN : 0 < N) (P : Measure (Configuration d N)) [IsProbabilityMeasure P]
    (r : Measure (Position d)) [IsProbabilityMeasure r]
    (hP : HasSecondMoment P) (hr : Integrable positionSq r) (hex : Exchangeable P)
    (he : ∀ t,LipschitzWith L (GaussianBridge.euclideanDrift v t))
    (hs : 0 < s) (hsU : s ≤ U) (hC₀ : 0 ≤ C₀)
    (hinit : ∀ j,∀ hj : j ≤ N,wassersteinSq (marginal hj P) (tensorLaw r j) ≤
      ENNReal.ofReal (C₀*(j:ℝ)^2/(N:ℝ)^2))
    {b : Position d → Position d → Position d} (hB : 0 ≤ B)
    (hbmeas : Measurable (Function.uncurry b)) (hbnd : ∀ u w a,|b u w a| ≤ B) :
    let R := brownianLaw hv hb hl hs.le P
    let q := singleBrownianLaw hv hb hl hs.le r
    ∃ σ : ConfigurationTest d N →ₗ[ℝ] ℝ,
      (∀ φ : ConfigurationTest d N,σ φ = ∫ x,
        generator (fun z i => nonlinearDrift b q (z i)) φ.val x -
          generator (particleDrift b) φ.val x ∂R) ∧
      ConfigurationFiniteEnergy R σ ∧
      ∀ m,∀ _hm0 : 0 < m,∀ hm : m ≤ N,
        energy (WeightedMarginal.marginalLaw
            ((euclideanLaw R).map (dimensionReindex (d := d) hm)))
          (WeightedMarginal.marginalDistribution
            ((euclideanLaw R).map (dimensionReindex (d := d) hm))
            (imageSource (euclideanLaw R) (euclideanDistribution σ)
              (dimensionReindex (d := d) hm).toContinuousLinearEquiv.toContinuousLinearMap)) ≤
          RegularizationRates.sourceHorizonConstant d B C₀ L U*(1+1/s)*(m:ℝ)^2/(N:ℝ)^2 := by
  obtain ⟨σ,hσ,hfinite,hprofile⟩ := exists_regularized_consistent_source hv hb hl hN P r hP hr hex
    he hs hsU hC₀ hinit hB hbmeas hbnd
  refine ⟨σ,hσ,hfinite,fun m hm0 hm => ?_⟩
  rw [marginal_energy_reindexed_eq]
  exact (hprofile m hm0 hm).2

end SharpWasserstein.InitialSourceMarginal
