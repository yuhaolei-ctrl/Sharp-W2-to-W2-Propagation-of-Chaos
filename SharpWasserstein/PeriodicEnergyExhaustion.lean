module

public import SharpWasserstein.Compat
public import SharpWasserstein.CompressionPeriodicTests
public import SharpWasserstein.WeightedGradientApproximation

@[expose] public section

/-! Uniform bounds for arbitrarily large actual physical periods imply the
full Euclidean source energy bound. The proof recovers compact tests by
explicit sine-compressed periodic tests, with dominated gradient convergence.
No finite-period closure is identified with the full gradient closure. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ContDiff Topology InnerProductSpace
namespace SharpWasserstein.PeriodicEnergyExhaustion
open WeightedTangent WeightedPeriodicFourierScale PeriodicBochner
open CompressionPeriodicTests RoughEulerianCompression
variable {n : ℕ} [MeasurableSpace (Point n)] [BorelSpace (Point n)]
  (μ : Measure (Point n)) [IsFiniteMeasure μ]

theorem smooth_periodic_objective_le {P : ℝ} (hP : 0 < P)
    (σ : Test n →ₗ[ℝ] ℝ) {f : Point n → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : PeriodicOf P (f ∘ (coordinateEquiv n).symm)) :
    2*(∫ x,⟪gradient f x,(WeightedTangent.representative μ σ).val x⟫_ℝ ∂μ)-
      (∫ x,‖gradient f x‖^2 ∂μ) ≤ WeightedPeriodicTangentPhysical.energy P μ σ := by
  obtain ⟨g,rfl⟩ := ExternalInteractionPeriodic.exists_physical_test hP f hf hp
  have h := le_csSup (WeightedPeriodicTangentPhysical.objective_bddAbove P μ σ)
    (Set.mem_range_self g)
  change WeightedPeriodicTangentPhysical.objective P μ σ g ≤ _ at h
  have hs := WeightedPeriodicTangentPhysical.source_eq_full_pairing P μ σ g
  rw [real_inner_comm] at hs
  have hp := WeightedPeriodicTangentPhysical.gradientVector_pairing P μ g (WeightedTangent.representative μ σ)
  have hs' := hs.trans hp
  simpa only [WeightedPeriodicTangentPhysical.objective,WeightedPeriodicTangentPhysical.energy,hs'] using h

/-- Bounds with exactly the same constant for all integer multiples of any
positive base period control the actual full compact-test source energy. -/
theorem full_energy_le_of_periodic_multiples (σ : Test n →ₗ[ℝ] ℝ)
    (hσ : FiniteEnergy μ σ) {A C : ℝ} (hA : 0 < A)
    (hC : ∀ j : ℕ,WeightedPeriodicTangentPhysical.energy
      (2*Real.pi*(A*((j:ℝ)+1))) μ σ ≤ C) :
    WeightedTangent.energy μ σ ≤ C := by
  apply csSup_le (Set.range_nonempty _)
  rintro y ⟨φ,rfl⟩
  let U := (WeightedTangent.representative μ σ).val
  let f := fun j : ℕ => (φ : Point n → ℝ) ∘ compression (A*((j:ℝ)+1))
  have hf (j : ℕ) : ContDiff ℝ ∞ (f j) := φ.property.1.comp (compression_contDiff _)
  have hp (j : ℕ) := compressed_periodic (mul_ne_zero hA.ne' (by positivity : (j:ℝ)+1 ≠ 0)) (φ : Point n → ℝ)
  obtain ⟨B,hB⟩ := (compactSupport_test_gradient φ).exists_bound_of_continuous (continuous_test_gradient φ)
  have hBn : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hgb (j : ℕ) (x : Point n) : ‖gradient (f j) x‖ ≤ B :=
    compressed_gradient_bound φ.property.1 hB (mul_ne_zero hA.ne' (by positivity)) x
  have hgt (x : Point n) : Tendsto (fun j => gradient (f j) x) atTop (𝓝 (gradient (φ : Point n → ℝ) x)) :=
    compressed_gradient_tendsto φ.property.1 hA.ne' x
  have hpair : Tendsto (fun j => ∫ x,⟪gradient (f j) x,U x⟫_ℝ ∂μ) atTop
      (𝓝 (∫ x,⟪gradient (φ : Point n → ℝ) x,U x⟫_ℝ ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => B*‖U x‖)
    · intro j
      exact (BochnerIdentity.smooth_gradient (hf j)).continuous.aestronglyMeasurable.inner (Lp.memLp U).aestronglyMeasurable
    · exact ((Lp.memLp U).integrable (by norm_num)).norm.const_mul B
    · intro j
      exact Eventually.of_forall fun x => (norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (hgb j x) (norm_nonneg _))
    · exact Eventually.of_forall fun x => (hgt x).inner tendsto_const_nhds
  have hnorm : Tendsto (fun j => ∫ x,‖gradient (f j) x‖^2 ∂μ) atTop
      (𝓝 (∫ x,‖gradient (φ : Point n → ℝ) x‖^2 ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ : Point n => B^2)
    · intro j
      exact ((BochnerIdentity.smooth_gradient (hf j)).continuous.norm.pow 2).aestronglyMeasurable
    · exact integrable_const _
    · intro j
      exact Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hgb j x) 2
    · exact Eventually.of_forall fun x => (hgt x).norm.pow 2
  have ht := (hpair.const_mul 2).sub hnorm
  have hle : (2*(∫ x,⟪gradient (φ : Point n → ℝ) x,U x⟫_ℝ ∂μ)-
      (∫ x,‖gradient (φ : Point n → ℝ) x‖^2 ∂μ)) ≤ C := by
    apply le_of_tendsto' ht
    intro j
    exact (smooth_periodic_objective_le μ (by positivity) σ (hf j) (hp j)).trans (hC j)
  simpa only [testObjective,representative_divergence μ σ hσ φ] using hle

end SharpWasserstein.PeriodicEnergyExhaustion
