import SharpWasserstein.PeriodicConvolutionTestGradient
import SharpWasserstein.WeightedMarginalSmoothPairing

/-! Genuine weighted source marginals commute with averaging the periodic
gradient test. The identity uses the actual minimal-energy representatives,
and is valid for singular initial laws. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff InnerProductSpace
namespace SharpWasserstein.PeriodicConvolution
open WeightedTangent WeightedMarginal PeriodicIntegrationByParts PeriodicPositiveKernel PeriodicBochner
variable {n m : ℕ} [MeasurableSpace (Point n)] [BorelSpace (Point n)]
  [MeasurableSpace (Point (n+m))] [BorelSpace (Point (n+m))]
  (μ : Measure (Point (n+m))) [IsFiniteMeasure μ]

theorem marginal_representative_testAverage_pairing (σ : Test (n+m) →ₗ[ℝ] ℝ)
    (κ : ℝ) {f : Coordinates n → ℝ} (hf : ContDiff ℝ ∞ f) (hp : Periodic f) :
    (∫ y, ⟪∫ x, kernel κ (x-prefixCoords n m (coordinateEquiv (n+m) y)) •
      euclideanGradient f x ∂cube n,
      prefixProjection n m ((representative μ σ).val y)⟫_ℝ ∂μ) =
    ∫ y, ⟪∫ x, kernel κ (x-coordinateEquiv n y) • euclideanGradient f x ∂cube n,
      (representative (marginalLaw μ) (marginalDistribution μ σ)).val y⟫_ℝ ∂marginalLaw μ := by
  have hs := testAverage_smooth κ hf hp
  have hp' := testAverage_periodic κ hp
  have hg := hs.comp (coordinateEquiv n).contDiff
  obtain ⟨A,_,hA⟩ := PeriodicSmoothBounds.norm_bound hp' hs.continuous
  obtain ⟨B,_,hB⟩ := PeriodicSmoothBounds.norm_bound
    (euclideanGradient_periodic hp') (euclideanGradient_continuous hs)
  have ha : ∃ A : ℝ, ∀ x : Point n, |pullback (testAverage κ f) x| ≤ A :=
    ⟨A, fun x => by simpa only [Real.norm_eq_abs,pullback,Function.comp_def] using hA (coordinateEquiv n x)⟩
  have hb : ∃ B : ℝ, ∀ x : Point n, ‖gradient (pullback (testAverage κ f)) x‖ ≤ B :=
    ⟨B,fun x => by
      simpa only [euclideanGradient,ContinuousLinearEquiv.symm_apply_apply] using hB (coordinateEquiv n x)⟩
  simp_rw [← testAverage_euclideanGradient κ hf hp]
  convert marginal_representative_bounded_smooth_pairing μ σ hg ha hb using 1
  · apply integral_congr_ae
    exact Eventually.of_forall fun y => rfl
  · apply integral_congr_ae
    exact Eventually.of_forall fun y => by
      simp only [euclideanGradient,ContinuousLinearEquiv.symm_apply_apply]
      rfl

end SharpWasserstein.PeriodicConvolution
