import SharpWasserstein.WeightedMarginal

/-! The genuine marginal representative pairs correctly with all bounded
smooth potentials with bounded gradient, by the proved compact cutoff density.
No compact-support claim is made for the lifted cylinder function. -/
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff
namespace SharpWasserstein.WeightedMarginal
open WeightedTangent
variable {n m : ℕ} [MeasurableSpace (Point n)] [BorelSpace (Point n)]
  [MeasurableSpace (Point (n+m))] [BorelSpace (Point (n+m))]
  (μ : Measure (Point (n+m))) [IsFiniteMeasure μ]

theorem marginal_representative_bounded_smooth_pairing
    (σ : Test (n+m) →ₗ[ℝ] ℝ) {f : Point n → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfa : ∃ A : ℝ, ∀ x, |f x| ≤ A)
    (hfb : ∃ B : ℝ, ∀ x, ‖gradient f x‖ ≤ B) :
    (∫ x, ⟪gradient f (prefixProjection n m x),
      prefixProjection n m ((representative μ σ).val x)⟫_ℝ ∂μ) =
    ∫ y, ⟪gradient f y,
      (representative (marginalLaw μ) (marginalDistribution μ σ)).val y⟫_ℝ ∂marginalLaw μ := by
  have hg := bounded_smooth_gradient_memLp (marginalLaw μ) f hf hfb
  let w : gradientClosure (marginalLaw μ) :=
    ⟨hg.toLp (gradient f), bounded_smooth_gradient_memClosure (marginalLaw μ) f hf hfa hfb hg⟩
  have hl := vectorLiftLinear_ae μ (w : Lp (Point n) 2 (marginalLaw μ))
  have hgw : (w : Lp (Point n) 2 (marginalLaw μ)) =ᵐ[marginalLaw μ] gradient f := hg.coeFn_toLp
  have hgp := ae_of_ae_map (prefixProjection n m).continuous.measurable.aemeasurable hgw
  have he := marginal_representative_pairing μ σ w
  rw [L2.inner_def,L2.inner_def] at he
  calc
    _ = ∫ x, ⟪(representative μ σ).val x,vectorLift μ (w : Lp (Point n) 2 (marginalLaw μ)) x⟫_ℝ ∂μ := by
      apply integral_congr_ae
      filter_upwards [hl,hgp] with x hx hy
      change _ = ⟪(representative μ σ).val x,vectorLiftLinear μ (w : Lp (Point n) 2 (marginalLaw μ)) x⟫_ℝ
      rw [hx,hy,← inner_prefixEmbedding]
      exact real_inner_comm _ _
    _ = ∫ y, ⟪(representative (marginalLaw μ) (marginalDistribution μ σ)).val y,w.val y⟫_ℝ ∂marginalLaw μ := he
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hgw] with y hy
      rw [hy,real_inner_comm]

end SharpWasserstein.WeightedMarginal
