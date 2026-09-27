import SharpWasserstein.PropagatedFluxSmoothPairing
import SharpWasserstein.WeightedPeriodicCoefficientEvolutionBrownian

/-! Actual Brownian source action on bounded smooth tests equals pairing
with the canonical tangent of its actual carrying law. This extends the
compact-test identification by proved gradient-closure density. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace NNReal
namespace SharpWasserstein.PropagatedSourceEquation.Brownian
open WeightedTangent NoiseAverage PeriodicSourceConvolution PropagatedFlux.Flow
variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  {b : Configuration d N → Configuration d N} {M' K' : ℝ≥0}
  (hv' : Continuous (Function.uncurry (fun _ : ℝ => equivDrift (configurationEuclidean d N) b)))
  (hb' : ∀ _ : ℝ,∀ y,‖equivDrift (configurationEuclidean d N) b y‖ ≤ M')
  (hl' : ∀ _ : ℝ,LipschitzWith K' (equivDrift (configurationEuclidean d N) b))
  {T : ℝ} (hT : 0 ≤ T) (hbs : ContDiff ℝ ∞ b) (hB : AllDerivativesBounded b)
  (μ : Measure (Point (N*d))) [IsFiniteMeasure μ]
  {u : Point (N*d) → Point (N*d)} (hu : MemLp u 2 μ)

instance lawAt_isFiniteMeasure (t : ℝ) : IsFiniteMeasure (lawAt hv' hb' hl' hT μ t) := by
  unfold lawAt
  infer_instance

theorem action_eq_representative_pairing {F : Point (N*d) → ℝ}
    (hF : ContDiff ℝ ∞ F) (hBF : AllDerivativesBounded F)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    action hv' hb' hl' hT (euclideanBrownianPathLaw d N T) μ u F t =
      ∫ x,⟪gradient F x,
        (WeightedTangent.representative (lawAt hv' hb' hl' hT μ t)
          (sourceAt hv' hb' hl' hT hbs hB μ u hu t)).val x⟫_ℝ ∂lawAt hv' hb' hl' hT μ t := by
  obtain ⟨C,_,hC⟩ := hBF.bounded
  obtain ⟨L,hL,hLf⟩ := hBF.fderiv.bounded
  have hgrad : ∃ B : ℝ,∀ x,‖gradient F x‖ ≤ B := by
    obtain ⟨B,_,h⟩ := (WeightedPeriodicCoefficientEvolution.gradient_allDerivativesBounded hF hBF).bounded
    exact ⟨B,h⟩
  rw [action_eq_randomFlux hv' hb' hl' hT _ μ (equivDrift_smooth _ hbs)
    (equivDrift_allDerivativesBounded _ hbs hB) (hF.of_le (by simp)) hC
    (L := ⟨L,hL⟩) hLf hu ht]
  have hV := velocity_memLp hv' hb' hl' hT (euclideanBrownianPathLaw d N T) (projIcc 0 T hT t).property
    (equivDrift_smooth _ hbs) (equivDrift_allDerivativesBounded _ hbs hB) μ hu
  have hp := PropagatedFlux.representative_bounded_smooth_pairing
    (μ.prod (euclideanBrownianPathLaw d N T)) (endpoint hv' hb' hl' hT (t := projIcc 0 T hT t))
    (endpoint_measurable hv' hb' hl' hT (projIcc 0 T hT t).property) (hV.toLp _) hF
    ⟨C,fun x => by simpa only [Real.norm_eq_abs] using hC x⟩ hgrad
  refine Eq.trans ?_ hp.symm
  apply integral_congr_ae
  filter_upwards [hV.coeFn_toLp] with q hq
  rw [hq,inner_gradient_left]
  simp only [endpoint,velocity,projIcc_of_mem _ ht]

end SharpWasserstein.PropagatedSourceEquation.Brownian
