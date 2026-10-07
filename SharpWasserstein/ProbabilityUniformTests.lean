module

public import SharpWasserstein.Compat
public import SharpWasserstein.ProbabilityLipschitzEstimate

@[expose] public section

/-! Narrowly continuous probability curves control an entire uniformly bounded
Lipschitz family of observables uniformly on compact time intervals. -/
noncomputable section
open MeasureTheory Set Metric
open scoped Topology NNReal ENNReal BoundedContinuousFunction
namespace SharpWasserstein
variable {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace.SeparableSpace E]

theorem continuous_probabilityCurve_uniform_lipschitz_tests
    (μ : ℝ → ProbabilityMeasure E) (hμ : Continuous μ) (T : ℝ)
    (A L : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, dist s t < δ →
      ∀ f : E →ᵇ ℝ, ‖f‖ ≤ A → LipschitzWith L f →
        ‖(∫ x, f x ∂(μ s : Measure E)) - (∫ x, f x ∂(μ t : Measure E))‖ < ε := by
  let η : ℝ := ε / ((L:ℝ)+2*A+1)
  have hden : 0 < (L:ℝ)+2*A+1 := by positivity
  have hη : 0 < η := div_pos hε hden
  have hc : Continuous (fun t => LevyProkhorov.ofMeasure (μ t)) :=
    LevyProkhorov.continuous_ofMeasure_probabilityMeasure.comp hμ
  have hu : UniformContinuousOn (fun t => LevyProkhorov.ofMeasure (μ t)) (Icc 0 T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hc.continuousOn
  obtain ⟨δ,hδ,hd⟩ := Metric.uniformContinuousOn_iff.mp hu η hη
  refine ⟨δ,hδ,fun s hs t ht hst f hf hL => ?_⟩
  have hdist := hd s hs t ht hst
  have he : levyProkhorovEDist (μ s : Measure E) (μ t : Measure E) < ENNReal.ofReal η := by
    change edist (LevyProkhorov.ofMeasure (μ s)) (LevyProkhorov.ofMeasure (μ t)) < ENNReal.ofReal η
    rw [edist_dist]
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg |>.mpr hdist
  have h := norm_integral_lipschitz_sub_le_of_levyProkhorovEDist_lt
    (μ s : Measure E) (μ t : Measure E) f hL hη he
  apply h.trans_lt
  calc
    η*((L:ℝ)+2*‖f‖) ≤ η*((L:ℝ)+2*A) := by gcongr
    _ < η*((L:ℝ)+2*A+1) := by nlinarith
    _ = ε := by dsimp [η]; field_simp

end SharpWasserstein
