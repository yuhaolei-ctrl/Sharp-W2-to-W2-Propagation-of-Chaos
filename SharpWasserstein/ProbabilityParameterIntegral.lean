import SharpWasserstein.WeakEvolutionTimeTests

/-! Jointly continuous bounded parameterized integrals against actual narrow
probability curves, including a two-time drift-variation modulus. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction
namespace SharpWasserstein

theorem continuous_integral_parameter_probability {S E : Type*}
    [MeasurableSpace S] [MetricSpace S] [BorelSpace S] [SecondCountableTopology S]
    [MeasurableSpace E] [PseudoMetricSpace E] [SecondCountableTopology E] [BorelSpace E]
    (μ : S → ProbabilityMeasure E) (hμ : Continuous μ) (F : S × E → ℝ)
    (hF : Continuous F) {C : ℝ} (hC : ∀ p, ‖F p‖ ≤ C) :
    Continuous (fun s => ∫ x, F (s,x) ∂(μ s : Measure E)) := by
  let f : S × E →ᵇ ℝ := {
    toFun := F
    continuous_toFun := hF
    map_bounded' := ⟨2*C,fun p q => (dist_le_norm_add_norm _ _).trans (by linarith [hC p,hC q])⟩ }
  have hp : Continuous (fun s => (diracProba s).prod (μ s)) :=
    ProbabilityMeasure.continuous_prod.comp (continuous_diracProba.prodMk hμ)
  have hc := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).comp hp
  convert hc using 1
  funext s
  change (∫ x, F (s,x) ∂(μ s : Measure E)) = ∫ p, f p ∂(Measure.dirac s).prod (μ s : Measure E)
  rw [integral_prod _ (f.integrable _),integral_dirac]
  rfl

namespace ProbabilityDriftVariation
variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [SecondCountableTopology E] [BorelSpace E]

def variation (v : ℝ → E → E) (μ : ℝ → ProbabilityMeasure E) (p : ℝ × ℝ) : ℝ :=
  ∫ x, ‖v p.1 x-v p.2 x‖ ∂(μ p.2 : Measure E)

theorem continuous_variation {v : ℝ → E → E} (hv : Continuous (Function.uncurry v))
    {M : ℝ} (hM : ∀ s x, ‖v s x‖ ≤ M) (μ : ℝ → ProbabilityMeasure E) (hμ : Continuous μ) :
    Continuous (variation v μ) := by
  apply continuous_integral_parameter_probability (C := 2*M) (fun p : ℝ × ℝ => μ p.2) (hμ.comp continuous_snd)
    (fun p : (ℝ × ℝ) × E => ‖v p.1.1 p.2-v p.1.2 p.2‖)
  · exact ((hv.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)).sub
      (hv.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd))).norm
  · intro p
    rw [norm_norm]
    exact (norm_sub_le _ _).trans (by linarith [hM p.1.1 p.2,hM p.1.2 p.2])

theorem uniform_variation {v : ℝ → E → E} (hv : Continuous (Function.uncurry v))
    {M : ℝ} (hM : ∀ s x, ‖v s x‖ ≤ M) (μ : ℝ → ProbabilityMeasure E) (hμ : Continuous μ)
    (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, dist t s < δ → variation v μ (t,s) < ε := by
  have hc := continuous_variation hv hM μ hμ
  have hu : UniformContinuousOn (variation v μ) (Icc (0:ℝ) T ×ˢ Icc (0:ℝ) T) :=
    (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hc.continuousOn
  obtain ⟨δ,hδ,hd⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  refine ⟨δ,hδ,fun s hs t ht hst => ?_⟩
  have hh := hd (t,s) ⟨ht,hs⟩ (s,s) ⟨hs,hs⟩ (by simpa only [Prod.dist_eq,dist_self,max_eq_left dist_nonneg] using hst)
  have he : variation v μ (s,s) = 0 := by simp [variation]
  rw [he,dist_zero_right,Real.norm_eq_abs] at hh
  exact (le_abs_self _).trans_lt hh

end ProbabilityDriftVariation
end SharpWasserstein
