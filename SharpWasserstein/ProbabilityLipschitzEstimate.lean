import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! Quantitative control of bounded Lipschitz observables by the actual
Lévy–Prokhorov distance, for uniform families of weak tests. -/
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology NNReal ENNReal BoundedContinuousFunction
namespace SharpWasserstein
variable {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]

theorem integral_nonneg_lipschitz_le_of_levyProkhorovEDist_lt
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : E →ᵇ ℝ) {L : ℝ≥0} (hL : LipschitzWith L f) (hf : ∀ x, 0 ≤ f x)
    {ε : ℝ} (hε : 0 < ε) (hμν : levyProkhorovEDist μ ν < ENNReal.ofReal ε) :
    (∫ x, f x ∂μ) ≤ (∫ x, f x ∂ν) + ε*((L:ℝ)+‖f‖) := by
  let g : E →ᵇ ℝ := f + BoundedContinuousFunction.const E ((L:ℝ)*ε)
  have hg (x : E) : 0 ≤ g x := add_nonneg (hf x) (mul_nonneg L.coe_nonneg hε.le)
  have hfg : ‖f‖ ≤ ‖g‖ := by
    apply (BoundedContinuousFunction.norm_le (norm_nonneg g)).mpr
    intro x
    rw [Real.norm_of_nonneg (hf x)]
    exact (le_add_of_nonneg_right (mul_nonneg L.coe_nonneg hε.le)).trans (g.apply_le_norm x)
  have hset (t : ℝ) : thickening ε {x | t ≤ f x} ⊆ {x | t ≤ g x} := by
    intro x hx
    obtain ⟨y,hy,hxy⟩ := mem_thickening_iff.mp hx
    change t ≤ f y at hy
    have hdist := hL.dist_le_mul y x
    rw [Real.dist_eq, dist_comm y x] at hdist
    have habs := le_abs_self (f y-f x)
    have hm := mul_le_mul_of_nonneg_left hxy.le L.coe_nonneg
    change t ≤ f x + (L:ℝ)*ε
    linarith
  have hi (F : ℝ → Set E) (hF : Antitone F) (a : ℝ) :
      IntegrableOn (fun t => ν.real (F t)) (Ioc 0 a) := by
    apply Measure.integrableOn_of_bounded (M := 1) (by simp)
    · exact (Measurable.ennreal_toReal (Antitone.measurable (fun s t hst => measure_mono (hF hst)))).aestronglyMeasurable
    · exact Eventually.of_forall fun t => by
        rw [Real.norm_of_nonneg measureReal_nonneg]
        exact (measureReal_mono (subset_univ _)).trans (by simp)
  have hiF := hi (fun t => thickening ε {x | t ≤ f x})
    (fun s t hst => thickening_subset_of_subset ε (fun x hx => hst.trans hx)) ‖f‖
  have hiG := hi (fun t => {x | t ≤ g x}) (fun s t hst x hx => hst.trans hx) ‖g‖
  have hiG' := hi (fun t => {x | t ≤ g x}) (fun s t hst x hx => hst.trans hx) ‖f‖
  have hmono : (∫ t in Ioc 0 ‖f‖, ν.real (thickening ε {x | t ≤ f x})) ≤
      ∫ t in Ioc 0 ‖g‖, ν.real {x | t ≤ g x} := by
    apply (setIntegral_mono hiF hiG' (fun t => measureReal_mono (hset t))).trans
    exact setIntegral_mono_set hiG (Eventually.of_forall fun t => measureReal_nonneg)
      (Eventually.of_forall fun t ht => ⟨ht.1,ht.2.trans hfg⟩)
  have h := f.integral_le_of_levyProkhorovEDist_lt μ ν hε hμν (Eventually.of_forall hf)
  have he : (∫ x, g x ∂ν) = (∫ x, f x ∂ν) + (L:ℝ)*ε := by
    change (∫ x, f x + (L:ℝ)*ε ∂ν) = _
    rw [integral_add (f.integrable ν) (integrable_const _)]
    simp
  rw [← g.integral_eq_integral_meas_le ν (Eventually.of_forall hg)] at hmono
  rw [he] at hmono
  linarith

theorem integral_lipschitz_sub_le_of_levyProkhorovEDist_lt
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : E →ᵇ ℝ) {L : ℝ≥0} (hL : LipschitzWith L f)
    {ε : ℝ} (hε : 0 < ε) (hμν : levyProkhorovEDist μ ν < ENNReal.ofReal ε) :
    (∫ x, f x ∂μ) - (∫ x, f x ∂ν) ≤ ε*((L:ℝ)+2*‖f‖) := by
  let g : E →ᵇ ℝ := f + BoundedContinuousFunction.const E ‖f‖
  have hgL : LipschitzWith L g := by
    change LipschitzWith L (fun x => f x + ‖f‖)
    simpa only [one_mul, Function.comp_def] using (isometry_add_right ‖f‖).lipschitz.comp hL
  have hgn (x : E) : 0 ≤ g x := by
    change 0 ≤ f x + ‖f‖
    linarith [f.neg_norm_le_apply x]
  have hgnorm : ‖g‖ ≤ 2*‖f‖ := by
    apply (norm_add_le _ _).trans
    have hn : ‖BoundedContinuousFunction.const E ‖f‖‖ ≤ ‖f‖ :=
      (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr (fun x => by simp)
    linarith
  have he (σ : Measure E) [IsProbabilityMeasure σ] :
      (∫ x, g x ∂σ) = (∫ x, f x ∂σ)+‖f‖ := by
    change (∫ x, f x + ‖f‖ ∂σ) = _
    rw [integral_add (f.integrable σ) (integrable_const _)]
    simp
  have h := integral_nonneg_lipschitz_le_of_levyProkhorovEDist_lt μ ν g hgL hgn hε hμν
  rw [he μ,he ν] at h
  nlinarith

theorem norm_integral_lipschitz_sub_le_of_levyProkhorovEDist_lt
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : E →ᵇ ℝ) {L : ℝ≥0} (hL : LipschitzWith L f)
    {ε : ℝ} (hε : 0 < ε) (hμν : levyProkhorovEDist μ ν < ENNReal.ofReal ε) :
    ‖(∫ x, f x ∂μ) - (∫ x, f x ∂ν)‖ ≤ ε*((L:ℝ)+2*‖f‖) := by
  rw [Real.norm_eq_abs, abs_le]
  have h := integral_lipschitz_sub_le_of_levyProkhorovEDist_lt μ ν f hL hε hμν
  have h' := integral_lipschitz_sub_le_of_levyProkhorovEDist_lt ν μ f hL hε
    (by rwa [levyProkhorovEDist_comm])
  exact ⟨by linarith, h⟩

end SharpWasserstein
