module

public import SharpWasserstein.Compat
public import BrownianMotion.Gaussian.BrownianMotion
public import SharpWasserstein.FlowMoments

@[expose] public section

/-! Concrete continuous Brownian input, with the sqrt(2) normalization of the
manuscript. The source is the pinned, independently replayed Brownian library;
this module does not assume existence of a Wiener law. -/

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SharpWasserstein.BrownianNoise

abbrev Sample := ℝ≥0 → ℝ

/-- Restrict the constructed continuous Brownian modification to the horizon. -/
def scalarPath {T : ℝ} (ω : Sample) : C(Icc 0 T, ℝ) :=
  ⟨fun t => Real.sqrt 2 * brownian ⟨t, t.property.1⟩ ω,
    continuous_const.mul ((continuous_brownian ω).comp
      (continuous_subtype_val.subtype_mk _))⟩

theorem scalarPath_measurable {T : ℝ} : Measurable (scalarPath (T := T)) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact measurable_const.mul (measurable_brownian _)

def scalarLaw (T : ℝ) : Measure C(Icc 0 T, ℝ) :=
  Measure.map scalarPath gaussianLimit

instance scalarLaw_probability (T : ℝ) : IsProbabilityMeasure (scalarLaw T) :=
  Measure.isProbabilityMeasure_map scalarPath_measurable.aemeasurable

theorem scalarPath_zero_ae {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ ω ∂gaussianLimit, scalarPath ω (⟨0, le_rfl, hT⟩ : Icc 0 T) = 0 := by
  filter_upwards [isBrownianReal_brownian.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hω
  change Real.sqrt 2 * brownian 0 ω = 0
  rw [hω, mul_zero]

theorem scalarLaw_zero_ae {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ w ∂scalarLaw T, w (⟨0, le_rfl, hT⟩ : Icc 0 T) = 0 := by
  exact (ae_map_iff scalarPath_measurable.aemeasurable
    ((by fun_prop : Continuous (fun w : C(Icc 0 T, ℝ) => w ⟨0, le_rfl, hT⟩)).measurable
      (measurableSet_singleton 0))).mpr
      (scalarPath_zero_ae hT)

theorem scalarPath_memLp {T : ℝ} (t : Icc 0 T) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun ω => scalarPath ω t) p gaussianLimit := by
  have h := (memLp_id_gaussianReal' (μ := 0) (v := ⟨t, t.property.1⟩) p hp).comp_measurePreserving
    (hasLaw_brownian_eval.measurePreserving (measurable_brownian _))
  exact h.const_mul (Real.sqrt 2)

theorem scalarLaw_memLp {T : ℝ} (t : Icc 0 T) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun w : C(Icc 0 T, ℝ) => w t) p (scalarLaw T) := by
  exact (memLp_map_measure_iff (by fun_prop : Continuous (fun w : C(Icc 0 T, ℝ) => w t)).measurable.aestronglyMeasurable
    scalarPath_measurable.aemeasurable).mpr (scalarPath_memLp t p hp)

/-- The variance is exactly 2t, matching diffusion coefficient one. -/
theorem scalarPath_hasLaw {T : ℝ} (t : Icc 0 T) :
    HasLaw (fun ω => scalarPath ω t) (gaussianReal 0 (2 * ⟨t, t.property.1⟩)) gaussianLimit := by
  have h := gaussianReal_const_mul (hasLaw_brownian_eval (t := ⟨t, t.property.1⟩)) (Real.sqrt 2)
  have hs : NNReal.mk ((Real.sqrt 2) ^ 2) (sq_nonneg _) = 2 := by
    apply Subtype.ext
    exact Real.sq_sqrt (by norm_num)
  rw [hs] at h
  simpa [scalarPath] using h

theorem scalarLaw_hasLaw {T : ℝ} (t : Icc 0 T) :
    HasLaw (fun w : C(Icc 0 T, ℝ) => w t) (gaussianReal 0 (2 * ⟨t, t.property.1⟩))
      (scalarLaw T) where
  aemeasurable := (by fun_prop : Continuous (fun w : C(Icc 0 T, ℝ) => w t)).measurable.aemeasurable
  map_eq := by
    rw [scalarLaw, Measure.map_map
      (by fun_prop : Continuous (fun w : C(Icc 0 T, ℝ) => w t)).measurable scalarPath_measurable]
    exact (scalarPath_hasLaw t).map_eq

theorem scalarLaw_secondMoment {T : ℝ} (t : Icc 0 T) :
    (∫ w : C(Icc 0 T, ℝ), (w t) ^ 2 ∂scalarLaw T) = 2 * (t : ℝ) := by
  have hm : (∫ w : C(Icc 0 T, ℝ), w t ∂scalarLaw T) = 0 := by
    rw [(scalarLaw_hasLaw t).integral_eq, integral_id_gaussianReal]
  have hv := (scalarLaw_hasLaw t).variance_eq
  rw [variance_eq_integral (scalarLaw_hasLaw t).aemeasurable, hm,
    variance_id_gaussianReal] at hv
  simp only [sub_zero] at hv
  change (∫ w : C(Icc 0 T, ℝ), (w t) ^ 2 ∂scalarLaw T) = 2 * (t : ℝ) at hv
  exact hv

end SharpWasserstein.BrownianNoise
