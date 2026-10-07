module

public import SharpWasserstein.Compat
public import SharpWasserstein.BoundedFlow
public import SharpWasserstein.ConfigurationEuclidean
public import SharpWasserstein.TransportMoments
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

/-! Moment propagation for the actual continuous-forcing trajectories. The
noise needs only a second moment at the time in question, not a moment of its
supremum over time. -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal Interval

namespace SharpWasserstein

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Bounded drift controls the trajectory by its initial label and noise value. -/
theorem FiniteAdditiveTrajectory.norm_le
    {v : ℝ → E → E} {w X : ℝ → E} {x₀ : E} {T t M : ℝ}
    (h : FiniteAdditiveTrajectory v w x₀ T X)
    (hb : ∀ s ∈ Icc 0 T, ∀ x, ‖v s x‖ ≤ M) (ht : t ∈ Icc 0 T) :
    ‖X t‖ ≤ ‖x₀‖ + M * t + ‖w t‖ := by
  have hi : ‖∫ s in (0 : ℝ)..t, v s (X s)‖ ≤ M * t := by
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
      (f := fun s => v s (X s)) (fun s hs => by
        have hs' : s ∈ Ioc 0 t := by simpa only [uIoc_of_le ht.1] using hs
        exact hb s ⟨hs'.1.le, hs'.2.trans ht.2⟩ (X s))
    simpa [abs_of_nonneg ht.1] using hi
  rw [h.equation t ht]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add le_rfl hi)) le_rfl)

/-- Any finite exponent propagates from the initial label and forcing value. -/
theorem finiteTrajectory_memLp {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P]
    {p : ℝ≥0∞} {v : ℝ → E → E} {x₀ : Ω → E} {w X : ℝ → Ω → E} {T t M : ℝ}
    (h : ∀ ω, FiniteAdditiveTrajectory v (fun s => w s ω) (x₀ ω) T (fun s => X s ω))
    (hb : ∀ s ∈ Icc 0 T, ∀ x, ‖v s x‖ ≤ M) (ht : t ∈ Icc 0 T)
    (hx : MemLp x₀ p P) (hw : MemLp (w t) p P) (hXm : AEStronglyMeasurable (X t) P) :
    MemLp (X t) p P := by
  have hm : MemLp (fun ω => ‖x₀ ω‖ + M * t + ‖w t ω‖) p P :=
    (hx.norm.add (memLp_const (M * t))).add hw.norm
  exact hm.mono' hXm (Filter.Eventually.of_forall fun ω => (h ω).norm_le hb ht)

/-- Euclidean second moment of a configuration-valued map follows from its
actual L² membership in the equivalent ambient norm. -/
theorem hasSecondMoment_map_of_memLp {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {d N : ℕ} {F : Ω → Configuration d N}
    (hF : Measurable F) (h₂ : MemLp F 2 P) : HasSecondMoment (Measure.map F P) := by
  have hE := (configurationEuclidean d N).toContinuousLinearMap.comp_memLp' h₂
  have hI := (memLp_two_iff_integrable_sq_norm hE.aestronglyMeasurable).mp hE
  unfold HasSecondMoment
  rw [lintegral_map measurable_secondMoment hF]
  have hI' : Integrable (fun ω => productCost (F ω) 0) P := by
    simpa only [Function.comp_apply, ContinuousLinearEquiv.coe_coe,
      configurationEuclidean_norm_sq, productCost, Pi.zero_apply, sub_zero] using hI
  exact (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun ω => productCost_nonneg (F ω) 0)).mp hI'.2

/-- Conversely, the manuscript's finite quadratic cost gives a genuine L²
random variable. This direction prevents moment assumptions changing under
coordinate conversion. -/
theorem memLp_of_hasSecondMoment_map {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {d N : ℕ} {F : Ω → Configuration d N}
    (hF : Measurable F) (h₂ : HasSecondMoment (Measure.map F P)) : MemLp F 2 P := by
  have hI : Integrable (fun ω => productCost (F ω) 0) P := by
    refine ⟨(measurable_productCost.comp (hF.prodMk measurable_const)).aestronglyMeasurable, ?_⟩
    apply (hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun ω => productCost_nonneg (F ω) 0)).mpr
    simpa only [HasSecondMoment, lintegral_map measurable_secondMoment hF] using h₂
  have hE : MemLp (fun ω => configurationEuclidean d N (F ω)) 2 P := by
    apply (memLp_two_iff_integrable_sq_norm
      ((configurationEuclidean d N).continuous.comp_aestronglyMeasurable hF.aestronglyMeasurable)).mpr
    simpa only [configurationEuclidean_norm_sq, productCost, Pi.zero_apply, sub_zero] using hI
  have hi := (configurationEuclidean d N).symm.toContinuousLinearMap.comp_memLp' hE
  change MemLp (fun ω => (configurationEuclidean d N).symm
    (configurationEuclidean d N (F ω))) 2 P at hi
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using hi

end SharpWasserstein
