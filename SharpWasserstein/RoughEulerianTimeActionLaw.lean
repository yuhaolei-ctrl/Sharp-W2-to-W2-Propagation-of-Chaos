import SharpWasserstein.RoughEulerianTimeKernel
import SharpWasserstein.RoughEulerianTransportKernel
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! Actual time averaging of a joint time-space measure. The averaged spatial
law is a measurable kernel constructed by weighting and pushing the original
joint measure; normalization and spatial support are proved. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal ProbabilityTheory
namespace SharpWasserstein.RoughEulerianTime
open WeightedTangent
variable {d : ℕ} [MeasurableSpace (Point d)]

/-- The literal nonnegative time-mollifier density. -/
def timeWeight (ε : ℝ) (hε : 0 < ε) (t : ℝ) (z : ℝ × Point d) : ℝ≥0∞ :=
  ENNReal.ofReal (timeKernel ε hε (t-z.1))

theorem timeWeight_measurable {ε : ℝ} (hε : 0 < ε) :
    Measurable (Function.uncurry (timeWeight (d := d) ε hε)) := by
  exact ((timeKernel_smooth hε).continuous.measurable.comp
    (measurable_fst.sub (measurable_fst.comp measurable_snd))).ennreal_ofReal

/-- Parameterized actual weighted joint measures. -/
def weightedTimeKernel (ε : ℝ) (hε : 0 < ε) (ρ : Measure (ℝ × Point d)) [IsFiniteMeasure ρ] :
    Kernel ℝ (ℝ × Point d) := (Kernel.const ℝ ρ).withDensity (timeWeight ε hε)

instance weightedTimeKernel_finite {ε : ℝ} (hε : 0 < ε)
    (ρ : Measure (ℝ × Point d)) [IsFiniteMeasure ρ] : IsFiniteKernel (weightedTimeKernel ε hε ρ) := by
  obtain ⟨C,D,hC,hD⟩ := timeKernel_bounds hε
  apply Kernel.isFiniteKernel_withDensity_of_bounded _ (B := ENNReal.ofReal C) ENNReal.ofReal_ne_top
  intro t z
  exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hC (t-z.1)))

theorem weightedTimeKernel_apply {ε : ℝ} (hε : 0 < ε)
    (ρ : Measure (ℝ × Point d)) [IsFiniteMeasure ρ] (t : ℝ) :
    weightedTimeKernel ε hε ρ t = ρ.withDensity (timeWeight ε hε t) :=
  Kernel.withDensity_apply _ (timeWeight_measurable hε) t

/-- The actual time-averaged spatial law, as one measurable kernel. -/
def averagedKernel (ε : ℝ) (hε : 0 < ε) (ρ : Measure (ℝ × Point d)) [IsFiniteMeasure ρ] :
    Kernel ℝ (Point d) := (weightedTimeKernel ε hε ρ).map Prod.snd

instance averagedKernel_finite {ε : ℝ} (hε : 0 < ε)
    (ρ : Measure (ℝ × Point d)) [IsFiniteMeasure ρ] : IsFiniteKernel (averagedKernel ε hε ρ) := by
  unfold averagedKernel
  infer_instance

theorem averagedKernel_apply {ε : ℝ} (hε : 0 < ε)
    (ρ : Measure (ℝ × Point d)) [IsFiniteMeasure ρ] (t : ℝ) :
    averagedKernel ε hε ρ t = (ρ.withDensity (timeWeight ε hε t)).map Prod.snd := by
  rw [averagedKernel,Kernel.map_apply _ measurable_snd,weightedTimeKernel_apply]

/-- Literal weighted-integral identity, including vector-valued fluxes. -/
theorem integral_weightedTimeKernel {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ε : ℝ} (hε : 0 < ε) (ρ : Measure (ℝ × Point d)) [IsFiniteMeasure ρ]
    (f : ℝ × Point d → E) (t : ℝ) :
    (∫ z,f z ∂weightedTimeKernel ε hε ρ t) =
      ∫ z,timeKernel ε hε (t-z.1) • f z ∂ρ := by
  have hw : Measurable (timeWeight (d := d) ε hε t) :=
    (timeWeight_measurable hε).comp (measurable_const.prodMk measurable_id)
  rw [weightedTimeKernel_apply,integral_withDensity_eq_integral_toReal_smul hw
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [timeWeight,ENNReal.toReal_ofReal (timeKernel_nonneg hε _)]

/-- The spatial averaging integral is the actual time-weighted joint integral. -/
theorem integral_averagedKernel {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ε : ℝ} (hε : 0 < ε) (ρ : Measure (ℝ × Point d)) [IsFiniteMeasure ρ]
    (f : Point d → E) (hf : StronglyMeasurable f) (t : ℝ) :
    (∫ x,f x ∂averagedKernel ε hε ρ t) =
      ∫ z,timeKernel ε hε (t-z.1) • f z.2 ∂ρ := by
  rw [averagedKernel_apply,integral_map measurable_snd.aemeasurable hf.aestronglyMeasurable]
  simpa only [weightedTimeKernel_apply] using integral_weightedTimeKernel hε ρ (fun z => f z.2) t

/-- Genuine normalization for interior times, derived from the probability
kernel and the integral-one compact time mollifier. -/
theorem averagedKernel_probability {ε a b t : ℝ} (hε : 0 < ε)
    (κ : Kernel ℝ (Point d)) [IsMarkovKernel κ]
    (ha : a+ε ≤ t) (hb : t+ε ≤ b) :
    IsProbabilityMeasure (averagedKernel ε hε ((volume.restrict (Icc a b)) ⊗ₘ κ) t) := by
  apply isProbabilityMeasure_iff.mpr
  rw [averagedKernel_apply,Measure.map_apply measurable_snd MeasurableSet.univ,
    preimage_univ,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  rw [Measure.lintegral_compProd (by
    exact (timeWeight_measurable hε).comp (measurable_const.prodMk measurable_id))]
  simp only [timeWeight,lintegral_const,measure_univ,mul_one]
  have hi : Integrable (fun s => timeKernel ε hε (t-s)) (volume.restrict (Icc a b)) :=
    (((timeKernel_smooth hε).continuous.comp (continuous_const.sub continuous_id)).continuousOn.integrableOn_Icc)
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun s => timeKernel_nonneg hε (t-s)),
    timeKernel_window_normalization hε ha hb,ENNReal.ofReal_one]

/-- Weighting and averaging preserve the fixed spatial support exactly. -/
theorem averagedKernel_support {ε : ℝ} (hε : 0 < ε)
    (ρ : Measure (ℝ × Point d)) [IsFiniteMeasure ρ] (K : Set (Point d))
    (hK : MeasurableSet K) (hρ : ρ (univ ×ˢ Kᶜ)=0) (t : ℝ) :
    averagedKernel ε hε ρ t Kᶜ = 0 := by
  rw [averagedKernel_apply,Measure.map_apply measurable_snd hK.compl]
  apply (withDensity_absolutelyContinuous ρ (timeWeight ε hε t))
  have he : Prod.snd ⁻¹' Kᶜ = (univ : Set ℝ) ×ˢ Kᶜ := by ext z; simp
  rwa [he]

end SharpWasserstein.RoughEulerianTime
