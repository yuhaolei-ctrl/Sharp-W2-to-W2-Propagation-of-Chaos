module

public import SharpWasserstein.Compat
public import SharpWasserstein.FlowJacobianContinuityGlobal
public import SharpWasserstein.FlowInitialDerivativeSmooth
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
public import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity

@[expose] public section

/-! Measurable actual Jacobians for bounded smooth autonomous drifts, together
with preservation of integrability when they act on a random tangent vector. -/
noncomputable section
open Set MeasureTheory
open scoped NNReal ContDiff ENNReal
namespace SharpWasserstein.FlowInitialDerivative
open NoiseAverage
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Smooth bounded derivatives give genuine joint continuity of the Jacobian. -/
theorem autonomousFlow_fderiv_continuous_of_boundedSmooth
    {b : E → E} {M K : ℝ≥0} (hb : ∀ x, ‖b x‖ ≤ M) (hLip : LipschitzWith K b)
    (hbs : ContDiff ℝ ∞ b) (hB : AllDerivativesBounded b)
    {T : ℝ} (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Continuous (fun p : E × C(Icc 0 T,E) =>
      fderiv ℝ (fun y => autonomousFlow hb hLip hT y p.2 t) p.1) := by
  have hbd := hbs.differentiable (by simp)
  have hDs : ContDiff ℝ ∞ (fderiv ℝ b) := (contDiff_infty_iff_fderiv.mp hbs).2
  obtain ⟨K₁,hD⟩ := hB.fderiv.lipschitz (hDs.differentiable (by simp))
  exact autonomousFlow_fderiv_continuous hb hLip hbd hD hT ht

/-- Direct continuity API for the pre-existing constructed flow. -/
theorem boundedFlow_fderiv_continuous_of_boundedSmooth
    {b : E → E} {M K : ℝ≥0}
    (hv : Continuous (Function.uncurry (fun _ : ℝ => b)))
    (hb : ∀ _ : ℝ, ∀ x, ‖b x‖ ≤ M) (hl : ∀ _ : ℝ, LipschitzWith K b)
    (hbs : ContDiff ℝ ∞ b) (hB : AllDerivativesBounded b)
    {T : ℝ} (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Continuous (fun p : E × C(Icc 0 T,E) =>
      fderiv ℝ (fun y => BoundedFlow.flow hv hb hl hT y p.2 t) p.1) := by
  simpa only [autonomousFlow] using
    autonomousFlow_fderiv_continuous_of_boundedSmooth (hb 0) (hl 0) hbs hB hT ht

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {T : ℝ} [MeasurableSpace C(Icc 0 T,E)] [BorelSpace C(Icc 0 T,E)]

/-- Operator-valued measurability is a consequence of proved continuity. -/
theorem boundedFlow_fderiv_measurable_of_boundedSmooth
    {b : E → E} {M K : ℝ≥0}
    (hv : Continuous (Function.uncurry (fun _ : ℝ => b)))
    (hb : ∀ _ : ℝ, ∀ x, ‖b x‖ ≤ M) (hl : ∀ _ : ℝ, LipschitzWith K b)
    (hbs : ContDiff ℝ ∞ b) (hB : AllDerivativesBounded b)
    (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Measurable (fun p : E × C(Icc 0 T,E) =>
      fderiv ℝ (fun y => BoundedFlow.flow hv hb hl hT y p.2 t) p.1) :=
  (boundedFlow_fderiv_continuous_of_boundedSmooth hv hb hl hbs hB hT ht).measurable

/-- The actual Jacobian acts on measurable random tangent vectors. This works
for any joint initial-point/path law, including the independent Brownian law. -/
theorem boundedFlow_fderiv_apply_aestronglyMeasurable
    {b : E → E} {M K : ℝ≥0}
    (hv : Continuous (Function.uncurry (fun _ : ℝ => b)))
    (hb : ∀ _ : ℝ, ∀ x, ‖b x‖ ≤ M) (hl : ∀ _ : ℝ, LipschitzWith K b)
    (hbs : ContDiff ℝ ∞ b) (hB : AllDerivativesBounded b)
    (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc 0 T)
    (ρ : Measure (E × C(Icc 0 T,E))) {u : E × C(Icc 0 T,E) → E}
    (hu : AEStronglyMeasurable u ρ) :
    AEStronglyMeasurable (fun p =>
      fderiv ℝ (fun y => BoundedFlow.flow hv hb hl hT y p.2 t) p.1 (u p)) ρ := by
  have he : Measurable (fun q : (E →L[ℝ] E) × E => q.1 q.2) :=
    (continuous_fst.clm_apply continuous_snd).measurable
  exact (he.comp_aemeasurable
    ((boundedFlow_fderiv_measurable_of_boundedSmooth hv hb hl hbs hB hT ht).aemeasurable.prodMk
      hu.aemeasurable)).aestronglyMeasurable

/-- Acting by the genuine initial Jacobian preserves every Lᵖ class, by the
proved exponential operator bound; no integrability assumption on path suprema
is required. -/
theorem boundedFlow_fderiv_apply_memLp
    {b : E → E} {M K : ℝ≥0}
    (hv : Continuous (Function.uncurry (fun _ : ℝ => b)))
    (hb : ∀ _ : ℝ, ∀ x, ‖b x‖ ≤ M) (hl : ∀ _ : ℝ, LipschitzWith K b)
    (hbs : ContDiff ℝ ∞ b) (hB : AllDerivativesBounded b)
    (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc 0 T)
    (ρ : Measure (E × C(Icc 0 T,E))) {u : E × C(Icc 0 T,E) → E} {p : ℝ≥0∞}
    (hu : MemLp u p ρ) :
    MemLp (fun q =>
      fderiv ℝ (fun y => BoundedFlow.flow hv hb hl hT y q.2 t) q.1 (u q)) p ρ := by
  apply hu.of_le_mul (c := Real.exp ((K:ℝ)*t))
    (boundedFlow_fderiv_apply_aestronglyMeasurable hv hb hl hbs hB hT ht ρ hu.aestronglyMeasurable)
  filter_upwards [] with q
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right
      (boundedFlow_hasFDerivAt_and_norm_of_boundedSmooth hv hb hl hbs hB hT q.2 q.1 ht).2
      (norm_nonneg _))

/-- The quadratic energy of a random tangent vector grows by at most the
square of the proved Jacobian bound. -/
theorem boundedFlow_fderiv_apply_energy_le
    {b : E → E} {M K : ℝ≥0}
    (hv : Continuous (Function.uncurry (fun _ : ℝ => b)))
    (hb : ∀ _ : ℝ, ∀ x, ‖b x‖ ≤ M) (hl : ∀ _ : ℝ, LipschitzWith K b)
    (hbs : ContDiff ℝ ∞ b) (hB : AllDerivativesBounded b)
    (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc 0 T)
    (ρ : Measure (E × C(Icc 0 T,E))) {u : E × C(Icc 0 T,E) → E}
    (hu : MemLp u 2 ρ) :
    (∫ q, ‖fderiv ℝ (fun y => BoundedFlow.flow hv hb hl hT y q.2 t) q.1 (u q)‖^2 ∂ρ) ≤
      Real.exp ((K:ℝ)*t)^2 * ∫ q, ‖u q‖^2 ∂ρ := by
  have hj := boundedFlow_fderiv_apply_memLp hv hb hl hbs hB hT ht ρ hu
  have hi := (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mp hu
  have hji := (memLp_two_iff_integrable_sq_norm hj.aestronglyMeasurable).mp hj
  rw [← integral_const_mul]
  apply integral_mono_ae hji (hi.const_mul _)
  filter_upwards [] with q
  have hn := (ContinuousLinearMap.le_opNorm
    (fderiv ℝ (fun y => BoundedFlow.flow hv hb hl hT y q.2 t) q.1) (u q)).trans
    (mul_le_mul_of_nonneg_right
      (boundedFlow_hasFDerivAt_and_norm_of_boundedSmooth hv hb hl hbs hB hT q.2 q.1 ht).2
      (norm_nonneg _))
  simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn

end SharpWasserstein.FlowInitialDerivative
