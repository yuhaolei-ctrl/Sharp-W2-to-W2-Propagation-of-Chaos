import SharpWasserstein.DynamicTransport
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Lifting pointwise trajectories to L²

The mixed time-L¹, label-L² assumption is used directly. In particular, the
argument does not require time-square-integrability, which would exclude the
inverse-square-root speed appearing in the manuscript.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal InnerProductSpace

namespace SharpWasserstein.PointwiseTrajectory

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] {P : Measure Ω}

theorem norm_toLp_two_eq_sqrt {f : Ω → E} (hf : MemLp f 2 P) :
    ‖hf.toLp f‖ = Real.sqrt (∫ ω, ‖f ω‖ ^ 2 ∂P) := by
  rw [Lp.norm_toLp, hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  norm_num only [ENNReal.toReal_ofNat]
  rw [ENNReal.toReal_ofReal (by positivity)]
  simp only [Real.rpow_two, Real.sqrt_eq_rpow, one_div]

/-- The mixed-norm estimate needed for Fubini against every L² test vector. -/
theorem integral_norm_mul_le {f g : Ω → E} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    (∫ ω, ‖f ω‖ * ‖g ω‖ ∂P) ≤ ‖hf.toLp f‖ * ‖hg.toLp g‖ := by
  have ht := integral_mul_norm_le_Lp_mul_Lq (μ := P) Real.HolderConjugate.two_two
    (by simpa using hf) (by simpa using hg)
  rw [norm_toLp_two_eq_sqrt hf, norm_toLp_two_eq_sqrt hg]
  simpa only [Real.rpow_two, Real.sqrt_eq_rpow] using ht

variable [InnerProductSpace ℝ E]

theorem integrable_inner_of_memLp {f g : Ω → E} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    Integrable (fun ω => ⟪f ω, g ω⟫_ℝ) P := by
  apply (L2.integrable_inner (hf.toLp f) (hg.toLp g)).congr
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with ω hω h'ω
  rw [hω, h'ω]

theorem integral_norm_inner_le {f g : Ω → E} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    (∫ ω, ‖⟪f ω, g ω⟫_ℝ‖ ∂P) ≤ ‖hf.toLp f‖ * ‖hg.toLp g‖ := by
  have hi : Integrable (fun ω => ‖f ω‖ * ‖g ω‖) P := hf.norm.integrable_mul hg.norm
  exact (integral_mono (integrable_inner_of_memLp hf hg).norm hi
    (fun ω => norm_inner_le_norm _ _)).trans (integral_norm_mul_le hf hg)

theorem integrable_inner_product {T : Type*} [MeasurableSpace T]
    {τ : Measure T} [SFinite τ] [SFinite P]
    (v : T → Ω → E) (hv : StronglyMeasurable (Function.uncurry v))
    (h₂ : ∀ t, MemLp (v t) 2 P)
    (hV : Integrable (fun t => (h₂ t).toLp (v t)) τ) (W : Lp E 2 P) :
    Integrable (fun z : T × Ω => ⟪W z.2, v z.1 z.2⟫_ℝ) (τ.prod P) := by
  have hm : StronglyMeasurable (fun z : T × Ω => ⟪W z.2, v z.1 z.2⟫_ℝ) :=
    ((Lp.stronglyMeasurable W).comp_measurable measurable_snd).inner hv
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall fun t => integrable_inner_of_memLp (Lp.memLp W) (h₂ t), ?_⟩
  apply (hV.norm.const_mul ‖W‖).mono'
    hm.norm.aestronglyMeasurable.integral_prod_right'
  filter_upwards [] with t
  rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  simpa only [Lp.toLp_coeFn] using integral_norm_inner_le (Lp.memLp W) (h₂ t)

omit [InnerProductSpace ℝ E] in
theorem integral_norm_le_l2norm [IsProbabilityMeasure P] {f : Ω → E} (hf : MemLp f 2 P) :
    (∫ ω, ‖f ω‖ ∂P) ≤ ‖hf.toLp f‖ := by
  rw [Lp.norm_toLp, integral_norm_eq_lintegral_enorm hf.1,
    ← eLpNorm_one_eq_lintegral_enorm]
  exact ENNReal.toReal_mono hf.2.ne
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1 : ℝ≥0∞) ≤ 2) hf.1)

omit [InnerProductSpace ℝ E] in
/-- Time-L¹, label-L² integrability implies genuine joint Bochner integrability. -/
theorem integrable_product_of_l1_l2 {T : Type*} [MeasurableSpace T]
    {τ : Measure T} [SFinite τ] [IsProbabilityMeasure P]
    (v : T → Ω → E) (hv : StronglyMeasurable (Function.uncurry v))
    (h₂ : ∀ t, MemLp (v t) 2 P)
    (hV : Integrable (fun t => (h₂ t).toLp (v t)) τ) :
    Integrable (Function.uncurry v) (τ.prod P) := by
  apply (integrable_prod_iff hv.aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall fun t => (h₂ t).integrable (by norm_num), ?_⟩
  apply hV.norm.mono' hv.norm.aestronglyMeasurable.integral_prod_right'
  filter_upwards [] with t
  rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  exact integral_norm_le_l2norm (h₂ t)

variable [CompleteSpace E]

/-- Fubini identifies a pointwise integral with the genuine Bochner integral in L².
No interchange of a quotient representative and an integral is assumed. -/
theorem toLp_eq_integral_of_pointwise {T : Type*} [MeasurableSpace T]
    {τ : Measure T} [SFinite τ] [IsProbabilityMeasure P]
    (v : T → Ω → E) (hv : StronglyMeasurable (Function.uncurry v))
    (h₂ : ∀ t, MemLp (v t) 2 P)
    (hV : Integrable (fun t => (h₂ t).toLp (v t)) τ)
    {f : Ω → E} (hf : MemLp f 2 P)
    (heq : ∀ᵐ ω ∂P, f ω = ∫ t, v t ω ∂τ) :
    hf.toLp f = ∫ t, (h₂ t).toLp (v t) ∂τ := by
  have hvprod := integrable_product_of_l1_l2 v hv h₂ hV
  apply ext_inner_left ℝ
  intro W
  rw [← integral_inner hV W]
  calc
    ⟪W, hf.toLp f⟫_ℝ = ∫ ω, ⟪W ω, f ω⟫_ℝ ∂P := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with ω hω
      rw [hω]
    _ = ∫ ω, ∫ t, ⟪W ω, v t ω⟫_ℝ ∂τ ∂P := by
      apply integral_congr_ae
      filter_upwards [heq, hvprod.prod_left_ae] with ω hω hωint
      rw [hω]
      exact (integral_inner hωint (W ω)).symm
    _ = ∫ t, ∫ ω, ⟪W ω, v t ω⟫_ℝ ∂P ∂τ := by
      exact (integral_integral_swap (integrable_inner_product v hv h₂ hV W)).symm
    _ = ∫ t, ⟪W, (h₂ t).toLp (v t)⟫_ℝ ∂τ := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(h₂ t).coeFn_toLp] with ω hω
      rw [hω]

/-- Pointwise endpoint increments lift to an L²-valued interval integral equation. -/
theorem toLp_sub_eq_intervalIntegral [IsProbabilityMeasure P]
    (v : ℝ → Ω → E) (hv : StronglyMeasurable (Function.uncurry v))
    (h₂ : ∀ t, MemLp (v t) 2 P) {a b : ℝ} (hab : a ≤ b)
    (hV : IntervalIntegrable (fun t => (h₂ t).toLp (v t)) volume a b)
    {f g : Ω → E} (hf : MemLp f 2 P) (hg : MemLp g 2 P)
    (heq : ∀ᵐ ω ∂P, f ω - g ω = ∫ t in a..b, v t ω) :
    hf.toLp f - hg.toLp g = ∫ t in a..b, (h₂ t).toLp (v t) := by
  rw [intervalIntegral.integral_of_le hab]
  apply toLp_eq_integral_of_pointwise v hv h₂ hV.1 (hf.sub hg)
  simpa only [intervalIntegral.integral_of_le hab, Pi.sub_apply] using heq

/-- Pointwise integral trajectories become continuous L² trajectories. -/
theorem continuousOn_toLp_of_pointwise_integrals [IsProbabilityMeasure P]
    (Z v : ℝ → Ω → E) (hv : StronglyMeasurable (Function.uncurry v))
    (hZ₂ : ∀ t, MemLp (Z t) 2 P) (hv₂ : ∀ t, MemLp (v t) 2 P)
    {a b : ℝ} (hab : a ≤ b)
    (hV : IntervalIntegrable (fun t => (hv₂ t).toLp (v t)) volume a b)
    (heq : ∀ t ∈ Icc a b, ∀ᵐ ω ∂P, Z t ω - Z a ω = ∫ s in a..t, v s ω) :
    ContinuousOn (fun t => (hZ₂ t).toLp (Z t)) (Icc a b) := by
  have hc := (continuousOn_const (c := (hZ₂ a).toLp (Z a))).add
    (intervalIntegral.continuousOn_primitive_interval' hV left_mem_uIcc)
  rw [uIcc_of_le hab] at hc
  apply hc.congr
  intro t ht
  have hVt : IntervalIntegrable (fun t => (hv₂ t).toLp (v t)) volume a t := by
    apply hV.mono_set
    rw [uIcc_of_le ht.1, uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl ht.2
  have he := toLp_sub_eq_intervalIntegral v hv hv₂ ht.1 hVt (hZ₂ t) (hZ₂ a) (heq t ht)
  exact (eq_add_of_sub_eq he).trans (add_comm _ _)

/-- Actual sample-path derivatives supply the pointwise integral equation;
section integrability is derived from the mixed L¹/L² velocity hypothesis. -/
theorem pointwise_integral_equation_of_derivative [IsProbabilityMeasure P]
    (Z v : ℝ → Ω → E) (hv : StronglyMeasurable (Function.uncurry v))
    (hv₂ : ∀ t, MemLp (v t) 2 P) {a b : ℝ} (hab : a ≤ b)
    (hV : IntervalIntegrable (fun t => (hv₂ t).toLp (v t)) volume a b)
    (hZ : ∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Icc a b))
    (hderiv : ∀ᵐ ω ∂P, ∀ t ∈ Ioo a b, HasDerivAt (fun s => Z s ω) (v t ω) t) :
    ∀ᵐ ω ∂P, Z b ω - Z a ω = ∫ t in a..b, v t ω := by
  have hi := integrable_product_of_l1_l2 v hv hv₂ hV.1
  filter_upwards [hZ, hderiv, hi.prod_left_ae] with ω hZω hderivω hiω
  apply (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hZω hderivω _).symm
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr hiω

end SharpWasserstein.PointwiseTrajectory

namespace SharpWasserstein

/-- A pointwise random-trajectory integral equation gives the genuine W₂ length.
Joint measurability and an integrable L² velocity justify the lifting internally. -/
theorem wasserstein_length_of_pointwise_integral {Ω : Type*} [MeasurableSpace Ω] {d N : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ℝ → Ω → Configuration d N)
    (hZ₂ : ∀ t, MemLp (fun ω => configurationToEuclidean (Z t ω)) 2 P)
    (v : ℝ → Ω → EuclideanSpace ℝ (Fin N × Fin d))
    (hv : StronglyMeasurable (Function.uncurry v)) (hv₂ : ∀ t, MemLp (v t) 2 P)
    {a b : ℝ} (hab : a ≤ b)
    (hV : IntervalIntegrable (fun t => (hv₂ t).toLp (v t)) volume a b)
    (heq : ∀ᵐ ω ∂P, configurationToEuclidean (Z b ω) - configurationToEuclidean (Z a ω) =
      ∫ t in a..b, v t ω) :
    Real.sqrt (wassersteinSq (Measure.map (Z a) P) (Measure.map (Z b) P)).toReal ≤
      ∫ t in a..b, ‖(hv₂ t).toLp (v t)‖ := by
  have he := PointwiseTrajectory.toLp_sub_eq_intervalIntegral v hv hv₂ hab hV
    (hZ₂ b) (hZ₂ a) heq
  have h := wasserstein_length_of_l2_integral P
    (fun t => l2LiftConfiguration (Z t) (hZ₂ t))
    (fun t => (hv₂ t).toLp (v t)) hab hV he
  simpa only [law_l2LiftConfiguration] using h

/-- The extended-valued squared transport cost is bounded as well, so the result
does not rely on how `toReal` handles infinity. -/
theorem wassersteinSq_of_pointwise_integral {Ω : Type*} [MeasurableSpace Ω] {d N : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ℝ → Ω → Configuration d N)
    (hZ₂ : ∀ t, MemLp (fun ω => configurationToEuclidean (Z t ω)) 2 P)
    (v : ℝ → Ω → EuclideanSpace ℝ (Fin N × Fin d))
    (hv : StronglyMeasurable (Function.uncurry v)) (hv₂ : ∀ t, MemLp (v t) 2 P)
    {a b : ℝ} (hab : a ≤ b)
    (hV : IntervalIntegrable (fun t => (hv₂ t).toLp (v t)) volume a b)
    (heq : ∀ᵐ ω ∂P, configurationToEuclidean (Z b ω) - configurationToEuclidean (Z a ω) =
      ∫ t in a..b, v t ω) :
    wassersteinSq (Measure.map (Z a) P) (Measure.map (Z b) P) ≤
      ENNReal.ofReal ((∫ t in a..b, ‖(hv₂ t).toLp (v t)‖) ^ 2) := by
  have he := PointwiseTrajectory.toLp_sub_eq_intervalIntegral v hv hv₂ hab hV
    (hZ₂ b) (hZ₂ a) heq
  have h := wassersteinSq_of_l2_integral P
    (fun t => l2LiftConfiguration (Z t) (hZ₂ t))
    (fun t => (hv₂ t).toLp (v t)) hab hV he
  simpa only [law_l2LiftConfiguration] using h

/-- Smooth sample paths with a jointly measurable, time-integrable L² velocity
give a genuine squared Wasserstein bound, without assuming an L² derivative. -/
theorem wassersteinSq_of_pointwise_derivative {Ω : Type*} [MeasurableSpace Ω] {d N : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ℝ → Ω → Configuration d N)
    (hZ₂ : ∀ t, MemLp (fun ω => configurationToEuclidean (Z t ω)) 2 P)
    (v : ℝ → Ω → EuclideanSpace ℝ (Fin N × Fin d))
    (hv : StronglyMeasurable (Function.uncurry v)) (hv₂ : ∀ t, MemLp (v t) 2 P)
    {a b : ℝ} (hab : a ≤ b)
    (hV : IntervalIntegrable (fun t => (hv₂ t).toLp (v t)) volume a b)
    (hZ : ∀ᵐ ω ∂P, ContinuousOn (fun t => configurationToEuclidean (Z t ω)) (Icc a b))
    (hderiv : ∀ᵐ ω ∂P, ∀ t ∈ Ioo a b,
      HasDerivAt (fun s => configurationToEuclidean (Z s ω)) (v t ω) t) :
    wassersteinSq (Measure.map (Z a) P) (Measure.map (Z b) P) ≤
      ENNReal.ofReal ((∫ t in a..b, ‖(hv₂ t).toLp (v t)‖) ^ 2) := by
  apply wassersteinSq_of_pointwise_integral P Z hZ₂ v hv hv₂ hab hV
  exact PointwiseTrajectory.pointwise_integral_equation_of_derivative
    (fun t ω => configurationToEuclidean (Z t ω)) v hv hv₂ hab hV hZ hderiv

end SharpWasserstein
