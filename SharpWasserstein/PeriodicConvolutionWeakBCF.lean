import SharpWasserstein.PeriodicConvolutionWeak
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! Uniform spatial bounds for the genuine periodic convolution evolution.
Translation of a single bounded smooth test provides the common derivative
constants required by the proved time-generator modulus. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal ContDiff Interval BoundedContinuousFunction
namespace SharpWasserstein.PeriodicConvolution
open WeightedTangent NoiseAverage PeriodicIntegrationByParts PeriodicPositiveKernel

variable {d N : ℕ}

theorem kernelTest_eq_translate (κ : ℝ) (x : Coordinates (N*d)) :
    kernelTest (d := d) (N := N) κ x = fun y =>
      kernelTest κ 0 (y + -(configurationFlatten d N).symm x) := by
  funext y
  change kernel κ (x-configurationFlatten d N y) =
    kernel κ (0-configurationFlatten d N (y + -(configurationFlatten d N).symm x))
  simp only [← flattenCLM_apply, map_add, map_neg]
  simp only [flattenCLM_apply, (configurationFlatten d N).apply_symm_apply]
  congr 1
  abel

theorem lipschitz_translate {E F : Type*} [SeminormedAddCommGroup E]
    [PseudoMetricSpace F] {L : ℝ≥0} {f : E → F} (hf : LipschitzWith L f) (a : E) :
    LipschitzWith L (fun y => f (y+a)) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  simpa only [dist_add_right] using hf.dist_le_mul (y+a) (z+a)

/-- All translations share the same first three derivative Lipschitz bounds;
none of these constants depends on the convolution position. -/
theorem kernelTest_uniform_lipschitz (κ : ℝ) :
    ∃ L L₁ L₂ : ℝ≥0, ∀ x : Coordinates (N*d),
      LipschitzWith L (kernelTest (d := d) (N := N) κ x) ∧
      LipschitzWith L₁ (fderiv ℝ (kernelTest (d := d) (N := N) κ x)) ∧
      LipschitzWith L₂ (fderiv ℝ (fderiv ℝ (kernelTest (d := d) (N := N) κ x))) := by
  let f := kernelTest (d := d) (N := N) κ 0
  have hf : ContDiff ℝ ∞ f := kernelTest_smooth κ 0
  have hB : AllDerivativesBounded f := kernelTest_derivatives_bounded κ 0
  have hdf := (contDiff_infty_iff_fderiv.mp hf).2
  have hddf := (contDiff_infty_iff_fderiv.mp hdf).2
  obtain ⟨L,hL⟩ := hB.lipschitz (hf.differentiable (by simp))
  obtain ⟨L₁,hL₁⟩ := hB.fderiv.lipschitz (hdf.differentiable (by simp))
  obtain ⟨L₂,hL₂⟩ := hB.fderiv.fderiv.lipschitz (hddf.differentiable (by simp))
  refine ⟨L,L₁,L₂,fun x => ?_⟩
  let a := -(configurationFlatten d N).symm x
  have he : kernelTest (d := d) (N := N) κ x = fun y => f (y+a) := kernelTest_eq_translate κ x
  have he₁ : fderiv ℝ (kernelTest (d := d) (N := N) κ x) =
      fun y => fderiv ℝ f (y+a) := by
    rw [he]
    funext y
    exact fderiv_comp_add_right a
  have he₂ : fderiv ℝ (fderiv ℝ (kernelTest (d := d) (N := N) κ x)) =
      fun y => fderiv ℝ (fderiv ℝ f) (y+a) := by
    rw [he₁]
    funext y
    exact fderiv_comp_add_right a
  rw [he₂,he₁,he]
  exact ⟨lipschitz_translate hL a,lipschitz_translate hL₁ a,lipschitz_translate hL₂ a⟩

variable [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  {v : ℝ → Configuration d N → Configuration d N} {P : ℝ → Measure (Configuration d N)}

/-- The actual time generator modulus is uniform over every spatial translate. -/
theorem evolutionDensity_uniform_generator (h : WeakEvolution v P)
    {K M : ℝ≥0} (hvC : Continuous (Function.uncurry v))
    (hv : ∀ t,LipschitzWith K (v t)) (hM : ∀ t y,‖v t y‖ ≤ M)
    (κ T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, dist s t < δ →
      ∀ x : Coordinates (N*d),
        ‖(∫ y,generator (v s) (kernelTest κ x) y ∂P s)-
          (∫ y,generator (v t) (kernelTest κ x) y ∂P t)‖ < ε := by
  obtain ⟨L,L₁,L₂,hL⟩ := kernelTest_uniform_lipschitz (d := d) (N := N) κ
  obtain ⟨δ,hδ,hd⟩ := WeakEvolution.uniform_time_generator_expectation h hvC hv hM T L L₁ L₂ hε
  refine ⟨δ,hδ,fun s hs t ht hst x => ?_⟩
  exact hd s hs t ht hst (kernelTest κ x)
    ((kernelTest_smooth κ x).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (hL x).1 (hL x).2.1 (hL x).2.2

/-- Two-sided scalar weak-equation remainders are controlled uniformly in position. -/
theorem evolutionDensity_uniform_remainder (h : WeakEvolution v P)
    {K M : ℝ≥0} (hvC : Continuous (Function.uncurry v))
    (hv : ∀ t,LipschitzWith K (v t)) (hM : ∀ t y,‖v t y‖ ≤ M)
    (κ T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, dist s t < δ →
      ∀ x : Coordinates (N*d),
        ‖evolutionDensity κ P s x-evolutionDensity κ P t x-
          (s-t)*(∫ y,generator (v t) (kernelTest κ x) y ∂P t)‖ ≤ |s-t| * ε := by
  obtain ⟨δ,hδ,hd⟩ := evolutionDensity_uniform_generator h hvC hv hM κ T hε
  refine ⟨δ,hδ,fun s hs t ht hst x => ?_⟩
  have heq := evolutionDensity_equation h hv hM κ x ht.1 hs.1
  have he : evolutionDensity κ P s x-evolutionDensity κ P t x-
      (s-t)*(∫ y,generator (v t) (kernelTest κ x) y ∂P t) =
      ∫ r in t..s, (∫ y,generator (v r) (kernelTest κ x) y ∂P r)-
        (∫ y,generator (v t) (kernelTest κ x) y ∂P t) := by
    rw [intervalIntegral.integral_sub heq.1 intervalIntegrable_const,
      intervalIntegral.integral_const,heq.2,smul_eq_mul]
  rw [he]
  have hb : ∀ r ∈ Ι t s,
      ‖(∫ y,generator (v r) (kernelTest κ x) y ∂P r)-
        (∫ y,generator (v t) (kernelTest κ x) y ∂P t)‖ ≤ ε := by
    intro r hr
    have hr' : r ∈ uIcc t s := uIoc_subset_uIcc hr
    have hrT := uIcc_subset_Icc ht hs hr'
    apply (hd r hrT t ht ?_ x).le
    simpa only [dist_comm] using (Real.dist_left_le_of_mem_uIcc hr').trans_lt
      (by simpa only [dist_comm] using hst)
  simpa only [mul_comm] using intervalIntegral.norm_integral_le_of_norm_le_const hb

/-- Spatial continuity of the derivative follows from uniform approximation
by actual continuous density secants, including at the initial time. -/
theorem evolutionDensity_generator_continuous_space (h : WeakEvolution v P)
    {K M : ℝ≥0} (hvC : Continuous (Function.uncurry v))
    (hv : ∀ t,LipschitzWith K (v t)) (hM : ∀ t y,‖v t y‖ ≤ M)
    (κ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    Continuous (fun x : Coordinates (N*d) => ∫ y,generator (v t) (kernelTest κ x) y ∂P t) := by
  have hcont (s : ℝ) (hs : 0 ≤ s) : Continuous (evolutionDensity κ P s) := by
    have hc := (evolutionDensity_joint_continuous_nonnegExtension h κ).comp
      (continuous_const.prodMk continuous_id : Continuous (fun x : Coordinates (N*d) => (s,x)))
    simpa only [Function.comp_def,max_eq_right hs] using hc
  apply continuous_of_uniform_approx_of_continuous
  intro u hu
  obtain ⟨ε,hε,hεu⟩ := Metric.mem_uniformity_dist.mp hu
  obtain ⟨δ,hδ,hd⟩ := evolutionDensity_uniform_remainder h hvC hv hM κ (t+1) (half_pos hε)
  let q := min δ 1 / 2
  have hq : 0 < q := half_pos (lt_min hδ zero_lt_one)
  have hqδ : q < δ := by dsimp [q]; linarith [min_le_left δ 1]
  have hq1 : q ≤ 1 := by dsimp [q]; linarith [min_le_right δ 1]
  refine ⟨fun x => (evolutionDensity κ P (t+q) x-evolutionDensity κ P t x)/q,
    ((hcont (t+q) (by linarith)).sub (hcont t ht)).div_const q,fun x => hεu ?_⟩
  have hb := hd (t+q) ⟨by linarith,by linarith⟩ t ⟨ht,by linarith⟩
    (by simpa only [Real.dist_eq,add_sub_cancel_left,abs_of_pos hq] using hqδ) x
  simp only [add_sub_cancel_left,abs_of_pos hq] at hb
  have he : (∫ y,generator (v t) (kernelTest κ x) y ∂P t)-
      (evolutionDensity κ P (t+q) x-evolutionDensity κ P t x)/q =
      -(evolutionDensity κ P (t+q) x-evolutionDensity κ P t x-
        q*(∫ y,generator (v t) (kernelTest κ x) y ∂P t))/q := by
    field_simp
    ring
  rw [dist_eq_norm,he,norm_div,norm_neg,Real.norm_eq_abs q,abs_of_pos hq]
  exact (div_le_div_of_nonneg_right hb hq.le).trans_lt (by
    rw [mul_div_cancel_left₀ _ hq.ne']
    exact half_lt_self hε)

omit [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))] in
/-- A common finite bound for the genuine generator density. -/
theorem evolutionDensity_generator_bounded (h : WeakEvolution v P)
    {M : ℝ≥0} (hM : ∀ t y,‖v t y‖ ≤ M) (κ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, 0 ≤ t → ∀ x : Coordinates (N*d),
      ‖∫ y,generator (v t) (kernelTest κ x) y ∂P t‖ ≤ C := by
  obtain ⟨L,L₁,L₂,hL⟩ := kernelTest_uniform_lipschitz (d := d) (N := N) κ
  refine ⟨(N*d:ℕ)*(L₁:ℝ)+L*M,by positivity,fun t ht x => ?_⟩
  letI := h.probability t ht
  simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const (μ := P t)
    (Eventually.of_forall (generator_norm_le_of_derivatives
      ((kernelTest_smooth κ x).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
      (hL x).1 (hL x).2.1 (hM t)))

/-- The actual density curve in the Euclidean bounded-continuous-function
space used by the weighted energy differentiation theorem. Times before zero
are extended constantly, so this is an everywhere-defined Banach-space curve. -/
def evolutionDensityBCF (h : WeakEvolution v P) (κ t : ℝ) : Point (N*d) →ᵇ ℝ := by
  letI := h.probability (max 0 t) (le_max_left _ _)
  letI : IsProbabilityMeasure ((P (max 0 t)).map (configurationFlatten d N)) :=
    Measure.isProbabilityMeasure_map (configurationFlatten d N).measurable.aemeasurable
  apply BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => evolutionDensity κ P (max 0 t) (WithLp.ofLp x))
    ((density_smooth κ ((P (max 0 t)).map (configurationFlatten d N))).continuous.comp
      (PiLp.continuous_ofLp 2 (fun _ : Fin (N*d) => ℝ)))
    ((Real.exp |κ|/normalizer κ)^(N*d))
  intro x
  dsimp only [evolutionDensity]
  rw [Real.norm_eq_abs,abs_of_pos (density_pos κ _ _)]
  exact (density_bounds κ _ _).2

omit [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))] in
@[simp] theorem evolutionDensityBCF_apply (h : WeakEvolution v P) (κ t : ℝ) (x : Point (N*d)) :
    evolutionDensityBCF h κ t x = evolutionDensity κ P (max 0 t) (WithLp.ofLp x) := rfl

/-- The actual generator expectation, packaged in the same bounded continuous
function space; spatial continuity was proved from uniform weak secants. -/
def evolutionGeneratorBCF (h : WeakEvolution v P)
    {K M : ℝ≥0} (hvC : Continuous (Function.uncurry v))
    (hv : ∀ t,LipschitzWith K (v t)) (hM : ∀ t y,‖v t y‖ ≤ M)
    (κ t : ℝ) : Point (N*d) →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => ∫ y,generator (v (max 0 t)) (kernelTest κ (WithLp.ofLp x)) y ∂P (max 0 t))
    ((evolutionDensity_generator_continuous_space h hvC hv hM κ (le_max_left 0 t)).comp
      (PiLp.continuous_ofLp 2 (fun _ : Fin (N*d) => ℝ)))
    (evolutionDensity_generator_bounded h hM κ).choose
    (fun x => (evolutionDensity_generator_bounded h hM κ).choose_spec.2
      (max 0 t) (le_max_left 0 t) (WithLp.ofLp x))

@[simp] theorem evolutionGeneratorBCF_apply (h : WeakEvolution v P)
    {K M : ℝ≥0} (hvC : Continuous (Function.uncurry v))
    (hv : ∀ t,LipschitzWith K (v t)) (hM : ∀ t y,‖v t y‖ ≤ M)
    (κ t : ℝ) (x : Point (N*d)) :
    evolutionGeneratorBCF h hvC hv hM κ t x =
      ∫ y,generator (v (max 0 t)) (kernelTest κ (WithLp.ofLp x)) y ∂P (max 0 t) := rfl

/-- Genuine Banach-space time differentiability follows from the uniform
translated-test remainder. No Banach derivative is assumed. -/
theorem evolutionDensityBCF_hasDerivWithinAt (h : WeakEvolution v P)
    {K M : ℝ≥0} (hvC : Continuous (Function.uncurry v))
    (hv : ∀ t,LipschitzWith K (v t)) (hM : ∀ t y,‖v t y‖ ≤ M)
    (κ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (evolutionDensityBCF h κ)
      (evolutionGeneratorBCF h hvC hv hM κ t) (Ici 0) t := by
  rw [hasDerivWithinAt_iff_isLittleO,Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ,hδ,hd⟩ := evolutionDensity_uniform_remainder h hvC hv hM κ (t+1) hε
  have hd' : 0 < min δ 1 := lt_min hδ zero_lt_one
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Metric.ball_mem_nhds t hd')] with s hs hst
  have hsmall : dist s t < min δ 1 := hst
  have hsT : s ∈ Icc 0 (t+1) := ⟨hs,by
    have hh := (abs_lt.mp (show |s-t| < 1 from hsmall.trans_le (min_le_right _ _))).2
    linarith⟩
  apply (BoundedContinuousFunction.norm_le (mul_nonneg hε.le (norm_nonneg _))).mpr
  intro x
  have hh := hd s hsT t ⟨ht,by linarith⟩ (hsmall.trans_le (min_le_left _ _)) (WithLp.ofLp x)
  simpa only [BoundedContinuousFunction.sub_apply,BoundedContinuousFunction.smul_apply,
    evolutionDensityBCF_apply,evolutionGeneratorBCF_apply,max_eq_right (show 0 ≤ s from hs),max_eq_right ht,
    smul_eq_mul,Real.norm_eq_abs,mul_comm] using hh

/-- The positive-time derivative needed in periodic weighted-energy
calculus holds in the full bounded continuous function norm. -/
theorem evolutionDensityBCF_hasDerivAt (h : WeakEvolution v P)
    {K M : ℝ≥0} (hvC : Continuous (Function.uncurry v))
    (hv : ∀ t,LipschitzWith K (v t)) (hM : ∀ t y,‖v t y‖ ≤ M)
    (κ : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (evolutionDensityBCF h κ) (evolutionGeneratorBCF h hvC hv hM κ t) t :=
  (evolutionDensityBCF_hasDerivWithinAt h hvC hv hM κ ht.le).hasDerivAt (Ici_mem_nhds ht)

/-- The derivative curve is uniformly continuous on every compact time
interval in the full supremum norm. -/
theorem evolutionGeneratorBCF_uniformContinuousOn (h : WeakEvolution v P)
    {K M : ℝ≥0} (hvC : Continuous (Function.uncurry v))
    (hv : ∀ t,LipschitzWith K (v t)) (hM : ∀ t y,‖v t y‖ ≤ M)
    (κ T : ℝ) : UniformContinuousOn (evolutionGeneratorBCF h hvC hv hM κ) (Icc 0 T) := by
  apply Metric.uniformContinuousOn_iff.mpr
  intro ε hε
  obtain ⟨δ,hδ,hd⟩ := evolutionDensity_uniform_generator h hvC hv hM κ T (half_pos hε)
  refine ⟨δ,hδ,fun s hs t ht hst => ?_⟩
  rw [dist_eq_norm]
  apply lt_of_le_of_lt ?_ (half_lt_self hε)
  apply (BoundedContinuousFunction.norm_le (half_pos hε).le).mpr
  intro x
  simpa only [BoundedContinuousFunction.sub_apply,evolutionGeneratorBCF_apply,
    max_eq_right hs.1,max_eq_right ht.1] using (hd s hs t ht hst (WithLp.ofLp x)).le

theorem evolutionGeneratorBCF_continuousOn (h : WeakEvolution v P)
    {K M : ℝ≥0} (hvC : Continuous (Function.uncurry v))
    (hv : ∀ t,LipschitzWith K (v t)) (hM : ∀ t y,‖v t y‖ ≤ M)
    (κ : ℝ) : ContinuousOn (evolutionGeneratorBCF h hvC hv hM κ) (Ici 0) := by
  intro t ht
  have hc := (evolutionGeneratorBCF_uniformContinuousOn h hvC hv hM κ (t+1)).continuousOn
    t (show t ∈ Icc 0 (t+1) from ⟨ht,by linarith⟩)
  apply hc.mono_of_mem_nhdsWithin
  rw [← Ici_inter_Iic]
  exact inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Iic_mem_nhds (by linarith : t < t+1)))

theorem evolutionDensityBCF_continuousOn (h : WeakEvolution v P)
    {K M : ℝ≥0} (hvC : Continuous (Function.uncurry v))
    (hv : ∀ t,LipschitzWith K (v t)) (hM : ∀ t y,‖v t y‖ ≤ M)
    (κ : ℝ) : ContinuousOn (evolutionDensityBCF h κ) (Ici 0) :=
  fun _ ht => (evolutionDensityBCF_hasDerivWithinAt h hvC hv hM κ ht).continuousWithinAt

omit [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))] in
/-- Strict positivity and a common finite upper bound hold at every time,
exactly as required to apply the weighted Hilbert-space energy theorem. -/
theorem evolutionDensityBCF_bounds (h : WeakEvolution v P) (κ t : ℝ) (x : Point (N*d)) :
    (Real.exp (-|κ|)/normalizer κ)^(N*d) ≤ evolutionDensityBCF h κ t x ∧
      evolutionDensityBCF h κ t x ≤ (Real.exp |κ|/normalizer κ)^(N*d) := by
  letI := h.probability (max 0 t) (le_max_left _ _)
  letI : IsProbabilityMeasure ((P (max 0 t)).map (configurationFlatten d N)) :=
    Measure.isProbabilityMeasure_map (configurationFlatten d N).measurable.aemeasurable
  exact density_bounds κ _ _

end SharpWasserstein.PeriodicConvolution
