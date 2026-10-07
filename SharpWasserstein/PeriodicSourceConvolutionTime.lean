module

public import SharpWasserstein.Compat
public import SharpWasserstein.PeriodicSourceConvolutionGenerator
public import SharpWasserstein.PropagatedSourceEquation
public import SharpWasserstein.PeriodicConvolutionWeak
public import SharpWasserstein.PeriodicBochner

@[expose] public section

/-! Genuine pointwise time derivatives of the periodic smoothing of a
Brownian-propagated finite-energy source. Time continuity is derived by a
second application of the actual weak equation, rather than assumed. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal ContDiff Topology Interval
namespace SharpWasserstein.PeriodicSourceConvolution
open WeightedTangent NoiseAverage PropagatedSourceEquation FlowSemigroupDerivative
open PeriodicIntegrationByParts PeriodicPositiveKernel PeriodicBochner

/-- The actual reflected periodic test of a source, in Euclidean coordinates. -/
def euclideanKernelTest {n : ℕ} (κ : ℝ) (x : Coordinates n) (y : Point n) : ℝ :=
  kernel κ (x-coordinateEquiv n y)

theorem euclideanKernelTest_smooth {n : ℕ} (κ : ℝ) (x : Coordinates n) :
    ContDiff ℝ ∞ (euclideanKernelTest κ x) :=
  (kernel_smooth n κ).comp (contDiff_const.sub (coordinateEquiv n).contDiff)

theorem euclideanKernelTest_bounded {n : ℕ} (κ : ℝ) (x : Coordinates n) :
    AllDerivativesBounded (euclideanKernelTest κ x) := by
  let L := (coordinateEquiv n).toContinuousLinearMap
  let a : Point n → Coordinates n := fun y => x-L y
  have ha : ContDiff ℝ ∞ a := contDiff_const.sub L.contDiff
  have hd : fderiv ℝ a = fun _ => -L := by
    funext y
    convert ((hasFDerivAt_const x y).sub L.hasFDerivAt).fderiv using 1 <;>
      first | rfl | simp only [zero_sub]
  apply AllDerivativesBounded.comp_of_fderiv (kernel_smooth n κ) ha (kernel_derivatives_bounded n κ)
  rw [hd]
  exact allDerivativesBounded_const _

/-- Reflection contributes the required minus sign in source convolution. -/
theorem fderiv_euclideanKernelTest {n : ℕ} (κ : ℝ) (x : Coordinates n) (y v : Point n) :
    fderiv ℝ (euclideanKernelTest κ x) y v =
      -fderiv ℝ (kernel κ) (x-coordinateEquiv n y) (coordinateEquiv n v) := by
  have ha := (hasFDerivAt_const x y).sub (coordinateEquiv n).toContinuousLinearMap.hasFDerivAt
  have hk := ((kernel_smooth n κ).differentiable (by simp) (x-coordinateEquiv n y)).hasFDerivAt
  have hd := hk.comp y ha
  simp only [Function.comp_def] at hd
  have he := congrArg (fun A : Point n →L[ℝ] ℝ => A v) hd.fderiv
  simp only [Pi.sub_apply,ContinuousLinearMap.comp_apply,
    zero_sub,neg_apply,map_neg] at he
  convert he using 1 <;> rfl

section Brownian
variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  {b : Configuration d N → Configuration d N} {M K M' K' : ℝ≥0}
  (hv : Continuous (Function.uncurry (fun _ : ℝ => b)))
  (hb : ∀ _ : ℝ,∀ x,‖b x‖ ≤ M) (hl : ∀ _ : ℝ,LipschitzWith K b)
  (hv' : Continuous (Function.uncurry (fun _ : ℝ => equivDrift (configurationEuclidean d N) b)))
  (hb' : ∀ _ : ℝ,∀ y,‖equivDrift (configurationEuclidean d N) b y‖ ≤ M')
  (hl' : ∀ _ : ℝ,LipschitzWith K' (equivDrift (configurationEuclidean d N) b))
  {T : ℝ} (hT : 0 ≤ T) (hbs : ContDiff ℝ ∞ b) (hB : AllDerivativesBounded b)
  (μ : Measure (Point (N*d))) [IsFiniteMeasure μ]
  {u : Point (N*d) → Point (N*d)} (hu : MemLp u 2 μ)
include hv hb hl hbs hB hu

/-- The bounded smooth extension obeys the actual homogeneous source equation. -/
theorem brownian_action_equation
    {F : Point (N*d) → ℝ} (hF : ContDiff ℝ ∞ F) (hBF : AllDerivativesBounded F)
    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) :
    IntervalIntegrable (action hv' hb' hl' hT (euclideanBrownianPathLaw d N T) μ u
      (euclideanGenerator b F)) volume s t ∧
    action hv' hb' hl' hT (euclideanBrownianPathLaw d N T) μ u F t-
      action hv' hb' hl' hT (euclideanBrownianPathLaw d N T) μ u F s =
      ∫ r in s..t,action hv' hb' hl' hT (euclideanBrownianPathLaw d N T) μ u (euclideanGenerator b F) r := by
  obtain ⟨C,_,hC⟩ := hBF.bounded
  obtain ⟨L,hL0,hL⟩ := hBF.fderiv.bounded
  have hG := euclideanGenerator_smooth hbs hF
  have hBG := euclideanGenerator_bounded hbs hB hF hBF
  obtain ⟨D,_,hD⟩ := hBG.bounded
  obtain ⟨L',hL0',hL'⟩ := hBG.fderiv.bounded
  exact action_interval_eq hv' hb' hl' hT _ μ
    (equivDrift_smooth _ hbs) (equivDrift_allDerivativesBounded _ hbs hB)
    (hF.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)) hC (L := NNReal.mk L hL0) hL
    (hG.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)) hD (L' := NNReal.mk L' hL0') hL' hu hs ht
    (euclidean_brownian_primal_bounded hv hb hl hT hv' hb' hl' hF hBF hs ht)

/-- Repeated genuine generator equations prove the required time regularity. -/
theorem brownian_action_lipschitzOn
    {F : Point (N*d) → ℝ} (hF : ContDiff ℝ ∞ F) (hBF : AllDerivativesBounded F) :
    ∃ C : ℝ≥0,LipschitzOnWith C
      (action hv' hb' hl' hT (euclideanBrownianPathLaw d N T) μ u F) (Icc 0 T) := by
  obtain ⟨C,_,hC⟩ := hBF.bounded
  obtain ⟨L,hL0,hL⟩ := hBF.fderiv.bounded
  have hG := euclideanGenerator_smooth hbs hF
  have hBG := euclideanGenerator_bounded hbs hB hF hBF
  obtain ⟨D,_,hD⟩ := hBG.bounded
  obtain ⟨L',hL0',hL'⟩ := hBG.fderiv.bounded
  let A : ℝ := L'*Real.exp ((K':ℝ)*T)*(∫ x,‖u x‖ ∂μ)
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg hL0' (Real.exp_pos _).le) (integral_nonneg fun _ => norm_nonneg _)
  refine ⟨NNReal.mk A hA,LipschitzOnWith.of_dist_le_mul ?_⟩
  intro t ht s hs
  have hh := action_sub_norm_le hv' hb' hl' hT (euclideanBrownianPathLaw d N T) μ
    (equivDrift_smooth _ hbs) (equivDrift_allDerivativesBounded _ hbs hB)
    (hF.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)) hC (L := NNReal.mk L hL0) hL
    (hG.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)) hD (L' := NNReal.mk L' hL0') hL' hu hs ht
    (euclidean_brownian_primal_bounded hv hb hl hT hv' hb' hl' hF hBF hs ht)
  simpa only [dist_eq_norm,Real.norm_eq_abs,NNReal.coe_mk,A,mul_comm] using hh

/-- Pointwise differentiation of the actual bounded source action, including
the one-sided derivatives at the horizon endpoints. -/
theorem brownian_action_hasDerivWithinAt
    {F : Point (N*d) → ℝ} (hF : ContDiff ℝ ∞ F) (hBF : AllDerivativesBounded F)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (action hv' hb' hl' hT (euclideanBrownianPathLaw d N T) μ u F)
      (action hv' hb' hl' hT (euclideanBrownianPathLaw d N T) μ u (euclideanGenerator b F) t) (Icc 0 T) t := by
  let A := action hv' hb' hl' hT (euclideanBrownianPathLaw d N T) μ u F
  let G := action hv' hb' hl' hT (euclideanBrownianPathLaw d N T) μ u (euclideanGenerator b F)
  obtain ⟨C,hC⟩ := brownian_action_lipschitzOn hv hb hl hv' hb' hl' hT hbs hB μ hu
    (euclideanGenerator_smooth hbs hF) (euclideanGenerator_bounded hbs hB hF hBF)
  have hGc : Continuous (fun r => G (projIcc 0 T hT r)) :=
    hC.continuousOn.comp_continuous (continuous_subtype_val.comp continuous_projIcc) (fun r => (projIcc 0 T hT r).property)
  let Gc := fun r => G (projIcc 0 T hT r)
  have he (s : ℝ) (hs : s ∈ Icc 0 T) : A s = A 0+∫ r in (0:ℝ)..s,Gc r := by
    have hh := (brownian_action_equation hv hb hl hv' hb' hl' hT hbs hB μ hu hF hBF
      (show (0:ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩) hs).2
    have hi : (∫ r in (0:ℝ)..s,Gc r) = ∫ r in (0:ℝ)..s,G r := by
      apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le hs.1] at hr
      simp only [Gc,projIcc_of_mem _ (show r ∈ Icc 0 T from ⟨hr.1,hr.2.trans hs.2⟩)]
    rw [hi]
    dsimp only [A,G] at *
    linarith
  have hd : HasDerivAt (fun s => A 0+∫ r in (0:ℝ)..s,Gc r) (Gc t) t :=
    (intervalIntegral.integral_hasDerivAt_right (hGc.intervalIntegrable 0 t)
      hGc.stronglyMeasurable.stronglyMeasurableAtFilter hGc.continuousAt).const_add _
  have hh := hd.hasDerivWithinAt.congr_of_mem he ht
  simpa only [Gc,projIcc_of_mem _ ht] using hh

theorem brownian_action_hasDerivAt
    {F : Point (N*d) → ℝ} (hF : ContDiff ℝ ∞ F) (hBF : AllDerivativesBounded F)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt (action hv' hb' hl' hT (euclideanBrownianPathLaw d N T) μ u F)
      (action hv' hb' hl' hT (euclideanBrownianPathLaw d N T) μ u (euclideanGenerator b F) t) t :=
  (brownian_action_hasDerivWithinAt hv hb hl hv' hb' hl' hT hbs hB μ hu hF hBF
    ⟨ht.1.le,ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

omit hv hb hl hbs hB hu in
/-- Literal periodic convolution of the propagated source, evaluated by its
actual semigroup differential on the reflected product kernel. -/
def convolvedSource (κ : ℝ) (t : ℝ) (x : Coordinates (N*d)) : ℝ :=
  action hv' hb' hl' hT (euclideanBrownianPathLaw d N T) μ u (euclideanKernelTest κ x) t

omit hv hb hl in
/-- The smoothing is literally the negative derivative of the periodic kernel
against the actual pushed Jacobian flux, even for singular initial laws. -/
theorem convolvedSource_eq_randomFlux (κ : ℝ) (x : Coordinates (N*d))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    convolvedSource hv' hb' hl' hT μ (u := u) κ t x =
      -(∫ q : Point (N*d) × C(Icc 0 T,Point (N*d)),
        fderiv ℝ (kernel κ)
          (x-coordinateEquiv (N*d) (PropagatedFlux.Flow.endpoint hv' hb' hl' hT (t := t) q))
          (coordinateEquiv (N*d) (PropagatedFlux.Flow.velocity hv' hb' hl' hT (t := t) u q))
          ∂μ.prod (euclideanBrownianPathLaw d N T)) := by
  have hF := euclideanKernelTest_smooth κ x
  have hBF := euclideanKernelTest_bounded κ x
  obtain ⟨C,_,hC⟩ := hBF.bounded
  obtain ⟨L,hL0,hL⟩ := hBF.fderiv.bounded
  have he := action_eq_randomFlux hv' hb' hl' hT (euclideanBrownianPathLaw d N T) μ
    (equivDrift_smooth _ hbs) (equivDrift_allDerivativesBounded _ hbs hB)
    (hF.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)) hC (L := NNReal.mk L hL0) hL hu ht
  change convolvedSource hv' hb' hl' hT μ (u := u) κ t x = _ at he
  rw [he]
  simp_rw [fderiv_euclideanKernelTest]
  rw [integral_neg]
  rfl

theorem convolvedSource_hasDerivWithinAt (κ : ℝ) (x : Coordinates (N*d))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (fun r => convolvedSource hv' hb' hl' hT μ (u := u) κ r x)
      (action hv' hb' hl' hT (euclideanBrownianPathLaw d N T) μ u
        (euclideanGenerator b (euclideanKernelTest κ x)) t) (Icc 0 T) t :=
  brownian_action_hasDerivWithinAt hv hb hl hv' hb' hl' hT hbs hB μ hu
    (euclideanKernelTest_smooth κ x) (euclideanKernelTest_bounded κ x) ht

theorem convolvedSource_hasDerivAt (κ : ℝ) (x : Coordinates (N*d))
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r => convolvedSource hv' hb' hl' hT μ (u := u) κ r x)
      (action hv' hb' hl' hT (euclideanBrownianPathLaw d N T) μ u
        (euclideanGenerator b (euclideanKernelTest κ x)) t) t :=
  brownian_action_hasDerivAt hv hb hl hv' hb' hl' hT hbs hB μ hu
    (euclideanKernelTest_smooth κ x) (euclideanKernelTest_bounded κ x) ht
end Brownian
end SharpWasserstein.PeriodicSourceConvolution
