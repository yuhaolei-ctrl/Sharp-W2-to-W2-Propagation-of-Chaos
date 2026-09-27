import SharpWasserstein.PeriodicSourceConvolutionModulus
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! The actual source convolution curve is differentiable in the full
bounded-continuous-function norm. This does not assert an extension of scalar
source integration to arbitrary nonperiodic cube gradients. -/
set_option maxHeartbeats 800000
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal ContDiff Topology Interval BoundedContinuousFunction
namespace SharpWasserstein.PeriodicSourceConvolution
open WeightedTangent NoiseAverage PropagatedSourceEquation FlowSemigroupDerivative
open PeriodicIntegrationByParts PeriodicBochner

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

omit [IsFiniteMeasure μ] [BorelSpace (Point (N*d))] in
theorem action_clamped (F : Point (N*d) → ℝ) (r : ℝ) :
    action hv' hb' hl' hT (euclideanBrownianPathLaw d N T) μ u F (projIcc 0 T hT r) =
      action hv' hb' hl' hT (euclideanBrownianPathLaw d N T) μ u F r := by
  unfold action clampedExpectation
  rw [projIcc_of_mem _ (projIcc 0 T hT r).property]

section Parameter
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  (f : P → Point (N*d) → ℝ)
  (hf : ContDiff ℝ ∞ (Function.uncurry f)) (hBf : UniformDerivatives f)
include hbs hB hu hf hBf

/-- Spatial continuity at all clamped times follows from the actual JV
integral and the common derivative bounds. -/
theorem action_continuous_param_all_time (r : ℝ) :
    Continuous (fun p => action hv' hb' hl' hT (euclideanBrownianPathLaw d N T) μ u (f p) r) := by
  have hh := action_continuous_param hv' hb' hl' hT (euclideanBrownianPathLaw d N T) μ
    (equivDrift_smooth _ hbs) (equivDrift_allDerivativesBounded _ hbs hB) hf hBf hu
    (projIcc 0 T hT r).property
  simpa only [action_clamped hv' hb' hl' hT μ] using hh

/-- The genuine source action family, bundled with proved continuity and
uniform boundedness in the whole spatial parameter. -/
def actionBCF (r : ℝ) : P →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p => action hv' hb' hl' hT (euclideanBrownianPathLaw d N T) μ u (f p) r)
    (action_continuous_param_all_time hv' hb' hl' hT hbs hB μ hu f hf hBf r)
    (uniform_action_bound hv' hb' hl' hT hbs hB μ hu
      (fun _p => hf.comp (contDiff_const.prodMk contDiff_id)) hBf).choose
    (fun p => (uniform_action_bound hv' hb' hl' hT hbs hB μ hu
      (fun _p => hf.comp (contDiff_const.prodMk contDiff_id)) hBf).choose_spec.2 r p)

@[simp] theorem actionBCF_apply (r : ℝ) (p : P) :
    actionBCF hv' hb' hl' hT hbs hB μ hu f hf hBf r p =
      action hv' hb' hl' hT (euclideanBrownianPathLaw d N T) μ u (f p) r := rfl

include hv hb hl
/-- The uniform quadratic remainder gives the actual Banach derivative. -/
theorem actionBCF_hasDerivWithinAt {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (actionBCF hv' hb' hl' hT hbs hB μ hu f hf hBf)
      (actionBCF hv' hb' hl' hT hbs hB μ hu (fun p => euclideanGenerator b (f p))
        (joint_euclideanGenerator hf hbs)
        (uniform_euclideanGenerator hbs hB (fun _p => hf.comp (contDiff_const.prodMk contDiff_id)) hBf) t)
      (Icc 0 T) t := by
  obtain ⟨C,hC,hrem⟩ := uniform_action_remainder hv hb hl hv' hb' hl' hT hbs hB μ hu
    (fun _p => hf.comp (contDiff_const.prodMk contDiff_id)) hBf
  rw [hasDerivWithinAt_iff_isLittleO,Asymptotics.isLittleO_iff]
  intro ε hε
  have hδ : 0 < ε/(C+1) := div_pos hε (by linarith)
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Metric.ball_mem_nhds t hδ)] with s hs hst
  apply (BoundedContinuousFunction.norm_le (mul_nonneg hε.le (norm_nonneg _))).mpr
  intro p
  have hh := hrem s hs t ht p
  have hsmall : |s-t| < ε/(C+1) := by simpa only [Metric.mem_ball,Real.dist_eq] using hst
  have hmul : |s-t| * (C+1) < ε := (lt_div_iff₀ (by linarith : 0 < C+1)).mp hsmall
  have hbound : C * |s-t|^2 ≤ ε * |s-t| := by nlinarith [abs_nonneg (s-t)]
  simp only [BoundedContinuousFunction.sub_apply,BoundedContinuousFunction.smul_apply,
    actionBCF_apply,smul_eq_mul,Real.norm_eq_abs]
  convert hh.trans hbound using 1 <;> rfl

theorem actionBCF_hasDerivAt {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt (actionBCF hv' hb' hl' hT hbs hB μ hu f hf hBf)
      (actionBCF hv' hb' hl' hT hbs hB μ hu (fun p => euclideanGenerator b (f p))
        (joint_euclideanGenerator hf hbs)
        (uniform_euclideanGenerator hbs hB (fun _p => hf.comp (contDiff_const.prodMk contDiff_id)) hBf) t) t :=
  (actionBCF_hasDerivWithinAt hv hb hl hv' hb' hl' hT hbs hB μ hu f hf hBf
    ⟨ht.1.le,ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
end Parameter

/-- Same source kernel, parametrized by the actual Euclidean spatial point. -/
def pointKernelTest {n : ℕ} (κ : ℝ) (x y : Point n) : ℝ :=
  euclideanKernelTest κ (coordinateEquiv n x) y

theorem pointKernelTest_joint_smooth {n : ℕ} (κ : ℝ) :
    ContDiff ℝ ∞ (Function.uncurry (pointKernelTest (n := n) κ)) := by
  change ContDiff ℝ ∞ (fun q : Point n × Point n =>
    PeriodicPositiveKernel.kernel κ (coordinateEquiv n q.1 - coordinateEquiv n q.2))
  exact (PeriodicPositiveKernel.kernel_smooth n κ).comp
    (((coordinateEquiv n).contDiff.comp contDiff_fst).sub
      ((coordinateEquiv n).contDiff.comp contDiff_snd))

theorem pointKernelTest_uniform {n : ℕ} (κ : ℝ) :
    UniformDerivatives (pointKernelTest (n := n) κ) := by
  intro m
  obtain ⟨C,hC,hb⟩ := euclideanKernelTest_uniform (n := n) κ m
  exact ⟨C,hC,fun x y => hb (coordinateEquiv n x) y⟩

/-- The actual scalar convolved source in the same BCF space as the density. -/
def convolvedSourceBCF (κ t : ℝ) : Point (N*d) →ᵇ ℝ :=
  actionBCF hv' hb' hl' hT hbs hB μ hu (pointKernelTest κ)
    (pointKernelTest_joint_smooth κ) (pointKernelTest_uniform κ) t

/-- Its actual differentiated generator action, with proved global bounds. -/
def convolvedSourceDerivativeBCF (κ t : ℝ) : Point (N*d) →ᵇ ℝ :=
  actionBCF hv' hb' hl' hT hbs hB μ hu (fun x => euclideanGenerator b (pointKernelTest κ x))
    (joint_euclideanGenerator (pointKernelTest_joint_smooth κ) hbs)
    (uniform_euclideanGenerator hbs hB
      (fun x => euclideanKernelTest_smooth κ (coordinateEquiv (N*d) x))
      (pointKernelTest_uniform κ)) t

@[simp] theorem convolvedSourceBCF_apply (κ t : ℝ) (x : Point (N*d)) :
    convolvedSourceBCF hv' hb' hl' hT hbs hB μ hu κ t x =
      convolvedSource hv' hb' hl' hT μ (u := u) κ t (coordinateEquiv (N*d) x) := rfl

include hv hb hl in
/-- Genuine BCF time differentiation of the smoothed source, including endpoints. -/
theorem convolvedSourceBCF_hasDerivWithinAt (κ : ℝ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (convolvedSourceBCF hv' hb' hl' hT hbs hB μ hu κ)
      (convolvedSourceDerivativeBCF hv' hb' hl' hT hbs hB μ hu κ t) (Icc 0 T) t :=
  actionBCF_hasDerivWithinAt hv hb hl hv' hb' hl' hT hbs hB μ hu (pointKernelTest κ)
    (pointKernelTest_joint_smooth κ) (pointKernelTest_uniform κ) ht

include hv hb hl in
theorem convolvedSourceBCF_hasDerivAt (κ : ℝ) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt (convolvedSourceBCF hv' hb' hl' hT hbs hB μ hu κ)
      (convolvedSourceDerivativeBCF hv' hb' hl' hT hbs hB μ hu κ t) t :=
  actionBCF_hasDerivAt hv hb hl hv' hb' hl' hT hbs hB μ hu (pointKernelTest κ)
    (pointKernelTest_joint_smooth κ) (pointKernelTest_uniform κ) ht

end SharpWasserstein.PeriodicSourceConvolution
