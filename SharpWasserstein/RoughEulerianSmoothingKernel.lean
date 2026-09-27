import SharpWasserstein.RoughEulerianSmoothingFloor
import SharpWasserstein.SmoothCutoff
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-! An actual nonnegative, normalized compact smooth Euclidean mollifier and
its density/flux convolutions. Bounded support of the original carrying law
gives compact support of the convolved flux, with an explicit radius. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff NNReal
namespace SharpWasserstein.RoughEulerianSmoothing
open WeightedTangent NoiseAverage WeightedConvolution
variable {d : ℕ} [MeasurableSpace (Point d)] [BorelSpace (Point d)]

def mollifierBump (ε : ℝ) (hε : 0 < ε) : ContDiffBump (0 : Point d) :=
  ⟨ε/2, ε, by positivity, by linarith⟩

def mollifier (ε : ℝ) (hε : 0 < ε) : Point d → ℝ :=
  (mollifierBump ε hε).normed volume

theorem mollifier_nonneg {ε : ℝ} (hε : 0 < ε) (x : Point d) : 0 ≤ mollifier ε hε x :=
  (mollifierBump ε hε).nonneg_normed x

theorem mollifier_smooth {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ ∞ (mollifier (d := d) ε hε) :=
  (mollifierBump ε hε).contDiff_normed

theorem mollifier_compact {ε : ℝ} (hε : 0 < ε) : HasCompactSupport (mollifier (d := d) ε hε) :=
  (mollifierBump ε hε).hasCompactSupport_normed

theorem mollifier_allDerivativesBounded {ε : ℝ} (hε : 0 < ε) :
    AllDerivativesBounded (mollifier (d := d) ε hε) :=
  allDerivativesBounded_of_compact (mollifier_smooth hε) (mollifier_compact hε)

theorem mollifier_integrable {ε : ℝ} (hε : 0 < ε) : Integrable (mollifier (d := d) ε hε) :=
  (mollifierBump ε hε).integrable_normed

theorem mollifier_integral {ε : ℝ} (hε : 0 < ε) : (∫ x : Point d, mollifier ε hε x) = 1 :=
  (mollifierBump ε hε).integral_normed

theorem mollifier_eq_zero {ε : ℝ} (hε : 0 < ε) {x : Point d} (hx : ε ≤ ‖x‖) :
    mollifier ε hε x = 0 := by
  unfold mollifier ContDiffBump.normed
  rw [(mollifierBump ε hε).zero_of_le_dist (by simpa [mollifierBump, dist_zero_right] using hx)]
  exact zero_div _

def density (ε : ℝ) (hε : 0 < ε) (μ : Measure (Point d)) (x : Point d) : ℝ :=
  ∫ y, mollifier ε hε (x-y) ∂μ

def flux (ε : ℝ) (hε : 0 < ε) (μ : Measure (Point d)) (v : Point d → Point d)
    (x : Point d) : Point d := ∫ y, mollifier ε hε (x-y) • v y ∂μ

theorem density_nonneg {ε : ℝ} (hε : 0 < ε) (μ : Measure (Point d)) (x : Point d) :
    0 ≤ density ε hε μ x := integral_nonneg (fun y => mollifier_nonneg hε (x-y))

theorem mollifier_translate_integrable {ε : ℝ} (hε : 0 < ε) (μ : Measure (Point d))
    [IsFiniteMeasure μ] (x : Point d) : Integrable (fun y => mollifier ε hε (x-y)) μ := by
  obtain ⟨C,_,hC⟩ := (mollifier_allDerivativesBounded (d := d) hε).bounded
  exact Integrable.of_bound ((mollifier_smooth hε).continuous.comp
    (continuous_const.sub continuous_id)).aestronglyMeasurable C (Eventually.of_forall fun y => hC _)

theorem mollifier_smul_integrable {ε : ℝ} (hε : 0 < ε) (μ : Measure (Point d))
    {v : Point d → Point d} (hv : Integrable v μ) (x : Point d) :
    Integrable (fun y => mollifier ε hε (x-y) • v y) μ := by
  obtain ⟨C,_,hC⟩ := (mollifier_allDerivativesBounded (d := d) hε).bounded
  exact hv.bdd_smul C ((mollifier_smooth hε).continuous.comp
    (continuous_const.sub continuous_id)).aestronglyMeasurable (Eventually.of_forall fun y => hC _)

theorem density_smooth {ε : ℝ} (hε : 0 < ε) (μ : Measure (Point d)) [IsProbabilityMeasure μ] :
    ContDiff ℝ ∞ (density ε hε μ) := by
  have hh := contDiff_infty_average μ (fun y : Point d => -y)
    continuous_neg.stronglyMeasurable (mollifier_smooth hε) (mollifier_allDerivativesBounded hε)
  convert hh using 1
  funext x
  simp only [density, average, sub_eq_add_neg]

theorem flux_smooth {ε : ℝ} (hε : 0 < ε) (μ : Measure (Point d))
    {v : Point d → Point d} (hv : Integrable v μ) : ContDiff ℝ ∞ (flux ε hε μ v) := by
  have hW : Integrable (fun y => ContinuousLinearMap.toSpanSingleton ℝ (v y)) μ :=
    (ContinuousLinearMap.toSpanSingletonLIE ℝ (Point d)).integrable_comp_iff.mpr hv
  have hh := contDiff_infty_operatorAverage μ (fun y : Point d => -y)
    continuous_neg.stronglyMeasurable hW (mollifier_smooth hε) (mollifier_allDerivativesBounded hε)
  convert hh using 1
  funext x
  simp only [flux, operatorAverage, ContinuousLinearMap.toSpanSingleton_apply, sub_eq_add_neg]

/-- The support bound is derived from the actual original law, and requires
neither boundedness nor continuity of the original vector field. -/
theorem flux_eq_zero_of_norm_gt {ε R : ℝ} (hε : 0 < ε) (μ : Measure (Point d))
    (hμ : ∀ᵐ y ∂μ, ‖y‖ ≤ R) (v : Point d → Point d) {x : Point d} (hx : R+ε < ‖x‖) :
    flux ε hε μ v x = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [hμ] with y hy
  have hdist : ε ≤ ‖x-y‖ := by
    have hh := norm_le_norm_sub_add x y
    linarith
  simp only [mollifier_eq_zero hε hdist, zero_smul, Pi.zero_apply]

theorem flux_compact {ε R : ℝ} (hε : 0 < ε) (μ : Measure (Point d))
    (hμ : ∀ᵐ y ∂μ, ‖y‖ ≤ R) (v : Point d → Point d) : HasCompactSupport (flux ε hε μ v) := by
  apply HasCompactSupport.intro' (isCompact_closedBall (0 : Point d) (R+ε))
    Metric.isClosed_closedBall
  intro x hx
  exact flux_eq_zero_of_norm_gt hε μ hμ v (by simpa only [Metric.mem_closedBall, dist_zero_right,
    not_le] using hx)

/-- The normalized compact convolution with a stationary positive smooth
floor yields a genuine compact smooth velocity with all bounded derivatives. -/
theorem convolved_floor_regular {ε R a : ℝ} (hε : 0 < ε) (ha : 0 ≤ a)
    (μ : Measure (Point d)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ y ∂μ, ‖y‖ ≤ R) {v : Point d → Point d} (hv : Integrable v μ)
    {g : Point d → ℝ} (hg : ∀ x, 0 < g x) (hgs : ContDiff ℝ ∞ g) :
    AllDerivativesBounded (floorVelocity a (density ε hε μ) g (flux ε hε μ v)) ∧
      (∃ K : ℝ≥0, LipschitzWith K (floorVelocity a (density ε hε μ) g (flux ε hε μ v))) ∧
      (∃ K₁ : ℝ≥0, LipschitzWith K₁
        (fderiv ℝ (floorVelocity a (density ε hε μ) g (flux ε hε μ v)))) :=
  floorVelocity_regular ha (density_nonneg hε μ) hg (density_smooth hε μ) hgs
    (flux_smooth hε μ hv) (flux_compact hε μ hμ v)

end SharpWasserstein.RoughEulerianSmoothing
