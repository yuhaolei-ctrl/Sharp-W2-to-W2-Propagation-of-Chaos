import SharpWasserstein.RoughEulerianTimeKernel
import SharpWasserstein.RoughEulerianSmoothingLaw

/-! Actual joint space-time convolution of the original finite carrying
measure and integrable flux. A compact product kernel and a stationary
Gaussian floor give a jointly smooth compact velocity, before any timewise
choice of vector fields is made. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff NNReal
namespace SharpWasserstein.RoughEulerianSmoothing
open WeightedTangent WeightedConvolution NoiseAverage RoughEulerianTime
variable {d : ℕ} [MeasurableSpace (Point d)] [BorelSpace (Point d)]

def spaceTimeKernel (τ : ℝ) (hτ : 0 < τ) (ε : ℝ) (hε : 0 < ε) (p : ℝ × Point d) : ℝ :=
  timeKernel τ hτ p.1 * mollifier ε hε p.2

theorem spaceTimeKernel_nonneg {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε) (p : ℝ × Point d) :
    0 ≤ spaceTimeKernel τ hτ ε hε p :=
  mul_nonneg (timeKernel_nonneg hτ p.1) (mollifier_nonneg hε p.2)

theorem spaceTimeKernel_smooth {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε) :
    ContDiff ℝ ∞ (spaceTimeKernel (d := d) τ hτ ε hε) :=
  ((timeKernel_smooth hτ).comp contDiff_fst).mul ((mollifier_smooth hε).comp contDiff_snd)

theorem spaceTimeKernel_eq_zero {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε)
    {p : ℝ × Point d} (hp : max τ ε ≤ ‖p‖) : spaceTimeKernel τ hτ ε hε p = 0 := by
  have hp' : max τ ε ≤ max ‖p.1‖ ‖p.2‖ := hp
  rcases le_max_iff.mp hp' with ht | hx
  · rw [spaceTimeKernel, timeKernel_eq_zero hτ
      (by simpa only [Real.norm_eq_abs] using (le_max_left τ ε).trans ht), zero_mul]
  · rw [spaceTimeKernel, mollifier_eq_zero hε ((le_max_right τ ε).trans hx), mul_zero]

theorem spaceTimeKernel_compact {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε) :
    HasCompactSupport (spaceTimeKernel (d := d) τ hτ ε hε) := by
  apply HasCompactSupport.intro' (isCompact_closedBall (0 : ℝ × Point d) (max τ ε))
    Metric.isClosed_closedBall
  intro p hp
  exact spaceTimeKernel_eq_zero hτ hε (le_of_lt (by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hp))

theorem spaceTimeKernel_allDerivativesBounded {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε) :
    AllDerivativesBounded (spaceTimeKernel (d := d) τ hτ ε hε) :=
  allDerivativesBounded_of_compact (spaceTimeKernel_smooth hτ hε) (spaceTimeKernel_compact hτ hε)

def spaceTimeDensity (τ : ℝ) (hτ : 0 < τ) (ε : ℝ) (hε : 0 < ε)
    (ρ : Measure (ℝ × Point d)) (p : ℝ × Point d) : ℝ :=
  ∫ z, spaceTimeKernel τ hτ ε hε (p-z) ∂ρ

def spaceTimeFlux (τ : ℝ) (hτ : 0 < τ) (ε : ℝ) (hε : 0 < ε)
    (ρ : Measure (ℝ × Point d)) (U : ℝ × Point d → Point d) (p : ℝ × Point d) : Point d :=
  ∫ z, spaceTimeKernel τ hτ ε hε (p-z) • U z ∂ρ

theorem spaceTimeDensity_nonneg {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε)
    (ρ : Measure (ℝ × Point d)) (p : ℝ × Point d) : 0 ≤ spaceTimeDensity τ hτ ε hε ρ p :=
  integral_nonneg (fun z => spaceTimeKernel_nonneg hτ hε (p-z))

theorem spaceTimeDensity_smooth {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε)
    (ρ : Measure (ℝ × Point d)) [IsFiniteMeasure ρ] :
    ContDiff ℝ ∞ (spaceTimeDensity τ hτ ε hε ρ) := by
  have hh := contDiff_infty_operatorAverage ρ (fun z : ℝ × Point d => -z)
    continuous_neg.stronglyMeasurable (integrable_const (ContinuousLinearMap.toSpanSingleton ℝ (1 : ℝ)))
    (spaceTimeKernel_smooth hτ hε) (spaceTimeKernel_allDerivativesBounded hτ hε)
  convert hh using 1
  funext p
  simp only [spaceTimeDensity, operatorAverage, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul,
    mul_one, sub_eq_add_neg]

theorem spaceTimeFlux_smooth {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε)
    (ρ : Measure (ℝ × Point d)) {U : ℝ × Point d → Point d} (hU : Integrable U ρ) :
    ContDiff ℝ ∞ (spaceTimeFlux τ hτ ε hε ρ U) := by
  have hW : Integrable (fun z => ContinuousLinearMap.toSpanSingleton ℝ (U z)) ρ :=
    (ContinuousLinearMap.toSpanSingletonLIE ℝ (Point d)).integrable_comp_iff.mpr hU
  have hh := contDiff_infty_operatorAverage ρ (fun z : ℝ × Point d => -z)
    continuous_neg.stronglyMeasurable hW (spaceTimeKernel_smooth hτ hε)
    (spaceTimeKernel_allDerivativesBounded hτ hε)
  convert hh using 1
  funext p
  simp only [spaceTimeFlux, operatorAverage, ContinuousLinearMap.toSpanSingleton_apply, sub_eq_add_neg]

theorem spaceTimeFlux_compact {τ ε R : ℝ} (hτ : 0 < τ) (hε : 0 < ε)
    (ρ : Measure (ℝ × Point d)) (hρ : ∀ᵐ z ∂ρ, ‖z‖ ≤ R) (U : ℝ × Point d → Point d) :
    HasCompactSupport (spaceTimeFlux τ hτ ε hε ρ U) := by
  apply HasCompactSupport.intro' (isCompact_closedBall (0 : ℝ × Point d) (R+max τ ε))
    Metric.isClosed_closedBall
  intro p hp
  have hp' : R+max τ ε < ‖p‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hp
  apply integral_eq_zero_of_ae
  filter_upwards [hρ] with z hz
  have hd : max τ ε ≤ ‖p-z‖ := by
    have hh := norm_le_norm_sub_add p z
    linarith
  simp only [spaceTimeKernel_eq_zero hτ hε hd, zero_smul, Pi.zero_apply]

/-- The actual product-convolved flux with a positive stationary Gaussian
floor defines a globally jointly smooth compact velocity. -/
theorem spaceTimeFloorVelocity_smooth {τ ε δ : ℝ} (hτ : 0 < τ) (hε : 0 < ε)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (ρ : Measure (ℝ × Point d)) [IsFiniteMeasure ρ]
    {U : ℝ × Point d → Point d} (hU : Integrable U ρ) :
    ContDiff ℝ ∞ (floorVelocity (1-δ) (spaceTimeDensity τ hτ ε hε ρ)
      (fun p => δ*gaussianFloor p.2) (spaceTimeFlux τ hτ ε hε ρ U)) :=
  floorVelocity_smooth (sub_nonneg.mpr hδ₁) (spaceTimeDensity_nonneg hτ hε ρ)
    (fun p => mul_pos hδ (gaussianFloor_pos p.2)) (spaceTimeDensity_smooth hτ hε ρ)
    (contDiff_const.mul (gaussianFloor_smooth.comp contDiff_snd)) (spaceTimeFlux_smooth hτ hε ρ hU)

theorem spaceTimeFloorVelocity_regular {τ ε δ R : ℝ} (hτ : 0 < τ) (hε : 0 < ε)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (ρ : Measure (ℝ × Point d)) [IsFiniteMeasure ρ]
    (hρ : ∀ᵐ z ∂ρ, ‖z‖ ≤ R) {U : ℝ × Point d → Point d} (hU : Integrable U ρ) :
    AllDerivativesBounded (floorVelocity (1-δ) (spaceTimeDensity τ hτ ε hε ρ)
      (fun p => δ*gaussianFloor p.2) (spaceTimeFlux τ hτ ε hε ρ U)) ∧
      (∃ K : ℝ≥0, LipschitzWith K (floorVelocity (1-δ) (spaceTimeDensity τ hτ ε hε ρ)
        (fun p => δ*gaussianFloor p.2) (spaceTimeFlux τ hτ ε hε ρ U))) ∧
      (∃ K₁ : ℝ≥0, LipschitzWith K₁ (fderiv ℝ (floorVelocity (1-δ) (spaceTimeDensity τ hτ ε hε ρ)
        (fun p => δ*gaussianFloor p.2) (spaceTimeFlux τ hτ ε hε ρ U)))) :=
  floorVelocity_regular (sub_nonneg.mpr hδ₁) (spaceTimeDensity_nonneg hτ hε ρ)
    (fun p => mul_pos hδ (gaussianFloor_pos p.2)) (spaceTimeDensity_smooth hτ hε ρ)
    (contDiff_const.mul (gaussianFloor_smooth.comp contDiff_snd)) (spaceTimeFlux_smooth hτ hε ρ hU)
    (spaceTimeFlux_compact hτ hε ρ hρ U)

end SharpWasserstein.RoughEulerianSmoothing
