module

public import SharpWasserstein.Compat
public import SharpWasserstein.RoughCommonLabelTimeEndpoint
public import SharpWasserstein.RoughEulerianTimeActionCurveEnergy
public import SharpWasserstein.RoughEulerianTransportLimit

@[expose] public section

/-! Explicit positive vanishing regularization scales and actual quadratic
endpoint laws used when removing time-space smoothing and then compression. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff
namespace SharpWasserstein.RoughEulerianTransport
open WeightedTangent RoughEulerianTime RoughEulerianSmoothing RoughEulerianCompression

def actionUnitScale (n : ℕ) : ℝ := 1 / ((n : ℝ)+1)

theorem actionUnitScale_pos (n : ℕ) : 0 < actionUnitScale n := by unfold actionUnitScale; positivity

theorem actionUnitScale_le_one (n : ℕ) : actionUnitScale n ≤ 1 := by
  unfold actionUnitScale
  apply (div_le_one (by positivity)).mpr
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

theorem actionUnitScale_tendsto : Tendsto actionUnitScale atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

def actionTimeScale (T : ℝ) (n : ℕ) : ℝ := (T/8)*actionUnitScale n

theorem actionTimeScale_pos {T : ℝ} (hT : 0 < T) (n : ℕ) : 0 < actionTimeScale T n :=
  mul_pos (div_pos hT (by norm_num)) (actionUnitScale_pos n)

theorem actionTimeScale_le {T : ℝ} (hT : 0 ≤ T) (n : ℕ) : actionTimeScale T n ≤ T/8 := by
  unfold actionTimeScale
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (actionUnitScale_le_one n) (div_nonneg hT (by norm_num : (0:ℝ)≤8))

theorem actionTimeScale_tendsto (T : ℝ) : Tendsto (actionTimeScale T) atTop (𝓝 0) := by
  have hh := actionUnitScale_tendsto.const_mul (T/8)
  unfold actionTimeScale
  simpa only [mul_zero] using hh

theorem actionTimeScale_interior {T : ℝ} (hT : 0 < T) (n : ℕ) :
    2*actionTimeScale T n ≤ T-2*actionTimeScale T n ∧
    actionTimeScale T n < 2*actionTimeScale T n ∧
    (T-2*actionTimeScale T n)+actionTimeScale T n < T := by
  have hp := actionTimeScale_pos hT n
  have hb := actionTimeScale_le hT.le n
  constructor
  · linarith
  constructor <;> linarith

variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]

/-- Actual finite-second-moment probability law in configuration coordinates. -/
def euclideanQuadraticLaw (μ : Measure (Point (N*d))) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x => ‖x‖^2) μ) : QuadraticProbabilityLaw d N :=
  ⟨μ.map (configurationEuclidean d N).symm,
    Measure.isProbabilityMeasure_map (configurationEuclidean d N).symm.continuous.measurable.aemeasurable,
    hasSecondMoment_configuration_of_quadratic μ hμ⟩

/-- Bounded spatial compression genuinely supplies a second moment, even if
the original law is only a probability. -/
theorem compressedMeasure_quadratic (R : ℝ) (μ : Measure (Point (N*d))) [IsProbabilityMeasure μ] :
    Integrable (fun x : Point (N*d) => ‖x‖^2) (μ.map (compression R)) := by
  apply (integrable_map_measure (continuous_norm.pow 2).aestronglyMeasurable
    (compression_contDiff R).continuous.measurable.aemeasurable).mpr
  apply Integrable.of_bound (((compression_contDiff R).continuous.norm.pow 2).aestronglyMeasurable)
    ((Real.sqrt ((N*d : ℕ) : ℝ)*|R|)^2)
  exact Eventually.of_forall fun x => by
    change ‖‖compression R x‖^2‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (compression_range_bound R x) 2

/-- Coordinate conversion commutes with the actual spatial compression. -/
theorem compressedMeasure_configuration (R : ℝ) (μ : Measure (Point (N*d))) :
    (μ.map (compression R)).map (configurationEuclidean d N).symm =
      (μ.map (configurationEuclidean d N).symm).map (configurationCompression R) := by
  rw [Measure.map_map (configurationEuclidean d N).symm.continuous.measurable
    (compression_contDiff R).continuous.measurable,
    Measure.map_map (configurationCompression_continuous R).measurable
      (configurationEuclidean d N).symm.continuous.measurable]
  congr 1
  funext x
  simp only [Function.comp_def,configurationCompression,ContinuousLinearEquiv.apply_symm_apply]

/-- Actual squared-Wasserstein endpoint convergence of compression. -/
theorem compressedMeasure_wassersteinSq_tendsto (μ : Measure (Point (N*d))) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x => ‖x‖^2) μ) :
    Tendsto (fun n : ℕ => wassersteinSq
      ((μ.map (compression ((n:ℝ)+1))).map (configurationEuclidean d N).symm)
      (μ.map (configurationEuclidean d N).symm)) atTop (𝓝 0) := by
  letI : IsProbabilityMeasure (μ.map (configurationEuclidean d N).symm) :=
    Measure.isProbabilityMeasure_map (configurationEuclidean d N).symm.continuous.measurable.aemeasurable
  simp_rw [compressedMeasure_configuration]
  exact configurationCompression_wassersteinSq_tendsto _ (hasSecondMoment_configuration_of_quadratic μ hμ)


/-- The actual interior regularized endpoint as a genuine quadratic
probability law. Normalization and moment finiteness are derived. -/
def spaceTimeQuadraticLaw {τ ε δ R T t : ℝ} (hτ : 0 < τ) (hε : 0 < ε)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (κ : ProbabilityTheory.Kernel ℝ (Point (N*d))) [ProbabilityTheory.IsMarkovKernel κ]
    (hρ : ∀ᵐ z ∂((volume.restrict (Icc 0 T)).compProd κ),‖z.2‖ ≤ R)
    (ha : τ ≤ t) (hb : t+τ ≤ T) : QuadraticProbabilityLaw d N := by
  letI := spaceTimeRegularizedLaw_probability (a := 0) (b := T) hτ hε hδ hδ₁ κ
    (by simpa only [zero_add] using ha) hb
  exact euclideanQuadraticLaw _
    (spaceTimeRegularizedLaw_quadratic (a := 0) (b := T) hτ hε hδ hδ₁ κ hρ
      (by simpa only [zero_add] using ha) hb).1

end SharpWasserstein.RoughEulerianTransport
