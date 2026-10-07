module

public import SharpWasserstein.Compat
public import SharpWasserstein.RoughEulerianCompressionEquation
public import SharpWasserstein.RoughEulerianTimeActionMoments

@[expose] public section

/-! A uniform bound on the original tangent objectives supplies every genuine
compressed joint-flux datum used by smoothing. No flux, action, measurability,
or compressed continuity equation is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff InnerProductSpace ProbabilityTheory ENNReal
namespace SharpWasserstein.RoughUniformAction
open WeightedTangent RoughEulerianTransport RoughEulerianCompression
variable {d : ℕ} [MeasurableSpace (Point d)] [BorelSpace (Point d)]
  {μ : ℝ → ProbabilityMeasure (Point d)} {σ : ℝ → Test d →ₗ[ℝ] ℝ} {T : ℝ}
  (h : CompactDistributionContinuity μ σ T)

def compressedJoint (R : ℝ) : Measure (ℝ × Point d) :=
  (volume.restrict (Icc 0 T)) ⊗ₘ probabilityCurveKernel (compressedCurve R μ)
    (compressedCurve_continuous R h.continuous)

def compressedField {R : ℝ} (hR : R ≠ 0) : ℝ × Point d → Point d :=
  compressedFlux (curveSpaceTimeMeasure h) hR (curveFlux h)

theorem compressedJoint_eq (R : ℝ) : compressedJoint h R =
    (curveSpaceTimeMeasure h).map (compressionMap R) := (compressedCurve_jointMeasure h R).symm

theorem compressedField_integrable {R : ℝ} (hR : R ≠ 0) :
    Integrable (compressedField h hR) (compressedJoint h R) := by
  rw [compressedJoint_eq]
  exact (Lp.memLp (compressedFlux (curveSpaceTimeMeasure h) hR (curveFlux h))).integrable
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)

theorem compressedField_sq_integrable {R : ℝ} (hR : R ≠ 0) :
    Integrable (fun z => ‖compressedField h hR z‖^2) (compressedJoint h R) := by
  rw [compressedJoint_eq]
  exact (memLp_two_iff_integrable_sq_norm
    (Lp.memLp (compressedFlux (curveSpaceTimeMeasure h) hR (curveFlux h))).aestronglyMeasurable).mp
    (Lp.memLp (compressedFlux (curveSpaceTimeMeasure h) hR (curveFlux h)))

theorem compressedJoint_support (R : ℝ) :
    ∀ᵐ z ∂compressedJoint h R,‖z.2‖ ≤ Real.sqrt (d : ℝ)*|R| := by
  rw [compressedJoint_eq]
  have hh := compressedMeasure_outside_ball (curveSpaceTimeMeasure h) R
  apply ae_iff.mpr
  convert hh using 2
  ext z
  simp

/-- A constant objective bound has exactly the integral `T*E`. -/
theorem integral_constant_horizon (hT : 0 ≤ T) (E : ℝ) :
    (∫ _t in Icc 0 T,E) = T*E := by
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hT,
    intervalIntegral.integral_const,sub_zero,smul_eq_mul]

include h in
/-- Uniform source objectives control the action of the constructed field. -/
theorem compressedField_action_le (hT : 0 ≤ T) {E : ℝ}
    (hbound : ∀ t ∈ Icc 0 T,∀ φ : Test d,testObjective (μ t : Measure (Point d)) (σ t) φ ≤ E)
    {R : ℝ} (hR : R ≠ 0) :
    (∫ z,‖compressedField h hR z‖^2 ∂compressedJoint h R) ≤ T*E := by
  have hb : ∀ᵐ t ∂volume.restrict (Icc 0 T),∀ φ : Test d,
      testObjective (μ t : Measure (Point d)) (σ t) φ ≤ E := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hbound t ht
  rw [compressedJoint_eq]
  exact (compressed_curve_action_le h (integrable_const E) hb hR).trans_eq
    (integral_constant_horizon hT E)

/-- Restriction to any joint measurable window cannot increase the action. -/
theorem compressedField_restricted_action_le (hT : 0 ≤ T) {E : ℝ}
    (hbound : ∀ t ∈ Icc 0 T,∀ φ : Test d,testObjective (μ t : Measure (Point d)) (σ t) φ ≤ E)
    {R : ℝ} (hR : R ≠ 0) (A : Set (ℝ × Point d)) :
    (∫ z in A,‖compressedField h hR z‖^2 ∂compressedJoint h R) ≤ T*E :=
  (integral_mono_measure Measure.restrict_le_self (Eventually.of_forall fun _ => sq_nonneg _)
    (compressedField_sq_integrable h hR)).trans (compressedField_action_le h hT hbound hR)

/-- The actual compressed curve and constructed field satisfy the original
integrated flux equation needed by time-space smoothing. -/
theorem compressedField_equation (hT : 0 ≤ T) {E : ℝ}
    (hbound : ∀ t ∈ Icc 0 T,∀ φ : Test d,testObjective (μ t : Measure (Point d)) (σ t) φ ≤ E)
    {R : ℝ} (hR : R ≠ 0) (φ : Test d) {r : ℝ} (hr : r ∈ Icc 0 T) :
    (∫ x,(φ : Point d → ℝ) x ∂(compressedCurve R μ r : Measure (Point d)))-
      (∫ x,(φ : Point d → ℝ) x ∂(compressedCurve R μ 0 : Measure (Point d))) =
      ∫ t in 0..r,∫ x,⟪gradient (φ : Point d → ℝ) x,compressedField h hR (t,x)⟫_ℝ
        ∂(compressedCurve R μ t : Measure (Point d)) := by
  have hb : ∀ᵐ t ∂volume.restrict (Icc 0 T),∀ φ : Test d,
      testObjective (μ t : Measure (Point d)) (σ t) φ ≤ E := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hbound t ht
  exact (compressed_curve_continuity_equation h hT (integrable_const E) hb hR φ
    ⟨le_rfl,hT⟩ hr hr.1).2

end SharpWasserstein.RoughUniformAction
