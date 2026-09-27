import SharpWasserstein.RoughUniformActionData
import SharpWasserstein.RoughEulerianRegularizedTransport

/-! A single uniform objective bound for the original source yields the
actual smoothed compressed endpoint cost bound `T² E`, independent of every
regularization parameter. The remaining passage removes regularization. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff InnerProductSpace ProbabilityTheory
namespace SharpWasserstein.RoughUniformAction
open WeightedTangent RoughEulerianTransport RoughEulerianCompression RoughEulerianSmoothing
variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]

instance compressedJoint_finite {μ : ℝ → ProbabilityMeasure (Point (N*d))}
    {σ : ℝ → Test (N*d) →ₗ[ℝ] ℝ} {T : ℝ}
    (h : CompactDistributionContinuity μ σ T) (R : ℝ) : IsFiniteMeasure (compressedJoint h R) := by
  unfold compressedJoint
  infer_instance

theorem compressed_regularized_wassersteinSq_le
    {μ : ℝ → ProbabilityMeasure (Point (N*d))} {σ : ℝ → Test (N*d) →ₗ[ℝ] ℝ}
    {T E : ℝ} (hT : 0 ≤ T) (hE : 0 ≤ E) (h : CompactDistributionContinuity μ σ T)
    (hbound : ∀ t ∈ Icc 0 T,∀ φ : Test (N*d),testObjective (μ t : Measure (Point (N*d))) (σ t) φ ≤ E)
    {R τ ε δ a b : ℝ} (hR : R ≠ 0) (hτ : 0 < τ) (hε : 0 < ε)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hab : a ≤ b) (ha : τ < a) (hb : b+τ < T) :
    wassersteinSq
      ((spaceTimeRegularizedLaw τ hτ ε hε δ (compressedJoint h R) a).map (configurationEuclidean d N).symm)
      ((spaceTimeRegularizedLaw τ hτ ε hε δ (compressedJoint h R) b).map (configurationEuclidean d N).symm) ≤
      ENNReal.ofReal (T^2*E) := by
  have hc := spaceTimeRegularizedLaw_wassersteinSq_le hτ hε hδ hδ₁
    (compressedCurve_continuous R h.continuous) (compressedField_integrable h hR)
    (compressedField_sq_integrable h hR) (compressedJoint_support h R)
    (fun φ _ hr => compressedField_equation h hT hbound hR φ hr) hab ha hb
  apply hc.trans
  apply ENNReal.ofReal_le_ofReal
  have hlen : 0 ≤ b-a := sub_nonneg.mpr hab
  have hlenT : b-a ≤ T := by linarith
  have hact := compressedField_action_le h hT hbound hR
  calc
    (b-a)*((1-δ)*(∫ z,‖compressedField h hR z‖^2 ∂compressedJoint h R)) ≤
        (b-a)*((1-δ)*(T*E)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hact (sub_nonneg.mpr hδ₁)) hlen
    _ ≤ (b-a)*(T*E) := by
      apply mul_le_mul_of_nonneg_left _ hlen
      exact mul_le_of_le_one_left (mul_nonneg hT hE) (by linarith)
    _ ≤ T^2*E := by
      nlinarith [mul_le_mul_of_nonneg_right hlenT (mul_nonneg hT hE)]

end SharpWasserstein.RoughUniformAction
