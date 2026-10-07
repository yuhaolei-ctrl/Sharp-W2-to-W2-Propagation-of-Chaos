module

public import SharpWasserstein.Compat
public import SharpWasserstein.RoughFiniteActionEndpoint
public import SharpWasserstein.RoughUniformRegularizedTransport
public import SharpWasserstein.RoughFiniteActionInterface

@[expose] public section

/-! The uniform finite-action transport theorem is proved by actual
compression, joint smoothing, the classical smooth-flow estimate, and two
actual Wasserstein endpoint limits. All source fields and regularized curves
are constructed in the preceding modules. -/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal ContDiff ProbabilityTheory
namespace SharpWasserstein.RoughEulerianTransport
open WeightedTangent RoughEulerianTime RoughEulerianSmoothing RoughEulerianCompression RoughUniformAction
variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]

/-- Removing time-space smoothing leaves the true transport bound on the
actual compressed curve. The common labels are used only for the proved
endpoint convergence and do not contain a finite-action estimate. -/
theorem compressed_wassersteinSq_le_uniform_action
    {μ : ℝ → ProbabilityMeasure (Point (N*d))} {σ : ℝ → Test (N*d) →ₗ[ℝ] ℝ}
    {T E : ℝ} (hT : 0 < T) (hE : 0 ≤ E) (h : CompactDistributionContinuity μ σ T)
    (hlabel : CommonLabelLift d N μ)
    (hbound : ∀ t ∈ Icc 0 T,∀ φ : Test (N*d),testObjective (μ t : Measure (Point (N*d))) (σ t) φ ≤ E)
    {R : ℝ} (hR : R ≠ 0) :
    wassersteinSq ((compressedCurve R μ 0 : Measure (Point (N*d))).map (configurationEuclidean d N).symm)
      ((compressedCurve R μ T : Measure (Point (N*d))).map (configurationEuclidean d N).symm) ≤
      ENNReal.ofReal (T^2*E) := by
  let μR := compressedCurve R μ
  have hμR : Continuous μR := compressedCurve_continuous R h.continuous
  let κ := probabilityCurveKernel μR hμR
  have hs : ∀ᵐ z ∂((volume.restrict (Icc 0 T)) ⊗ₘ κ),‖z.2‖ ≤ Real.sqrt ((N*d : ℕ):ℝ)*|R| :=
    compressedJoint_support h R
  have hleft (n : ℕ) : actionTimeScale T n ≤ 2*actionTimeScale T n ∧
      2*actionTimeScale T n+actionTimeScale T n ≤ T := by
    have hp := actionTimeScale_pos hT n
    have hb := actionTimeScale_le hT.le n
    constructor <;> linarith
  have hright (n : ℕ) : actionTimeScale T n ≤ T-2*actionTimeScale T n ∧
      (T-2*actionTimeScale T n)+actionTimeScale T n ≤ T := by
    have hp := actionTimeScale_pos hT n
    have hb := actionTimeScale_le hT.le n
    constructor <;> linarith
  let A (n : ℕ) : QuadraticProbabilityLaw d N := spaceTimeQuadraticLaw (actionTimeScale_pos hT n)
    (actionUnitScale_pos n) (actionUnitScale_pos n) (actionUnitScale_le_one n) κ hs (hleft n).1 (hleft n).2
  let B (n : ℕ) : QuadraticProbabilityLaw d N := spaceTimeQuadraticLaw (actionTimeScale_pos hT n)
    (actionUnitScale_pos n) (actionUnitScale_pos n) (actionUnitScale_le_one n) κ hs (hright n).1 (hright n).2
  let A₀ : QuadraticProbabilityLaw d N := euclideanQuadraticLaw (d := d) (N := N) (μR 0 : Measure (Point (N*d)))
    (compressedMeasure_quadratic (d := d) (N := N) R (μ 0 : Measure (Point (N*d))))
  let B₀ : QuadraticProbabilityLaw d N := euclideanQuadraticLaw (d := d) (N := N) (μR T : Measure (Point (N*d)))
    (compressedMeasure_quadratic (d := d) (N := N) R (μ T : Measure (Point (N*d))))
  have htleft : Tendsto (fun n => 2*actionTimeScale T n) atTop (𝓝 0) := by
    simpa only [mul_zero] using (actionTimeScale_tendsto T).const_mul 2
  have htright : Tendsto (fun n => T-2*actionTimeScale T n) atTop (𝓝 T) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub htleft
  have hA : Tendsto (fun n => wassersteinSq (A n).measure A₀.measure) atTop (𝓝 0) := by
    exact (hlabel.compress hR).spaceTimeRegularizedLaw_wassersteinSq_tendsto hμR
      (actionTimeScale_pos hT) actionUnitScale_pos (fun n => (actionUnitScale_pos n).le) actionUnitScale_le_one
      (a := 0) (b := T) (fun n => by simpa only [zero_add] using (hleft n).1)
      (fun n => (hleft n).2) (actionTimeScale_tendsto T) actionUnitScale_tendsto
      actionUnitScale_tendsto htleft hs
  have hB : Tendsto (fun n => wassersteinSq (B n).measure B₀.measure) atTop (𝓝 0) := by
    exact (hlabel.compress hR).spaceTimeRegularizedLaw_wassersteinSq_tendsto hμR
      (actionTimeScale_pos hT) actionUnitScale_pos (fun n => (actionUnitScale_pos n).le) actionUnitScale_le_one
      (a := 0) (b := T) (fun n => by simpa only [zero_add] using (hright n).1)
      (fun n => (hright n).2) (actionTimeScale_tendsto T) actionUnitScale_tendsto
      actionUnitScale_tendsto htright hs
  apply wassersteinSq_le_of_regularized_endpoints hA hB
  exact Eventually.of_forall fun n => compressed_regularized_wassersteinSq_le hT.le hE h hbound hR
    (actionTimeScale_pos hT n) (actionUnitScale_pos n) (actionUnitScale_pos n) (actionUnitScale_le_one n)
    (actionTimeScale_interior hT n).1 (actionTimeScale_interior hT n).2.1
    (actionTimeScale_interior hT n).2.2

/-- Removing the smooth compressions proves the actual rough finite-action
bound. Only endpoint second moments are required at this final stage. -/
theorem wassersteinSq_le_uniform_action
    {μ : ℝ → ProbabilityMeasure (Point (N*d))} {σ : ℝ → Test (N*d) →ₗ[ℝ] ℝ}
    {T E : ℝ} (hT : 0 ≤ T) (hE : 0 ≤ E) (h : CompactDistributionContinuity μ σ T)
    (hlabel : CommonLabelLift d N μ)
    (hP₀ : Integrable (fun x : Point (N*d) => ‖x‖^2) (μ 0 : Measure (Point (N*d))))
    (hPT : Integrable (fun x : Point (N*d) => ‖x‖^2) (μ T : Measure (Point (N*d))))
    (hbound : ∀ t ∈ Icc 0 T,∀ φ : Test (N*d),testObjective (μ t : Measure (Point (N*d))) (σ t) φ ≤ E) :
    wassersteinSq ((μ 0 : Measure (Point (N*d))).map (configurationEuclidean d N).symm)
      ((μ T : Measure (Point (N*d))).map (configurationEuclidean d N).symm) ≤ ENNReal.ofReal (T^2*E) := by
  rcases hT.eq_or_lt with hzero | hpos
  · subst T
    letI : IsProbabilityMeasure ((μ 0 : Measure (Point (N*d))).map (configurationEuclidean d N).symm) :=
      Measure.isProbabilityMeasure_map (configurationEuclidean d N).symm.continuous.measurable.aemeasurable
    rw [wassersteinSq_self,zero_pow (by decide : 2 ≠ 0),zero_mul,ENNReal.ofReal_zero]
  have hPc (R t : ℝ) : Integrable (fun x : Point (N*d) => ‖x‖^2)
      (compressedCurve R μ t : Measure (Point (N*d))) := by
    change Integrable (fun x : Point (N*d) => ‖x‖^2) ((μ t : Measure (Point (N*d))).map (compression R))
    exact compressedMeasure_quadratic (d := d) (N := N) R (μ t : Measure (Point (N*d)))
  let A (n : ℕ) : QuadraticProbabilityLaw d N := euclideanQuadraticLaw (d := d) (N := N)
    (compressedCurve ((n:ℝ)+1) μ 0 : Measure (Point (N*d))) (hPc ((n:ℝ)+1) 0)
  let B (n : ℕ) : QuadraticProbabilityLaw d N := euclideanQuadraticLaw (d := d) (N := N)
    (compressedCurve ((n:ℝ)+1) μ T : Measure (Point (N*d))) (hPc ((n:ℝ)+1) T)
  let A₀ : QuadraticProbabilityLaw d N := euclideanQuadraticLaw (d := d) (N := N) (μ 0 : Measure (Point (N*d))) hP₀
  let B₀ : QuadraticProbabilityLaw d N := euclideanQuadraticLaw (d := d) (N := N) (μ T : Measure (Point (N*d))) hPT
  have hA : Tendsto (fun n => wassersteinSq (A n).measure A₀.measure) atTop (𝓝 0) :=
    compressedMeasure_wassersteinSq_tendsto (d := d) (N := N) (μ 0 : Measure (Point (N*d))) hP₀
  have hB : Tendsto (fun n => wassersteinSq (B n).measure B₀.measure) atTop (𝓝 0) :=
    compressedMeasure_wassersteinSq_tendsto (d := d) (N := N) (μ T : Measure (Point (N*d))) hPT
  apply wassersteinSq_le_of_regularized_endpoints hA hB
  exact Eventually.of_forall fun n => compressed_wassersteinSq_le_uniform_action hpos hE h hlabel hbound
    (R := (n:ℝ)+1) (by positivity)

/-- The required finite-action interface now has an actual proof, obtained
from the original compact-test source bound and genuine law data. -/
theorem uniform_finite_action_transport : UniformFiniteActionTransport := by
  intro d N μ σ T E hT hE h hlabel hP hbound
  obtain ⟨hlabel⟩ := hlabel
  exact wassersteinSq_le_uniform_action hT hE h hlabel (hP 0 ⟨le_rfl,hT⟩) (hP T ⟨hT,le_rfl⟩) hbound

end SharpWasserstein.RoughEulerianTransport
