import SharpWasserstein.PointwiseTrajectory
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Bounded continuous actual velocity fields define continuous `L²` curves.
This verifies the mixed-integrability input of the pointwise transport theorem
from pointwise analytic data rather than assuming an `L²` derivative. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology InnerProductSpace ENNReal
namespace SharpWasserstein.EulerianTransport

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] {P : Measure Ω}

/-- The actual `L²` distance of two fields is their integrated squared Euclidean difference. -/
theorem norm_toLp_sub_sq {f g : Ω → E} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    ‖hf.toLp f - hg.toLp g‖ ^ 2 = ∫ ω, ‖f ω - g ω‖ ^ 2 ∂P := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (hf.toLp f) (hg.toLp g), hf.coeFn_toLp, hg.coeFn_toLp] with ω ha hb hc
  rw [ha]
  simp only [Pi.sub_apply, hb, hc, real_inner_self_eq_norm_sq]

/-- Uniformly bounded pointwise continuous fields yield an actual strongly
continuous `L²` curve, by dominated convergence of the true squared distance. -/
theorem continuous_toLp_of_uniform_bound [IsFiniteMeasure P]
    (F : ℝ → Ω → E) (h₂ : ∀ t, MemLp (F t) 2 P)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ t, ∀ᵐ ω ∂P, ‖F t ω‖ ≤ C)
    (hpath : ∀ᵐ ω ∂P, Continuous (fun t => F t ω)) :
    Continuous (fun t => (h₂ t).toLp (F t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hi : Continuous (fun s => ∫ ω, ‖F s ω - F t ω‖ ^ 2 ∂P) := by
    apply continuous_of_dominated (bound := fun _ => (2*C)^2)
    · intro s
      exact ((h₂ s).1.sub (h₂ t).1).norm.pow 2
    · intro s
      filter_upwards [hbound s, hbound t] with ω hs ht
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
      exact (norm_sub_le _ _).trans (by linarith)
    · exact integrable_const _
    · filter_upwards [hpath] with ω hω
      exact (hω.sub continuous_const).norm.pow 2
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have he (s : ℝ) : Real.sqrt (∫ ω, ‖F s ω - F t ω‖ ^ 2 ∂P) =
      ‖(h₂ s).toLp (F s) - (h₂ t).toLp (F t)‖ := by
    rw [← norm_toLp_sub_sq (h₂ s) (h₂ t), Real.sqrt_sq_eq_abs, abs_norm]
  have hh := (hi.continuousAt (x := t)).tendsto.sqrt
  have hz : (∫ ω, ‖F t ω - F t ω‖ ^ 2 ∂P) = 0 := by simp
  rw [hz, Real.sqrt_zero] at hh
  simpa only [he] using hh

/-- Bounded pointwise continuous velocities have the genuine time-L¹, label-L²
integrability needed by the transport-length argument. -/
theorem intervalIntegrable_toLp_of_uniform_bound [IsFiniteMeasure P]
    (F : ℝ → Ω → E) (h₂ : ∀ t, MemLp (F t) 2 P)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ t, ∀ᵐ ω ∂P, ‖F t ω‖ ≤ C)
    (hpath : ∀ᵐ ω ∂P, Continuous (fun t => F t ω)) (a b : ℝ) :
    IntervalIntegrable (fun t => (h₂ t).toLp (F t)) volume a b :=
  (continuous_toLp_of_uniform_bound F h₂ hC hbound hpath).intervalIntegrable a b

/-- Actual Euclidean coordinate linear map for the unnormalized configuration cost. -/
def euclideanMap {d N : ℕ} : Configuration d N →L[ℝ] EuclideanSpace ℝ (Fin N × Fin d) where
  toFun := configurationToEuclidean
  map_add' x y := by
    ext p
    simp [configurationToEuclidean, transportDisplacement]
  map_smul' c x := by
    ext p
    simp [configurationToEuclidean, transportDisplacement]
  cont := continuous_configurationToEuclidean

@[simp] theorem euclideanMap_apply {d N : ℕ} (x : Configuration d N) :
    euclideanMap x = configurationToEuclidean x := rfl

/-- Its norm uses exactly the stated quadratic cost, with no sup-norm substitution. -/
theorem euclideanMap_norm_sq {d N : ℕ} (x : Configuration d N) :
    ‖euclideanMap x‖ ^ 2 = productCost x 0 := by
  rw [productCost_eq_displacement_norm_sq]
  rfl

end SharpWasserstein.EulerianTransport
