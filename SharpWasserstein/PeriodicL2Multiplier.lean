import SharpWasserstein.PeriodicTestL2
import SharpWasserstein.WeakDerivativeLimit

/-! Actual multiplication by bounded smooth periodic coefficients in scalar
`L²`, preserving the closed periodic test-value space. This supplies the
admissible weak-Hessian pairings with products of the limiting optimizer. -/

noncomputable section
namespace SharpWasserstein.PeriodicL2Multiplier
open MeasureTheory Filter PeriodicIntegrationByParts PeriodicFourierTests PeriodicBochner
open PeriodicGalerkin PeriodicGradientClosure PeriodicSmoothGradient PeriodicTestL2 WeightedTangent
open scoped ENNReal Topology BigOperators ContDiff InnerProductSpace BoundedContinuousFunction

variable {n : ℕ} [MeasurableSpace (Point n)] [BorelSpace (Point n)]

theorem multiply_memLp (q : Point n →ᵇ ℝ) (u : Lp ℝ 2 (cubePoint (n := n))) :
    MemLp (fun y => q y * u y) 2 (cubePoint (n := n)) := by
  apply (Lp.memLp u).of_le_mul (c := ‖q‖)
    (q.continuous.aestronglyMeasurable.mul (Lp.aestronglyMeasurable u))
  filter_upwards [] with y
  change ‖q y * u y‖ ≤ ‖q‖ * ‖u y‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (q.norm_coe_le_norm y) (norm_nonneg _)

def multiply (q : Point n →ᵇ ℝ) (u : Lp ℝ 2 (cubePoint (n := n))) : Lp ℝ 2 (cubePoint (n := n)) :=
  (multiply_memLp q u).toLp (fun y => q y * u y)

theorem multiply_ae (q : Point n →ᵇ ℝ) (u : Lp ℝ 2 (cubePoint (n := n))) :
    multiply q u =ᵐ[cubePoint] (fun y => q y * u y) := (multiply_memLp q u).coeFn_toLp

def multiplyLinear (q : Point n →ᵇ ℝ) : Lp ℝ 2 (cubePoint (n := n)) →ₗ[ℝ] Lp ℝ 2 (cubePoint (n := n)) where
  toFun := multiply q
  map_add' u v := by
    apply Lp.ext
    filter_upwards [multiply_ae q (u + v), multiply_ae q u, multiply_ae q v,
      Lp.coeFn_add u v, Lp.coeFn_add (multiply q u) (multiply q v)] with y ha hb hc hd he
    rw [ha, he]
    simp only [Pi.add_apply, hb, hc, hd, mul_add]
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [multiply_ae q (c • u), multiply_ae q u,
      Lp.coeFn_smul c u, Lp.coeFn_smul c (multiply q u)] with y ha hb hc hd
    simp only [RingHom.id_apply]
    rw [ha, hd]
    simp only [Pi.smul_apply, hb, hc, smul_eq_mul]
    ring

theorem multiply_norm_le (q : Point n →ᵇ ℝ) (u : Lp ℝ 2 (cubePoint (n := n))) :
    ‖multiply q u‖ ≤ ‖q‖ * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [multiply_ae q u] with y hy
  rw [hy, norm_mul]
  exact mul_le_mul_of_nonneg_right (q.norm_coe_le_norm y) (norm_nonneg _)

/-- A genuine bounded multiplication operator on the scalar cube `L²` space. -/
def operator (q : Point n →ᵇ ℝ) : Lp ℝ 2 (cubePoint (n := n)) →L[ℝ] Lp ℝ 2 (cubePoint (n := n)) :=
  (multiplyLinear q).mkContinuous ‖q‖ (multiply_norm_le q)

theorem operator_ae (q : Point n →ᵇ ℝ) (u : Lp ℝ 2 (cubePoint (n := n))) :
    operator q u =ᵐ[cubePoint] (fun y => q y * u y) := multiply_ae q u

/-- Multiplying a smooth periodic test by a smooth periodic coefficient remains admissible. -/
def productTest (q : Point n →ᵇ ℝ)
    (hq : ContDiff ℝ ∞ (fun x => q ((coordinateEquiv n).symm x)))
    (hpq : Periodic (fun x => q ((coordinateEquiv n).symm x)))
    (φ : SmoothPeriodicTest n) : SmoothPeriodicTest n :=
  ⟨(fun x => q ((coordinateEquiv n).symm x)) * φ.val,
    hq.mul φ.property.1, fun i x => congrArg₂ (· * ·) (hpq i x) (φ.property.2 i x)⟩

/-- The actual multiplication operator acts on actual test values exactly as pointwise multiplication. -/
theorem operator_value (q : Point n →ᵇ ℝ)
    (hq : ContDiff ℝ ∞ (fun x => q ((coordinateEquiv n).symm x)))
    (hpq : Periodic (fun x => q ((coordinateEquiv n).symm x)))
    (φ : SmoothPeriodicTest n) : operator q (value φ) = value (productTest q hq hpq φ) := by
  apply Lp.ext
  filter_upwards [operator_ae q (value φ), scalarTestLp_ae (testCompactification φ),
    scalarTestLp_ae (testCompactification (productTest q hq hpq φ))] with y ha hb hc
  change operator q (value φ) y = scalarTestLp (testCompactification (productTest q hq hpq φ)) y
  rw [ha, hc]
  change q y * scalarTestLp (testCompactification φ) y = _
  rw [hb]
  change q y * (SmoothCutoff.cutoff n n y * φ.val (coordinateEquiv n y)) =
    SmoothCutoff.cutoff n n y * (q ((coordinateEquiv n).symm (coordinateEquiv n y)) *
      φ.val (coordinateEquiv n y))
  rw [ContinuousLinearEquiv.symm_apply_apply]
  ring

/-- Closed periodic test values are invariant under every actual smooth periodic multiplier. -/
theorem operator_mem_testClosure (q : Point n →ᵇ ℝ)
    (hq : ContDiff ℝ ∞ (fun x => q ((coordinateEquiv n).symm x)))
    (hpq : Periodic (fun x => q ((coordinateEquiv n).symm x)))
    {u : Lp ℝ 2 (cubePoint (n := n))} (hu : u ∈ WeakDerivativeLimit.testClosure value) :
    operator q u ∈ WeakDerivativeLimit.testClosure value := by
  have hle : WeakDerivativeLimit.testClosure (value (n := n)) ≤
      (WeakDerivativeLimit.testClosure value).comap (operator q).toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · rintro v ⟨φ, rfl⟩
      change operator q (value φ) ∈ WeakDerivativeLimit.testClosure value
      rw [operator_value q hq hpq]
      exact (value (n := n)).range.le_topologicalClosure (LinearMap.mem_range_self _ _)
    · exact (value (n := n)).range.isClosed_topologicalClosure.preimage (operator q).continuous
  exact hle hu

end SharpWasserstein.PeriodicL2Multiplier
