module

public import SharpWasserstein.Compat
public import SharpWasserstein.WeightedTangent
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Analysis.InnerProductSpace.LaxMilgram
public import Mathlib.Analysis.Normed.Operator.Bilinear

@[expose] public section

/-! Actual bounded-density multiplication on weighted `L²` and its coercive
operator on the closed space of compact smooth gradients. -/

noncomputable section
namespace SharpWasserstein.WeightedDensity

open MeasureTheory Set Filter WeightedTangent
open scoped InnerProductSpace Topology BoundedContinuousFunction

variable {d : ℕ} [MeasurableSpace (Point d)] [BorelSpace (Point d)]
variable (μ : Measure (Point d)) [IsFiniteMeasure μ]

omit [IsFiniteMeasure μ] in
/-- Multiplication by a genuine bounded continuous scalar density preserves weighted `L²`. -/
theorem densityMul_memLp (ρ : Point d →ᵇ ℝ) (v : Lp (Point d) 2 μ) :
    MemLp (fun x => ρ x • v x) 2 μ := by
  apply (Lp.memLp v).of_le_mul (c := ‖ρ‖) (ρ.continuous.aestronglyMeasurable.smul (Lp.aestronglyMeasurable v))
  filter_upwards [] with x
  change ‖ρ x • v x‖ ≤ ‖ρ‖ * ‖v x‖
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (ρ.norm_coe_le_norm x) (norm_nonneg _)

/-- Actual multiplication, quotiented only by almost-everywhere equality. -/
def densityMul (ρ : Point d →ᵇ ℝ) (v : Lp (Point d) 2 μ) : Lp (Point d) 2 μ :=
  (densityMul_memLp μ ρ v).toLp (fun x => ρ x • v x)

omit [IsFiniteMeasure μ] in
theorem densityMul_ae (ρ : Point d →ᵇ ℝ) (v : Lp (Point d) 2 μ) :
    densityMul μ ρ v =ᵐ[μ] fun x => ρ x • v x := (densityMul_memLp μ ρ v).coeFn_toLp

/-- Scalar-density multiplication is linear in the vector field. -/
def densityMulLinear (ρ : Point d →ᵇ ℝ) : Lp (Point d) 2 μ →ₗ[ℝ] Lp (Point d) 2 μ where
  toFun := densityMul μ ρ
  map_add' v w := by
    apply Lp.ext
    filter_upwards [densityMul_ae μ ρ (v + w), densityMul_ae μ ρ v, densityMul_ae μ ρ w,
      Lp.coeFn_add v w, Lp.coeFn_add (densityMul μ ρ v) (densityMul μ ρ w)] with x ha hb hc hd he
    rw [ha, he]
    simp only [Pi.add_apply, hb, hc, hd, smul_add]
  map_smul' c v := by
    apply Lp.ext
    filter_upwards [densityMul_ae μ ρ (c • v), densityMul_ae μ ρ v,
      Lp.coeFn_smul c v, Lp.coeFn_smul c (densityMul μ ρ v)] with x ha hb hc hd
    simp only [RingHom.id_apply]
    rw [ha, hd]
    simp only [Pi.smul_apply, hb, hc]
    exact smul_comm _ _ _

omit [IsFiniteMeasure μ] in
/-- Exact operator bound with the actual supremum norm of the density. -/
theorem densityMul_norm_le (ρ : Point d →ᵇ ℝ) (v : Lp (Point d) 2 μ) :
    ‖densityMul μ ρ v‖ ≤ ‖ρ‖ * ‖v‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [densityMul_ae μ ρ v] with x hx
  rw [hx, norm_smul]
  exact mul_le_mul_of_nonneg_right (ρ.norm_coe_le_norm x) (norm_nonneg _)

/-- Joint bilinearity in density and vector field. -/
def densityMulBilinear : (Point d →ᵇ ℝ) →ₗ[ℝ] Lp (Point d) 2 μ →ₗ[ℝ] Lp (Point d) 2 μ where
  toFun := densityMulLinear μ
  map_add' ρ η := by
    apply LinearMap.ext
    intro v
    change densityMul μ (ρ + η) v = densityMul μ ρ v + densityMul μ η v
    apply Lp.ext
    filter_upwards [densityMul_ae μ (ρ + η) v, densityMul_ae μ ρ v, densityMul_ae μ η v,
      Lp.coeFn_add (densityMul μ ρ v) (densityMul μ η v)] with x ha hb hc hd
    rw [ha, hd]
    simp only [Pi.add_apply, hb, hc, BoundedContinuousFunction.add_apply, add_smul]
  map_smul' c ρ := by
    apply LinearMap.ext
    intro v
    change densityMul μ (c • ρ) v = c • densityMul μ ρ v
    apply Lp.ext
    filter_upwards [densityMul_ae μ (c • ρ) v, densityMul_ae μ ρ v,
      Lp.coeFn_smul c (densityMul μ ρ v)] with x ha hb hc
    rw [ha, hc]
    simp only [Pi.smul_apply, hb, BoundedContinuousFunction.smul_apply, smul_assoc]

/-- Continuous linear dependence of the multiplication operator on a bounded continuous density. -/
def densityMulOperator : (Point d →ᵇ ℝ) →L[ℝ] Lp (Point d) 2 μ →L[ℝ] Lp (Point d) 2 μ :=
  (densityMulBilinear μ).mkContinuous₂ 1 (by
    intro ρ v
    change ‖densityMul μ ρ v‖ ≤ 1 * ‖ρ‖ * ‖v‖
    simpa only [one_mul] using densityMul_norm_le μ ρ v)

/-- The coercive weighted operator is actual density multiplication followed by gradient projection. -/
def weightedOperator : (Point d →ᵇ ℝ) →L[ℝ] gradientClosure μ →L[ℝ] gradientClosure μ :=
  let R : (Lp (Point d) 2 μ →L[ℝ] Lp (Point d) 2 μ) →L[ℝ]
      (gradientClosure μ →L[ℝ] Lp (Point d) 2 μ) :=
    (ContinuousLinearMap.flipₗᵢ ℝ
      (Lp (Point d) 2 μ →L[ℝ] Lp (Point d) 2 μ)
      (gradientClosure μ →L[ℝ] Lp (Point d) 2 μ)
      (gradientClosure μ →L[ℝ] Lp (Point d) 2 μ)
      (ContinuousLinearMap.compL ℝ (gradientClosure μ) (Lp (Point d) 2 μ) (Lp (Point d) 2 μ)))
      (gradientClosure μ).subtypeL
  let P : (gradientClosure μ →L[ℝ] Lp (Point d) 2 μ) →L[ℝ]
      (gradientClosure μ →L[ℝ] gradientClosure μ) :=
    ContinuousLinearMap.compL ℝ (gradientClosure μ) (Lp (Point d) 2 μ) (gradientClosure μ)
      (gradientClosure μ).orthogonalProjectionOnto
  P.comp (R.comp (densityMulOperator μ))

/-- The operator's bilinear form is an actual integral with the given density. -/
theorem weightedOperator_inner (ρ : Point d →ᵇ ℝ) (v w : gradientClosure μ) :
    ⟪weightedOperator μ ρ v, w⟫_ℝ =
      ∫ x, ρ x * ⟪(v : Lp (Point d) 2 μ) x, (w : Lp (Point d) 2 μ) x⟫_ℝ ∂μ := by
  change ⟪(gradientClosure μ).orthogonalProjectionOnto (densityMul μ ρ v), w⟫_ℝ = _
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [densityMul_ae μ ρ v] with x hx
  rw [hx, real_inner_smul_left]

/-- The integral pairing is integrable, so the weighted form does not rely on a totalized integral. -/
theorem integrable_weighted_inner (ρ : Point d →ᵇ ℝ) (v w : gradientClosure μ) :
    Integrable (fun x => ρ x * ⟪(v : Lp (Point d) 2 μ) x, (w : Lp (Point d) 2 μ) x⟫_ℝ) μ := by
  apply (L2.integrable_inner (𝕜 := ℝ) (densityMul μ ρ v) w).congr
  filter_upwards [densityMul_ae μ ρ v] with x hx
  rw [hx, real_inner_smul_left]

/-- The actual density-weighted bilinear form on the fixed closed gradient space. -/
def bilinearForm (ρ : Point d →ᵇ ℝ) : gradientClosure μ →L[ℝ] gradientClosure μ →L[ℝ] ℝ :=
  (innerSL ℝ).comp (weightedOperator μ ρ)

/-- Positive lower bounds on the density prove genuine coercivity. -/
theorem bilinearForm_coercive (ρ : Point d →ᵇ ℝ) {a : ℝ} (ha : 0 < a)
    (hρ : ∀ᵐ x ∂μ, a ≤ ρ x) : IsCoercive (bilinearForm μ ρ) := by
  refine ⟨a, ha, fun v => ?_⟩
  change a * ‖v‖ * ‖v‖ ≤ ⟪weightedOperator μ ρ v, v⟫_ℝ
  rw [weightedOperator_inner]
  simp_rw [real_inner_self_eq_norm_sq]
  have hi : Integrable (fun x => ‖(v : Lp (Point d) 2 μ) x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (v : Lp (Point d) 2 μ))).mp
      (Lp.memLp (v : Lp (Point d) 2 μ))
  have hρi := integrable_weighted_inner μ ρ v v
  simp_rw [real_inner_self_eq_norm_sq] at hρi
  calc
    a * ‖v‖ * ‖v‖ = ∫ x, a * ‖(v : Lp (Point d) 2 μ) x‖ ^ 2 ∂μ := by
      rw [integral_const_mul, ← lp_norm_sq_eq_integral]
      change a * ‖(v : Lp (Point d) 2 μ)‖ * ‖(v : Lp (Point d) 2 μ)‖ = _
      ring
    _ ≤ _ := integral_mono_ae (hi.const_mul a) hρi (hρ.mono fun x hx =>
      mul_le_mul_of_nonneg_right hx (sq_nonneg _))

/-- Symmetry follows from the genuine real weighted inner product. -/
theorem weightedOperator_symmetric (ρ : Point d →ᵇ ℝ) (v w : gradientClosure μ) :
    ⟪weightedOperator μ ρ v, w⟫_ℝ = ⟪v, weightedOperator μ ρ w⟫_ℝ := by
  rw [real_inner_comm (weightedOperator μ ρ w) v, weightedOperator_inner, weightedOperator_inner]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [real_inner_comm]

/-- Positive density produces an actual invertible operator by the Lax–Milgram theorem. -/
theorem weightedOperator_isUnit (ρ : Point d →ᵇ ℝ) {a : ℝ} (ha : 0 < a)
    (hρ : ∀ᵐ x ∂μ, a ≤ ρ x) : IsUnit (weightedOperator μ ρ) := by
  have hc := bilinearForm_coercive μ ρ ha hρ
  refine ⟨hc.continuousLinearEquivOfBilin.toUnit, ?_⟩
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_right ℝ
  intro w
  exact hc.continuousLinearEquivOfBilin_apply v w

/-- The quadratic form is nonnegative under the same verified density bound. -/
theorem weightedOperator_nonneg (ρ : Point d →ᵇ ℝ) {a : ℝ} (ha : 0 < a)
    (hρ : ∀ᵐ x ∂μ, a ≤ ρ x) (v : gradientClosure μ) :
    0 ≤ ⟪weightedOperator μ ρ v, v⟫_ℝ := by
  obtain ⟨C, hC, hB⟩ := bilinearForm_coercive μ ρ ha hρ
  exact (by positivity : 0 ≤ C * ‖v‖ * ‖v‖).trans (hB v)

end SharpWasserstein.WeightedDensity
