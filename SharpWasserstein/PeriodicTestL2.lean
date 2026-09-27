import SharpWasserstein.PeriodicHessianBounds

/-! Actual scalar test values, derivatives, and vector coordinates in the
fundamental cube's `L²` spaces. These maps make the distributional Hessian
limit a statement about integrals, not abstract named pairings. -/

noncomputable section
namespace SharpWasserstein.PeriodicTestL2
open MeasureTheory Filter PeriodicIntegrationByParts PeriodicFourierTests PeriodicBochner
open PeriodicGalerkin PeriodicGradientClosure PeriodicSmoothGradient PeriodicHessianBounds WeightedTangent
open scoped ENNReal Topology BigOperators ContDiff InnerProductSpace

variable {n : ℕ} [MeasurableSpace (Point n)] [BorelSpace (Point n)]

/-- Actual compact scalar test values belong to `L²` for the cube probability measure. -/
def scalarTestLp (φ : WeightedTangent.Test n) : Lp ℝ 2 (cubePoint (n := n)) :=
  (φ.property.1.continuous.memLp_of_hasCompactSupport φ.property.2).toLp (φ : Point n → ℝ)

theorem scalarTestLp_ae (φ : WeightedTangent.Test n) :
    scalarTestLp φ =ᵐ[(cubePoint (n := n))] (φ : Point n → ℝ) :=
  MemLp.coeFn_toLp _

/-- The actual value map is linear in the compact scalar test. -/
def scalarTestLpLinear : WeightedTangent.Test n →ₗ[ℝ] Lp ℝ 2 (cubePoint (n := n)) where
  toFun := scalarTestLp
  map_add' φ ψ := by
    apply Lp.ext
    filter_upwards [scalarTestLp_ae (φ + ψ), Lp.coeFn_add (scalarTestLp φ) (scalarTestLp ψ),
      scalarTestLp_ae φ, scalarTestLp_ae ψ] with y ha hb hc hd
    rw [ha, hb]
    simp only [Pi.add_apply, hc, hd]
    rfl
  map_smul' c φ := by
    apply Lp.ext
    filter_upwards [scalarTestLp_ae (c • φ), Lp.coeFn_smul c (scalarTestLp φ),
      scalarTestLp_ae φ] with y ha hb hc
    simp only [RingHom.id_apply]
    rw [ha, hb]
    simp only [Pi.smul_apply, hc]
    rfl

/-- Actual `L²` values of smooth periodic tests, via a fixed compact representative. -/
def value : SmoothPeriodicTest n →ₗ[ℝ] Lp ℝ 2 (cubePoint (n := n)) :=
  scalarTestLpLinear.comp testCompactification

/-- Genuine coordinate differentiation on the vector space of periodic tests. -/
def partialLinear (i : Fin n) : SmoothPeriodicTest n →ₗ[ℝ] SmoothPeriodicTest n where
  toFun f := partialTest f i
  map_add' f g := by
    apply Subtype.ext
    exact coordinatePartial_add (f.property.1.differentiable (by simp))
      (g.property.1.differentiable (by simp)) i
  map_smul' c f := by
    apply Subtype.ext
    exact funext (coordinatePartial_smul c f.val i)

/-- Actual `L²` values of the derivative of each periodic test. -/
def derivative (i : Fin n) : SmoothPeriodicTest n →ₗ[ℝ] Lp ℝ 2 (cubePoint (n := n)) :=
  value.comp (partialLinear i)

/-- A genuine coordinate functional on Euclidean vectors. -/
def coordinate (j : Fin n) : Point n →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j).comp (coordinateEquiv n).toContinuousLinearMap

omit [MeasurableSpace (Point n)] [BorelSpace (Point n)] in
@[simp] theorem coordinate_apply (j : Fin n) (x : Point n) : coordinate j x = x j := rfl

/-- Its action on actual equivalence classes is a continuous linear map. -/
def component (j : Fin n) : Lp (Point n) 2 (cubePoint (n := n)) →L[ℝ] Lp ℝ 2 (cubePoint (n := n)) :=
  (coordinate j).compLpL 2 (cubePoint (n := n))

omit [BorelSpace (Point n)] in
theorem component_ae (j : Fin n) (v : Lp (Point n) 2 (cubePoint (n := n))) :
    component j v =ᵐ[(cubePoint (n := n))] (fun y => v y j) :=
  (coordinate j).coeFn_compLpL v

omit [MeasurableSpace (Point n)] [BorelSpace (Point n)] in
theorem coordinate_norm_le_one (j : Fin n) : ‖coordinate j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [coordinate_apply, one_mul] using PiLp.norm_apply_le x j

omit [BorelSpace (Point n)] in
/-- Taking one coordinate is a contraction of the actual Euclidean `L²` norm. -/
theorem component_norm_le (j : Fin n) (v : Lp (Point n) 2 (cubePoint (n := n))) :
    ‖component j v‖ ≤ ‖v‖ := by
  calc
    _ ≤ ‖coordinate j‖ * ‖v‖ := (coordinate j).norm_compLp_le v
    _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right (coordinate_norm_le_one j) (norm_nonneg v)
    _ = _ := one_mul _

omit [MeasurableSpace (Point n)] [BorelSpace (Point n)] in
/-- Scalar test values coincide with the prescribed periodic function throughout the cube. -/
theorem compactTest_value_on_cube (f : Coordinates n → ℝ) (hf : ContDiff ℝ ∞ f)
    {x : Coordinates n} (hx : x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1)) :
    (compactTest f hf : Point n → ℝ) ((coordinateEquiv n).symm x) = f x := by
  have h := (compactTest_eq_near_cube f hf hx).eq_of_nhds
  simpa only [pullback, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply] using h

/-- The Hilbert pairing of an actual derivative and compact scalar value is its integral. -/
theorem inner_component_testGradient_scalarTestLp (Φ Ψ : WeightedTangent.Test n) (j : Fin n) :
    ⟪component j (testGradient (cubePoint (n := n)) Φ), scalarTestLp Ψ⟫_ℝ =
      ∫ y, gradient (Φ : Point n → ℝ) y j * (Ψ : Point n → ℝ) y ∂(cubePoint (n := n)) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [component_ae j (testGradient (cubePoint (n := n)) Φ), testGradient_ae (cubePoint (n := n)) Φ,
    scalarTestLp_ae Ψ] with y ha hb hc
  rw [ha, hb, hc]
  simp [RCLike.inner_apply, mul_comm]

/-- Genuine first-derivative pairings in the actual fundamental cube. -/
theorem inner_component_gradient_value (f : Coordinates n → ℝ) (hf : ContDiff ℝ ∞ f)
    (j : Fin n) (φ : SmoothPeriodicTest n) :
    ⟪component j (gradientVector f hf : Lp (Point n) 2 (cubePoint (n := n))), value φ⟫_ℝ =
      ∫ x, coordinatePartial f j x * φ.val x ∂cube n := by
  change ⟪component j (testGradient (cubePoint (n := n)) (compactTest f hf)),
    scalarTestLp (compactTest φ.val φ.property.1)⟫_ℝ = _
  rw [inner_component_testGradient_scalarTestLp, integral_cubePoint]
  apply integral_congr_ae
  filter_upwards [cube_ae_mem n] with x hx
  rw [compactTest_gradient_on_cube f hf hx, compactTest_value_on_cube φ.val φ.property.1 hx,
    ← PDEPairings.directionDeriv_eq_gradient_component, directionDeriv_pullback,
    ContinuousLinearEquiv.apply_symm_apply]

/-- Genuine second-derivative pairings in the actual fundamental cube. -/
theorem inner_component_hessian_value (f : Coordinates n → ℝ) (hf : ContDiff ℝ ∞ f)
    (i j : Fin n) (φ : SmoothPeriodicTest n) :
    ⟪component i (hessianColumn f hf j), value φ⟫_ℝ =
      ∫ x, coordinatePartial (coordinatePartial f j) i x * φ.val x ∂cube n := by
  change ⟪component i (testGradient (cubePoint (n := n))
    (PDEPairings.directionTest (compactTest f hf) (EuclideanSpace.single j 1))),
    scalarTestLp (compactTest φ.val φ.property.1)⟫_ℝ = _
  rw [inner_component_testGradient_scalarTestLp, integral_cubePoint]
  apply integral_congr_ae
  filter_upwards [cube_ae_mem n] with x hx
  rw [directionGradient_on_cube f hf j hx, compactTest_value_on_cube φ.val φ.property.1 hx,
    ← PDEPairings.directionDeriv_eq_gradient_component, directionDeriv_pullback,
    ContinuousLinearEquiv.apply_symm_apply]

/-- Actual periodic integration by parts gives each Hessian entry's weak derivative equation. -/
theorem hessian_component_weak_equation (f : Coordinates n → ℝ) (hf : ContDiff ℝ ∞ f)
    (hp : Periodic f) (i j : Fin n) (φ : SmoothPeriodicTest n) :
    ⟪component i (hessianColumn f hf j), value φ⟫_ℝ =
      -⟪component j (gradientVector f hf : Lp (Point n) 2 (cubePoint (n := n))), derivative i φ⟫_ℝ := by
  change _ = -⟪component j (gradientVector f hf : Lp (Point n) 2 (cubePoint (n := n))), value (partialTest φ i)⟫_ℝ
  rw [inner_component_hessian_value, inner_component_gradient_value]
  have he := integral_mul_coordinatePartial
    (φ.property.1.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1))
    ((smooth_coordinatePartial hf j).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1))
    φ.property.2 (periodic_coordinatePartial hp j) i
  simp only [partialTest] at *
  convert he using 1
  congr 1
  funext x
  exact mul_comm _ _

/-- Every scalar `L²` pairing with a periodic test is its genuine cube integral. -/
theorem inner_value (u : Lp ℝ 2 (cubePoint (n := n))) (φ : SmoothPeriodicTest n) :
    ⟪u, value φ⟫_ℝ = ∫ x, u ((coordinateEquiv n).symm x) * φ.val x ∂cube n := by
  rw [L2.inner_def]
  calc
    _ = ∫ y, u y * (compactTest φ.val φ.property.1 : Point n → ℝ) y ∂(cubePoint (n := n)) := by
      apply integral_congr_ae
      filter_upwards [scalarTestLp_ae (compactTest φ.val φ.property.1)] with y hy
      change ⟪u y, scalarTestLp (compactTest φ.val φ.property.1) y⟫_ℝ = _
      rw [hy]
      simp [RCLike.inner_apply, mul_comm]
    _ = _ := by
      rw [integral_cubePoint]
      apply integral_congr_ae
      filter_upwards [cube_ae_mem n] with x hx
      rw [compactTest_value_on_cube φ.val φ.property.1 hx]

/-- Every vector-component test pairing is its genuine cube integral. -/
theorem inner_component_value (u : Lp (Point n) 2 (cubePoint (n := n)))
    (j : Fin n) (φ : SmoothPeriodicTest n) :
    ⟪component j u, value φ⟫_ℝ =
      ∫ x, u ((coordinateEquiv n).symm x) j * φ.val x ∂cube n := by
  rw [L2.inner_def]
  calc
    _ = ∫ y, u y j * (compactTest φ.val φ.property.1 : Point n → ℝ) y ∂(cubePoint (n := n)) := by
      apply integral_congr_ae
      filter_upwards [component_ae j u, scalarTestLp_ae (compactTest φ.val φ.property.1)] with y hy hz
      change ⟪component j u y, scalarTestLp (compactTest φ.val φ.property.1) y⟫_ℝ = _
      rw [hy, hz]
      simp [RCLike.inner_apply, mul_comm]
    _ = _ := by
      rw [integral_cubePoint]
      apply integral_congr_ae
      filter_upwards [cube_ae_mem n] with x hx
      rw [compactTest_value_on_cube φ.val φ.property.1 hx]

end SharpWasserstein.PeriodicTestL2
