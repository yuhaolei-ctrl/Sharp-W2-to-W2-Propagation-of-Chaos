import SharpWasserstein.PeriodicOptimizerProducts
import SharpWasserstein.PeriodicDriftEnergy
import SharpWasserstein.PeriodicSmoothBounds

/-! Actual bounded matrix multiplication on the Euclidean cube `L²` space,
with its genuine integral quadratic form. Strong Galerkin convergence passes
the weighted Jacobian form of every smooth periodic drift to the optimizer;
no continuity or convergence of the desired quadratic form is postulated. -/

noncomputable section
namespace SharpWasserstein.PeriodicJacobianLimit
open MeasureTheory Filter PeriodicIntegrationByParts PeriodicFourierTests PeriodicBochner
open PeriodicGalerkin PeriodicGradientClosure PeriodicSmoothGradient PeriodicTestL2 WeightedTangent
open PeriodicDriftEnergy
open scoped ENNReal Topology BigOperators ContDiff InnerProductSpace BoundedContinuousFunction

variable {n : ℕ} [MeasurableSpace (Point n)] [BorelSpace (Point n)]

/-- Applying an actual bounded continuous matrix field preserves vector `L²`. -/
theorem matrix_memLp (A : Point n →ᵇ (Point n →L[ℝ] Point n))
    (u : Lp (Point n) 2 (cubePoint (n := n))) :
    MemLp (fun y => A y (u y)) 2 (cubePoint (n := n)) := by
  apply (Lp.memLp u).of_le_mul (c := ‖A‖)
    ((isBoundedBilinearMap_apply (𝕜 := ℝ)).continuous.comp_aestronglyMeasurable₂
      A.continuous.aestronglyMeasurable (Lp.aestronglyMeasurable u))
  filter_upwards [] with y
  exact (A y).le_opNorm (u y) |>.trans
    (mul_le_mul_of_nonneg_right (A.norm_coe_le_norm y) (norm_nonneg _))

/-- The actual almost-everywhere matrix product as an `L²` equivalence class. -/
def matrixMultiply (A : Point n →ᵇ (Point n →L[ℝ] Point n))
    (u : Lp (Point n) 2 (cubePoint (n := n))) : Lp (Point n) 2 (cubePoint (n := n)) :=
  (matrix_memLp A u).toLp (fun y => A y (u y))

theorem matrixMultiply_ae (A : Point n →ᵇ (Point n →L[ℝ] Point n))
    (u : Lp (Point n) 2 (cubePoint (n := n))) :
    matrixMultiply A u =ᵐ[cubePoint] (fun y => A y (u y)) := (matrix_memLp A u).coeFn_toLp

def matrixLinear (A : Point n →ᵇ (Point n →L[ℝ] Point n)) :
    Lp (Point n) 2 (cubePoint (n := n)) →ₗ[ℝ] Lp (Point n) 2 (cubePoint (n := n)) where
  toFun := matrixMultiply A
  map_add' u v := by
    apply Lp.ext
    filter_upwards [matrixMultiply_ae A (u + v), matrixMultiply_ae A u,
      matrixMultiply_ae A v, Lp.coeFn_add u v,
      Lp.coeFn_add (matrixMultiply A u) (matrixMultiply A v)] with y ha hb hc hd he
    rw [ha, he]
    simp only [Pi.add_apply, hb, hc, hd, map_add]
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [matrixMultiply_ae A (c • u), matrixMultiply_ae A u,
      Lp.coeFn_smul c u, Lp.coeFn_smul c (matrixMultiply A u)] with y ha hb hc hd
    simp only [RingHom.id_apply]
    rw [ha, hd]
    simp only [Pi.smul_apply, hb, hc, map_smul]

theorem matrixMultiply_norm_le (A : Point n →ᵇ (Point n →L[ℝ] Point n))
    (u : Lp (Point n) 2 (cubePoint (n := n))) : ‖matrixMultiply A u‖ ≤ ‖A‖ * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [matrixMultiply_ae A u] with y hy
  rw [hy]
  exact (A y).le_opNorm (u y) |>.trans
    (mul_le_mul_of_nonneg_right (A.norm_coe_le_norm y) (norm_nonneg _))

/-- Genuine pointwise matrix multiplication is a bounded linear operator. -/
def matrixOperator (A : Point n →ᵇ (Point n →L[ℝ] Point n)) :
    Lp (Point n) 2 (cubePoint (n := n)) →L[ℝ] Lp (Point n) 2 (cubePoint (n := n)) :=
  (matrixLinear A).mkContinuous ‖A‖ (matrixMultiply_norm_le A)

theorem matrixOperator_ae (A : Point n →ᵇ (Point n →L[ℝ] Point n))
    (u : Lp (Point n) 2 (cubePoint (n := n))) :
    matrixOperator A u =ᵐ[cubePoint] (fun y => A y (u y)) := matrixMultiply_ae A u

/-- Its Hilbert quadratic form is the actual integral of the matrix quadratic form. -/
theorem inner_matrixOperator (A : Point n →ᵇ (Point n →L[ℝ] Point n))
    (u v : Lp (Point n) 2 (cubePoint (n := n))) :
    ⟪matrixOperator A u, v⟫_ℝ = ∫ y, ⟪A y (u y), v y⟫_ℝ ∂cubePoint := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [matrixOperator_ae A u] with y hy
  rw [hy]

/-- Actual bounded matrix quadratic integrals are continuous under strong `L²` convergence. -/
theorem integral_quadratic_tendsto {ι : Type*} {L : Filter ι}
    (A : Point n →ᵇ (Point n →L[ℝ] Point n))
    {u : ι → Lp (Point n) 2 (cubePoint (n := n))}
    {uLimit : Lp (Point n) 2 (cubePoint (n := n))} (hu : Tendsto u L (𝓝 uLimit)) :
    Tendsto (fun k => ∫ y, ⟪A y (u k y), u k y⟫_ℝ ∂cubePoint) L
      (𝓝 (∫ y, ⟪A y (uLimit y), uLimit y⟫_ℝ ∂cubePoint)) := by
  simpa only [Function.comp_apply, inner_matrixOperator] using
    (((matrixOperator A).continuous.continuousAt.tendsto.comp hu).inner (𝕜 := ℝ) hu)

/-- Matrix pairings are genuinely integrable. -/
theorem integrable_matrix_inner (A : Point n →ᵇ (Point n →L[ℝ] Point n))
    (u v : Lp (Point n) 2 (cubePoint (n := n))) :
    Integrable (fun y => ⟪A y (u y), v y⟫_ℝ) cubePoint := by
  apply (L2.integrable_inner (𝕜 := ℝ) (matrixOperator A u) v).congr
  filter_upwards [matrixOperator_ae A u] with y hy
  rw [hy]

omit [MeasurableSpace (Point n)] [BorelSpace (Point n)] in
/-- Exact derivative conjugation by the actual coordinate equivalence. -/
theorem fderiv_vectorPullback (a : Coordinates n → Coordinates n) (y : Point n) :
    fderiv ℝ (vectorPullback a) y = (coordinateEquiv n).symm.toContinuousLinearMap.comp
      ((fderiv ℝ a (coordinateEquiv n y)).comp (coordinateEquiv n).toContinuousLinearMap) := by
  change fderiv ℝ ((coordinateEquiv n).symm ∘ (a ∘ coordinateEquiv n)) y = _
  rw [(coordinateEquiv n).symm.comp_fderiv, (coordinateEquiv n).comp_right_fderiv]

omit [MeasurableSpace (Point n)] [BorelSpace (Point n)] in
/-- The real Euclidean Jacobian of a smooth periodic vector field has a global bound. -/
theorem exists_jacobian_bound (a : Coordinates n → Coordinates n)
    (ha : ContDiff ℝ ∞ a) (hpa : ∀ i, Periodic (fun x => a x i)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖fderiv ℝ (vectorPullback a) y‖ ≤ C := by
  have hA : ContDiff ℝ ∞ (vectorPullback a) :=
    (coordinateEquiv n).symm.contDiff.comp (ha.comp (coordinateEquiv n).contDiff)
  have hp : ∀ i, Function.Periodic a (Pi.single i 1) := by
    intro i x
    ext j
    exact hpa j i x
  have hg : ∀ i, Function.Periodic
      (fun x => fderiv ℝ (vectorPullback a) ((coordinateEquiv n).symm x)) (Pi.single i 1) := by
    intro i x
    simp only [fderiv_vectorPullback, ContinuousLinearEquiv.apply_symm_apply]
    rw [PeriodicSmoothBounds.periodic_fderiv hp i x]
  obtain ⟨C, hC, hb⟩ := PeriodicSmoothBounds.norm_bound hg
    ((hA.continuous_fderiv (by simp)).comp (coordinateEquiv n).symm.continuous)
  exact ⟨C, hC, fun y => by simpa only [ContinuousLinearEquiv.symm_apply_apply] using hb (coordinateEquiv n y)⟩

omit [MeasurableSpace (Point n)] [BorelSpace (Point n)] in
/-- The actual derivative field, bundled with its proved global boundedness. -/
def jacobianField (a : Coordinates n → Coordinates n)
    (ha : ContDiff ℝ ∞ a) (hpa : ∀ i, Periodic (fun x => a x i)) :
    Point n →ᵇ (Point n →L[ℝ] Point n) :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fderiv ℝ (vectorPullback a))
    (((coordinateEquiv n).symm.contDiff.comp
      (ha.comp (coordinateEquiv n).contDiff)).continuous_fderiv (by simp))
    (exists_jacobian_bound a ha hpa).choose (exists_jacobian_bound a ha hpa).choose_spec.2

omit [MeasurableSpace (Point n)] [BorelSpace (Point n)] in
@[simp] theorem jacobianField_apply (a : Coordinates n → Coordinates n)
    (ha : ContDiff ℝ ∞ a) (hpa : ∀ i, Periodic (fun x => a x i)) (y : Point n) :
    jacobianField a ha hpa y = fderiv ℝ (vectorPullback a) y := rfl

omit [MeasurableSpace (Point n)] [BorelSpace (Point n)] in
/-- Actual density times the genuine drift Jacobian. -/
def jacobianCoefficient (ρ : Point n →ᵇ ℝ) (a : Coordinates n → Coordinates n)
    (ha : ContDiff ℝ ∞ a) (hpa : ∀ i, Periodic (fun x => a x i)) :
    Point n →ᵇ (Point n →L[ℝ] Point n) := ρ • jacobianField a ha hpa

omit [MeasurableSpace (Point n)] [BorelSpace (Point n)] in
@[simp] theorem jacobianCoefficient_apply (ρ : Point n →ᵇ ℝ) (a : Coordinates n → Coordinates n)
    (ha : ContDiff ℝ ∞ a) (hpa : ∀ i, Periodic (fun x => a x i)) (y : Point n) :
    jacobianCoefficient ρ a ha hpa y = ρ y • fderiv ℝ (vectorPullback a) y := rfl

/-- The weighted Jacobian pairing of arbitrary actual `L²` fields is its literal integral. -/
theorem inner_jacobianCoefficient (ρ : Point n →ᵇ ℝ) (a : Coordinates n → Coordinates n)
    (ha : ContDiff ℝ ∞ a) (hpa : ∀ i, Periodic (fun x => a x i))
    (u v : Lp (Point n) 2 (cubePoint (n := n))) :
    ⟪matrixOperator (jacobianCoefficient ρ a ha hpa) u, v⟫_ℝ =
      ∫ y, ρ y * ⟪fderiv ℝ (vectorPullback a) y (u y), v y⟫_ℝ ∂cubePoint := by
  rw [inner_matrixOperator]
  simp only [jacobianCoefficient_apply, smul_apply, real_inner_smul_left]

/-- This genuine weighted Jacobian integrand is integrable for arbitrary vector `L²` fields. -/
theorem integrable_jacobian_inner (ρ : Point n →ᵇ ℝ) (a : Coordinates n → Coordinates n)
    (ha : ContDiff ℝ ∞ a) (hpa : ∀ i, Periodic (fun x => a x i))
    (u v : Lp (Point n) 2 (cubePoint (n := n))) :
    Integrable (fun y => ρ y * ⟪fderiv ℝ (vectorPullback a) y (u y), v y⟫_ℝ) cubePoint := by
  simpa only [jacobianCoefficient_apply, smul_apply, real_inner_smul_left]
    using integrable_matrix_inner (jacobianCoefficient ρ a ha hpa) u v

/-- On a genuine smooth test gradient, the matrix operator gives exactly the manuscript's Jacobian form. -/
theorem inner_jacobian_gradientVector (ρ : Point n →ᵇ ℝ)
    (a : Coordinates n → Coordinates n) (ha : ContDiff ℝ ∞ a)
    (hpa : ∀ i, Periodic (fun x => a x i)) (f : Coordinates n → ℝ) (hf : ContDiff ℝ ∞ f) :
    ⟪matrixOperator (jacobianCoefficient ρ a ha hpa)
      (gradientVector f hf : Lp (Point n) 2 (cubePoint (n := n))),
      (gradientVector f hf : Lp (Point n) 2 cubePoint)⟫_ℝ =
      ∫ x, ρ ((coordinateEquiv n).symm x) * jacobianForm a f x ∂cube n := by
  rw [inner_jacobianCoefficient]
  calc
    _ = ∫ y, ρ y * ⟪fderiv ℝ (vectorPullback a) y
        (gradient (compactTest f hf : Point n → ℝ) y),
        gradient (compactTest f hf : Point n → ℝ) y⟫_ℝ ∂cubePoint := by
      apply integral_congr_ae
      filter_upwards [testGradient_ae (cubePoint (n := n)) (compactTest f hf)] with y hy
      change ρ y * ⟪fderiv ℝ (vectorPullback a) y
        (testGradient cubePoint (compactTest f hf) y),
        testGradient cubePoint (compactTest f hf) y⟫_ℝ = _
      rw [hy]
    _ = _ := by
      rw [integral_cubePoint]
      apply integral_congr_ae
      filter_upwards [cube_ae_mem n] with x hx
      rw [compactTest_gradient_on_cube f hf hx]
      rfl

/-- Exact finite Fourier Galerkin identification, not an abstract quadratic-form hypothesis. -/
theorem inner_jacobian_vector (ρ : Point n →ᵇ ℝ)
    (ℓ : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)
    (a : Coordinates n → Coordinates n) (ha : ContDiff ℝ ∞ a)
    (hpa : ∀ i, Periodic (fun x => a x i)) (s : Finset ((Fin n → ℤ) × Bool)) :
    ⟪matrixOperator (jacobianCoefficient ρ a ha hpa)
      (vector ρ ℓ s : Lp (Point n) 2 (cubePoint (n := n))),
      (vector ρ ℓ s : Lp (Point n) 2 cubePoint)⟫_ℝ =
      ∫ x, ρ ((coordinateEquiv n).symm x) * jacobianForm a (potential ρ ℓ s).val x ∂cube n := by
  have hf := (frequencySpace_properties s (potential ρ ℓ s).property).1
  rw [← gradient_potential ρ ℓ s]
  exact inner_jacobian_gradientVector ρ a ha hpa (potential ρ ℓ s).val hf

/-- The actual weighted drift-Jacobian integrals of the Galerkin potentials converge
 to the literal integral of the optimizer's `L²` vector field. -/
theorem potential_jacobianForm_tendsto (ρ : Point n →ᵇ ℝ)
    (ℓ : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)
    (a : Coordinates n → Coordinates n) (ha : ContDiff ℝ ∞ a)
    (hpa : ∀ i, Periodic (fun x => a x i))
    {c : ℝ} (hc : 0 < c) (hρ : ∀ᵐ y ∂cubePoint, c ≤ ρ y) :
    let U : Lp (Point n) 2 (cubePoint (n := n)) :=
      (optimizer ρ ℓ : gradientClosure (cubePoint (n := n)))
    Tendsto (fun s => ∫ x, ρ ((coordinateEquiv n).symm x) *
      jacobianForm a (potential ρ ℓ s).val x ∂cube n) atTop
      (𝓝 (∫ y, ρ y * ⟪fderiv ℝ (vectorPullback a) y (U y), U y⟫_ℝ ∂cubePoint)) := by
  dsimp only
  have hv := (gradientClosure (cubePoint (n := n))).subtypeL.continuous.continuousAt.tendsto.comp
    (vector_tendsto ρ ℓ hc hρ)
  have h := ((matrixOperator (jacobianCoefficient ρ a ha hpa)).continuous.continuousAt.tendsto.comp hv).inner
    (𝕜 := ℝ) hv
  simp only [Function.comp_apply, Submodule.subtypeL_apply] at h
  simp_rw [inner_jacobian_vector] at h
  rw [inner_jacobianCoefficient] at h
  exact h

/-- The same limit written entirely on the original fundamental cube. -/
theorem potential_jacobianForm_cube_tendsto (ρ : Point n →ᵇ ℝ)
    (ℓ : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)
    (a : Coordinates n → Coordinates n) (ha : ContDiff ℝ ∞ a)
    (hpa : ∀ i, Periodic (fun x => a x i))
    {c : ℝ} (hc : 0 < c) (hρ : ∀ᵐ y ∂cubePoint, c ≤ ρ y) :
    let U : Lp (Point n) 2 (cubePoint (n := n)) :=
      (optimizer ρ ℓ : gradientClosure (cubePoint (n := n)))
    Tendsto (fun s => ∫ x, ρ ((coordinateEquiv n).symm x) *
      jacobianForm a (potential ρ ℓ s).val x ∂cube n) atTop
      (𝓝 (∫ x, ρ ((coordinateEquiv n).symm x) *
        ⟪fderiv ℝ (vectorPullback a) ((coordinateEquiv n).symm x)
          (U ((coordinateEquiv n).symm x)), U ((coordinateEquiv n).symm x)⟫_ℝ ∂cube n)) := by
  simpa only [integral_cubePoint] using potential_jacobianForm_tendsto ρ ℓ a ha hpa hc hρ

/-- The genuine Jacobian operator-norm bound controls the limiting integral
with the same coefficient, without introducing a dimension factor. -/
theorem jacobian_integral_le (ρ : Point n →ᵇ ℝ)
    (a : Coordinates n → Coordinates n) (ha : ContDiff ℝ ∞ a)
    (hpa : ∀ i, Periodic (fun x => a x i))
    (u : gradientClosure (cubePoint (n := n))) {L : ℝ}
    (hρ : ∀ᵐ y ∂cubePoint, 0 ≤ ρ y)
    (hA : ∀ᵐ y ∂cubePoint, ‖fderiv ℝ (vectorPullback a) y‖ ≤ L) :
    (∫ y, ρ y * ⟪fderiv ℝ (vectorPullback a) y
      ((u : Lp (Point n) 2 cubePoint) y), (u : Lp (Point n) 2 cubePoint) y⟫_ℝ ∂cubePoint) ≤
      L * ∫ y, ρ y * ‖(u : Lp (Point n) 2 cubePoint) y‖ ^ 2 ∂cubePoint := by
  have hi := integrable_jacobian_inner ρ a ha hpa u u
  have hj : Integrable (fun y => ρ y * ‖(u : Lp (Point n) 2 cubePoint) y‖ ^ 2) cubePoint := by
    simpa only [real_inner_self_eq_norm_sq] using
      WeightedDensity.integrable_weighted_inner cubePoint ρ u u
  rw [← integral_const_mul]
  apply integral_mono_ae hi (hj.const_mul L)
  filter_upwards [hρ, hA] with y hy hAy
  calc
    _ ≤ ρ y * (L * ‖(u : Lp (Point n) 2 cubePoint) y‖ ^ 2) :=
      mul_le_mul_of_nonneg_left
        (DriftEnergyIdentity.jacobian_quadratic_le (fderiv ℝ (vectorPullback a) y) hAy _) hy
    _ = _ := by ring

/-- The limiting Jacobian term is bounded by the actual solved tangent energy. -/
theorem optimizer_jacobian_integral_le (ρ : Point n →ᵇ ℝ)
    (ℓ : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)
    (a : Coordinates n → Coordinates n) (ha : ContDiff ℝ ∞ a)
    (hpa : ∀ i, Periodic (fun x => a x i))
    {c L : ℝ} (hc : 0 < c) (hρ : ∀ᵐ y ∂cubePoint, c ≤ ρ y)
    (hA : ∀ᵐ y ∂cubePoint, ‖fderiv ℝ (vectorPullback a) y‖ ≤ L) :
    let U : Lp (Point n) 2 (cubePoint (n := n)) :=
      (optimizer ρ ℓ : gradientClosure (cubePoint (n := n)))
    (∫ y, ρ y * ⟪fderiv ℝ (vectorPullback a) y (U y), U y⟫_ℝ ∂cubePoint) ≤
      L * ℓ (optimizer ρ ℓ) := by
  dsimp only
  have hE := optimizer_equation ρ ℓ hc hρ (optimizer ρ ℓ)
  rw [WeightedDensity.weightedOperator_inner] at hE
  simp only [real_inner_self_eq_norm_sq] at hE
  rw [← hE]
  exact jacobian_integral_le ρ a ha hpa (optimizer ρ ℓ)
    (hρ.mono fun _ hy => hc.le.trans hy) hA

end SharpWasserstein.PeriodicJacobianLimit
