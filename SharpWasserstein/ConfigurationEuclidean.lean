module

public import SharpWasserstein.Compat
public import SharpWasserstein.Dynamics
public import SharpWasserstein.WeightedTangent
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-!
# Explicit Euclidean coordinates for particle configurations

The nested Pi configuration uses its ordinary sup norm. The map below is a
continuous linear equivalence, not a claimed isometry for that norm. Its
Euclidean target norm is proved equal to the manuscript's sum-of-squares cost.
Actual compact smooth tests and their Fréchet gradients are transported through
this equivalence, with exact coordinate derivative and energy identities.
-/

noncomputable section
namespace SharpWasserstein

open MeasureTheory Set
open scoped InnerProductSpace BigOperators Topology ContDiff

/-- Flatten particle and spatial coordinates into a genuine Euclidean space. -/
def configurationEuclidean (d N : ℕ) :
    Configuration d N ≃L[ℝ] WeightedTangent.Point (N * d) where
  toFun x := WithLp.toLp 2 (fun k =>
    x (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
  invFun y := fun i a => y (finProdFinEquiv (i, a))
  left_inv x := by
    ext i a
    change x (finProdFinEquiv.symm (finProdFinEquiv (i, a))).1
      (finProdFinEquiv.symm (finProdFinEquiv (i, a))).2 = x i a
    rw [Equiv.symm_apply_apply]
  right_inv y := by
    ext k
    change y (finProdFinEquiv (finProdFinEquiv.symm k)) = y k
    rw [Equiv.apply_symm_apply]
  map_add' x y := by rfl
  map_smul' c x := by rfl
  continuous_toFun := (PiLp.continuous_toLp 2 (fun _ : Fin (N * d) => ℝ)).comp (by fun_prop)
  continuous_invFun := by fun_prop

@[simp] theorem configurationEuclidean_apply_coordinate {d N : ℕ}
    (x : Configuration d N) (i : Fin N) (a : Fin d) :
    configurationEuclidean d N x (finProdFinEquiv (i, a)) = x i a := by
  change x (finProdFinEquiv.symm (finProdFinEquiv (i, a))).1
    (finProdFinEquiv.symm (finProdFinEquiv (i, a))).2 = x i a
  rw [Equiv.symm_apply_apply]

@[simp] theorem configurationEuclidean_symm_apply {d N : ℕ}
    (y : WeightedTangent.Point (N * d)) (i : Fin N) (a : Fin d) :
    (configurationEuclidean d N).symm y i a = y (finProdFinEquiv (i, a)) := rfl

/-- The target norm is exactly the unnormalized coordinate sum, with no dimension factor. -/
theorem configurationEuclidean_norm_sq {d N : ℕ} (x : Configuration d N) :
    ‖configurationEuclidean d N x‖ ^ 2 = ∑ i, ∑ a, (x i a) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    _ = ∑ p : Fin N × Fin d, (x p.1 p.2) ^ 2 := by
      symm
      apply Fintype.sum_equiv finProdFinEquiv
      intro p
      exact congrArg (fun r : ℝ => r ^ 2)
        (configurationEuclidean_apply_coordinate x p.1 p.2).symm
    _ = _ := Fintype.sum_prod_type _

/-- The actual quadratic transport cost is the Euclidean squared displacement. -/
theorem productCost_eq_configurationEuclidean_dist_sq {d N : ℕ} (x y : Configuration d N) :
    productCost x y = ‖configurationEuclidean d N x - configurationEuclidean d N y‖ ^ 2 := by
  rw [← map_sub, configurationEuclidean_norm_sq]
  rfl

/-- The scalar test expressed in flattened Euclidean coordinates. -/
def euclideanTest {d N : ℕ} (φ : Configuration d N → ℝ) : WeightedTangent.Point (N * d) → ℝ :=
  φ ∘ (configurationEuclidean d N).symm

@[simp] theorem euclideanTest_apply {d N : ℕ} (φ : Configuration d N → ℝ)
    (x : Configuration d N) : euclideanTest φ (configurationEuclidean d N x) = φ x := by
  simp [euclideanTest]

/-- Smooth compact tests remain smooth compact tests under the genuine coordinate map. -/
theorem smoothCompactTest_euclidean {d N : ℕ} {φ : Configuration d N → ℝ}
    (hφ : SmoothCompactTest φ) :
    ContDiff ℝ ∞ (euclideanTest φ) ∧ HasCompactSupport (euclideanTest φ) := by
  exact ⟨hφ.1.comp (configurationEuclidean d N).symm.contDiff,
    hφ.2.comp_homeomorph (configurationEuclidean d N).symm.toHomeomorph⟩

/-- Pulling back a Euclidean compact smooth test gives a test for the existing weak dynamics. -/
theorem smoothCompactTest_pullback {d N : ℕ} (ψ : WeightedTangent.Test (N * d)) :
    SmoothCompactTest ((ψ : WeightedTangent.Point (N * d) → ℝ) ∘ configurationEuclidean d N) := by
  exact ⟨ψ.property.1.comp (configurationEuclidean d N).contDiff,
    ψ.property.2.comp_homeomorph (configurationEuclidean d N).toHomeomorph⟩

/-- Genuine gradient pairing is exactly the Fréchet differential on the configuration space. -/
theorem euclideanTest_gradient_pairing {d N : ℕ} {φ : Configuration d N → ℝ}
    (x v : Configuration d N) :
    ⟪gradient (euclideanTest φ) (configurationEuclidean d N x),
      configurationEuclidean d N v⟫_ℝ = fderiv ℝ φ x v := by
  rw [inner_gradient_left]
  unfold euclideanTest
  rw [(configurationEuclidean d N).symm.comp_right_fderiv]
  simp

/-- Coordinate basis vectors map to the corresponding Euclidean orthonormal basis vectors. -/
theorem configurationEuclidean_coordinateVector {d N : ℕ} (i : Fin N) (a : Fin d) :
    configurationEuclidean d N (coordinateVector i a) =
      EuclideanSpace.single (finProdFinEquiv (i, a)) 1 := by
  classical
  ext k
  obtain ⟨⟨j, b⟩, rfl⟩ := finProdFinEquiv.surjective k
  simp [coordinateVector, EuclideanSpace.single, PiLp.single_apply, Prod.ext_iff]

/-- Every coordinate of the real Euclidean gradient is the coordinate derivative used by Dynamics. -/
theorem euclideanTest_gradient_coordinate {d N : ℕ} {φ : Configuration d N → ℝ}
    (x : Configuration d N) (i : Fin N) (a : Fin d) :
    gradient (euclideanTest φ) (configurationEuclidean d N x) (finProdFinEquiv (i, a)) =
      coordinateDerivative φ i a x := by
  have hp := euclideanTest_gradient_pairing (φ := φ) x (coordinateVector i a)
  rw [configurationEuclidean_coordinateVector, EuclideanSpace.inner_single_right] at hp
  simpa only [one_mul, conj_trivial, coordinateDerivative] using hp

/-- The gradient energy is precisely the coordinate derivative square sum in the manuscript. -/
theorem euclideanTest_gradient_norm_sq {d N : ℕ} {φ : Configuration d N → ℝ}
    (x : Configuration d N) :
    ‖gradient (euclideanTest φ) (configurationEuclidean d N x)‖ ^ 2 =
      ∑ i, ∑ a, (coordinateDerivative φ i a x) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    _ = ∑ p : Fin N × Fin d, (coordinateDerivative φ p.1 p.2 x) ^ 2 := by
      symm
      apply Fintype.sum_equiv finProdFinEquiv
      intro p
      rw [euclideanTest_gradient_coordinate]
    _ = _ := Fintype.sum_prod_type _

/-- The Fréchet differential is precisely the coordinate drift pairing used by the generator. -/
theorem fderiv_eq_sum_coordinateDerivative {d N : ℕ} (φ : Configuration d N → ℝ)
    (x v : Configuration d N) :
    fderiv ℝ φ x v = ∑ i, ∑ a, v i a * coordinateDerivative φ i a x := by
  rw [← euclideanTest_gradient_pairing, PiLp.inner_apply]
  calc
    _ = ∑ p : Fin N × Fin d, v p.1 p.2 * coordinateDerivative φ p.1 p.2 x := by
      symm
      apply Fintype.sum_equiv finProdFinEquiv
      intro p
      rw [RCLike.inner_apply, conj_trivial, configurationEuclidean_apply_coordinate,
        euclideanTest_gradient_coordinate]
    _ = _ := Fintype.sum_prod_type _

/-- The actual compact smooth test vector space used by the configuration dynamics. -/
def configurationTestSpace (d N : ℕ) : Submodule ℝ (Configuration d N → ℝ) where
  carrier := {φ | SmoothCompactTest φ}
  zero_mem' := ⟨contDiff_const, by simp [HasCompactSupport]⟩
  add_mem' := fun hφ hψ => ⟨hφ.1.add hψ.1, hφ.2.add hψ.2⟩
  smul_mem' := fun c φ hφ => ⟨hφ.1.const_smul c,
    hφ.2.comp_left (g := fun r : ℝ => c • r) (by simp)⟩

abbrev ConfigurationTest (d N : ℕ) := configurationTestSpace d N

/-- Compact smooth tests on the two coordinate presentations correspond linearly and bijectively. -/
def configurationTestEuclidean (d N : ℕ) :
    ConfigurationTest d N ≃ₗ[ℝ] WeightedTangent.Test (N * d) where
  toFun φ := ⟨euclideanTest φ.val, smoothCompactTest_euclidean φ.property⟩
  invFun ψ := ⟨ψ.val ∘ configurationEuclidean d N, smoothCompactTest_pullback ψ⟩
  left_inv φ := by
    apply Subtype.ext
    funext x
    exact euclideanTest_apply φ.val x
  right_inv ψ := by
    apply Subtype.ext
    funext y
    simp [euclideanTest, Function.comp_def]
  map_add' φ ψ := by rfl
  map_smul' c φ := by rfl

/-- The same distribution in genuine Euclidean coordinates. -/
def euclideanDistribution {d N : ℕ} (σ : ConfigurationTest d N →ₗ[ℝ] ℝ) :
    WeightedTangent.Test (N * d) →ₗ[ℝ] ℝ :=
  σ.comp (configurationTestEuclidean d N).symm.toLinearMap

@[simp] theorem euclideanDistribution_test {d N : ℕ}
    (σ : ConfigurationTest d N →ₗ[ℝ] ℝ) (φ : ConfigurationTest d N) :
    euclideanDistribution σ (configurationTestEuclidean d N φ) = σ φ := by
  simp [euclideanDistribution]

variable {d N : ℕ} [MeasurableSpace (WeightedTangent.Point (N * d))]
  [BorelSpace (WeightedTangent.Point (N * d))]

/-- Push the actual law through the explicit coordinate equivalence. -/
def euclideanLaw (μ : Measure (Configuration d N)) : Measure (WeightedTangent.Point (N * d)) :=
  Measure.map (configurationEuclidean d N) μ

instance euclideanLaw_isFiniteMeasure (μ : Measure (Configuration d N)) [IsFiniteMeasure μ] :
    IsFiniteMeasure (euclideanLaw μ) := by
  unfold euclideanLaw
  infer_instance

instance euclideanLaw_isProbabilityMeasure (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (euclideanLaw μ) :=
  Measure.isProbabilityMeasure_map (configurationEuclidean d N).continuous.measurable.aemeasurable

/-- Change of variables is exact for arbitrary real integrands under this measurable equivalence. -/
theorem integral_euclideanLaw (μ : Measure (Configuration d N))
    (f : WeightedTangent.Point (N * d) → ℝ) :
    (∫ y, f y ∂euclideanLaw μ) = ∫ x, f (configurationEuclidean d N x) ∂μ :=
  integral_map_equiv (configurationEuclidean d N).toHomeomorph.toMeasurableEquiv f

/-- The squared-gradient integral agrees with the actual configuration-coordinate expression. -/
theorem gradient_integral_euclideanLaw (μ : Measure (Configuration d N))
    (φ : Configuration d N → ℝ) :
    (∫ y, ‖gradient (euclideanTest φ) y‖ ^ 2 ∂euclideanLaw μ) =
      ∫ x, ∑ i, ∑ a, (coordinateDerivative φ i a x) ^ 2 ∂μ := by
  rw [integral_euclideanLaw]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => euclideanTest_gradient_norm_sq x)

/-- The compact-test objective expressed entirely in the coordinates used by Dynamics. -/
def configurationTestObjective (μ : Measure (Configuration d N))
    (σ : ConfigurationTest d N →ₗ[ℝ] ℝ) (φ : ConfigurationTest d N) : ℝ :=
  2 * σ φ - ∫ x, ∑ i, ∑ a, (coordinateDerivative φ.val i a x) ^ 2 ∂μ

/-- The variational tangent energy on the existing configuration type. -/
def configurationTangentEnergy (μ : Measure (Configuration d N))
    (σ : ConfigurationTest d N →ₗ[ℝ] ℝ) : ℝ := sSup (Set.range (configurationTestObjective μ σ))

/-- A genuine finite variational bound in configuration coordinates. -/
def ConfigurationFiniteEnergy (μ : Measure (Configuration d N))
    (σ : ConfigurationTest d N →ₗ[ℝ] ℝ) : Prop := BddAbove (Set.range (configurationTestObjective μ σ))

/-- Transporting coordinates preserves each actual variational test, not only a norm estimate. -/
theorem configurationTestObjective_eq_euclidean (μ : Measure (Configuration d N))
    (σ : ConfigurationTest d N →ₗ[ℝ] ℝ) (φ : ConfigurationTest d N) :
    configurationTestObjective μ σ φ = WeightedTangent.testObjective (euclideanLaw μ)
      (euclideanDistribution σ) (configurationTestEuclidean d N φ) := by
  unfold configurationTestObjective WeightedTangent.testObjective
  rw [euclideanDistribution_test]
  congr 1
  exact (gradient_integral_euclideanLaw μ φ.val).symm

/-- The two variational problems have identical sets of objective values. -/
theorem configurationTestObjective_range_eq (μ : Measure (Configuration d N))
    (σ : ConfigurationTest d N →ₗ[ℝ] ℝ) :
    Set.range (configurationTestObjective μ σ) =
      Set.range (WeightedTangent.testObjective (euclideanLaw μ) (euclideanDistribution σ)) := by
  ext r
  constructor
  · rintro ⟨φ, rfl⟩
    exact ⟨configurationTestEuclidean d N φ, (configurationTestObjective_eq_euclidean μ σ φ).symm⟩
  · rintro ⟨ψ, rfl⟩
    refine ⟨(configurationTestEuclidean d N).symm ψ, ?_⟩
    rw [configurationTestObjective_eq_euclidean, LinearEquiv.apply_symm_apply]

/-- Finite configuration energy is precisely finite energy in the constructed weighted Hilbert space. -/
theorem configurationFiniteEnergy_iff (μ : Measure (Configuration d N))
    (σ : ConfigurationTest d N →ₗ[ℝ] ℝ) :
    ConfigurationFiniteEnergy μ σ ↔
      WeightedTangent.FiniteEnergy (euclideanLaw μ) (euclideanDistribution σ) := by
  unfold ConfigurationFiniteEnergy WeightedTangent.FiniteEnergy
  rw [configurationTestObjective_range_eq]

/-- The numerical tangent energies are identical under the coordinate map. -/
theorem configurationTangentEnergy_eq (μ : Measure (Configuration d N))
    (σ : ConfigurationTest d N →ₗ[ℝ] ℝ) :
    configurationTangentEnergy μ σ =
      WeightedTangent.energy (euclideanLaw μ) (euclideanDistribution σ) := by
  unfold configurationTangentEnergy WeightedTangent.energy
  rw [configurationTestObjective_range_eq]

/-- The actual minimal tangent vector field, returned in the coordinates used by Dynamics. -/
def configurationTangent (μ : Measure (Configuration d N)) [IsFiniteMeasure μ]
    (σ : ConfigurationTest d N →ₗ[ℝ] ℝ) (x : Configuration d N) : Configuration d N :=
  (configurationEuclidean d N).symm
    ((WeightedTangent.representative (euclideanLaw μ) (euclideanDistribution σ) :
      Lp (WeightedTangent.Point (N * d)) 2 (euclideanLaw μ)) (configurationEuclidean d N x))

/-- The pulled-back representative has precisely the pointwise Euclidean energy density. -/
theorem configurationTangent_pointwise_energy (μ : Measure (Configuration d N)) [IsFiniteMeasure μ]
    (σ : ConfigurationTest d N →ₗ[ℝ] ℝ) (x : Configuration d N) :
    productCost (configurationTangent μ σ x) 0 =
      ‖(WeightedTangent.representative (euclideanLaw μ) (euclideanDistribution σ) :
        Lp (WeightedTangent.Point (N * d)) 2 (euclideanLaw μ)) (configurationEuclidean d N x)‖ ^ 2 := by
  rw [productCost_eq_configurationEuclidean_dist_sq]
  simp [configurationTangent]

/-- The pulled-back representative gives the exact coordinate distributional divergence. -/
theorem configurationTangent_divergence (μ : Measure (Configuration d N)) [IsFiniteMeasure μ]
    (σ : ConfigurationTest d N →ₗ[ℝ] ℝ) (h : ConfigurationFiniteEnergy μ σ)
    (φ : ConfigurationTest d N) :
    σ φ = ∫ x, ∑ i, ∑ a, configurationTangent μ σ x i a * coordinateDerivative φ.val i a x ∂μ := by
  have hp := WeightedTangent.representative_divergence (euclideanLaw μ) (euclideanDistribution σ)
    ((configurationFiniteEnergy_iff μ σ).mp h) (configurationTestEuclidean d N φ)
  rw [euclideanDistribution_test, integral_euclideanLaw] at hp
  calc
    σ φ = _ := hp
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      change ⟪gradient (euclideanTest φ.val) (configurationEuclidean d N x),
        (WeightedTangent.representative (euclideanLaw μ) (euclideanDistribution σ) :
          Lp (WeightedTangent.Point (N * d)) 2 (euclideanLaw μ)) (configurationEuclidean d N x)⟫_ℝ = _
      have he := euclideanTest_gradient_pairing (φ := φ.val) x (configurationTangent μ σ x)
      simpa only [configurationTangent, ContinuousLinearEquiv.apply_symm_apply,
        fderiv_eq_sum_coordinateDerivative] using he

/-- No energy factor is lost when returning the minimal tangent to the original coordinates. -/
theorem configurationTangent_energy (μ : Measure (Configuration d N)) [IsFiniteMeasure μ]
    (σ : ConfigurationTest d N →ₗ[ℝ] ℝ) (h : ConfigurationFiniteEnergy μ σ) :
    configurationTangentEnergy μ σ = ∫ x, productCost (configurationTangent μ σ x) 0 ∂μ := by
  rw [configurationTangentEnergy_eq, WeightedTangent.energy_eq_integral _ _
    ((configurationFiniteEnergy_iff μ σ).mp h), integral_euclideanLaw]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x =>
    (configurationTangent_pointwise_energy μ σ x).symm)

/-- The actual configuration tangent's quadratic energy density is integrable. -/
theorem configurationTangent_energy_integrable (μ : Measure (Configuration d N)) [IsFiniteMeasure μ]
    (σ : ConfigurationTest d N →ₗ[ℝ] ℝ) :
    Integrable (fun x => productCost (configurationTangent μ σ x) 0) μ := by
  let v : Lp (WeightedTangent.Point (N * d)) 2 (euclideanLaw μ) :=
    WeightedTangent.representative (euclideanLaw μ) (euclideanDistribution σ)
  have hv : Integrable (fun y => ‖v y‖ ^ 2) (euclideanLaw μ) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).mp (Lp.memLp v)
  have hc := hv.comp_measurable (configurationEuclidean d N).continuous.measurable
  apply hc.congr
  filter_upwards [] with x
  exact (configurationTangent_pointwise_energy μ σ x).symm

/-- The actual generator-coordinate test pairing is integrable. -/
theorem configurationTangent_pairing_integrable (μ : Measure (Configuration d N)) [IsFiniteMeasure μ]
    (σ : ConfigurationTest d N →ₗ[ℝ] ℝ) (φ : ConfigurationTest d N) :
    Integrable (fun x => ∑ i, ∑ a,
      configurationTangent μ σ x i a * coordinateDerivative φ.val i a x) μ := by
  let v : Lp (WeightedTangent.Point (N * d)) 2 (euclideanLaw μ) :=
    WeightedTangent.representative (euclideanLaw μ) (euclideanDistribution σ)
  have hv := WeightedTangent.integrable_gradient_pairing (euclideanLaw μ) v
    (configurationTestEuclidean d N φ)
  have hc := hv.comp_measurable (configurationEuclidean d N).continuous.measurable
  apply hc.congr
  filter_upwards [] with x
  change ⟪gradient (euclideanTest φ.val) (configurationEuclidean d N x),
    (WeightedTangent.representative (euclideanLaw μ) (euclideanDistribution σ) :
      Lp (WeightedTangent.Point (N * d)) 2 (euclideanLaw μ)) (configurationEuclidean d N x)⟫_ℝ = _
  have he := euclideanTest_gradient_pairing (φ := φ.val) x (configurationTangent μ σ x)
  simpa only [configurationTangent, ContinuousLinearEquiv.apply_symm_apply,
    fderiv_eq_sum_coordinateDerivative] using he

/-- The pulled-back tangent is an actual almost-everywhere strongly measurable vector field. -/
theorem configurationTangent_aestronglyMeasurable (μ : Measure (Configuration d N)) [IsFiniteMeasure μ]
    (σ : ConfigurationTest d N →ₗ[ℝ] ℝ) :
    AEStronglyMeasurable (configurationTangent μ σ) μ := by
  let v : Lp (WeightedTangent.Point (N * d)) 2 (euclideanLaw μ) :=
    WeightedTangent.representative (euclideanLaw μ) (euclideanDistribution σ)
  have hv := (Lp.aestronglyMeasurable v).comp_measurable
    (configurationEuclidean d N).continuous.measurable
  exact (configurationEuclidean d N).symm.continuous.comp_aestronglyMeasurable hv

/-- The tangent existence/energy theorem directly on the existing particle configuration type. -/
theorem exists_configurationTangent (μ : Measure (Configuration d N)) [IsFiniteMeasure μ]
    (σ : ConfigurationTest d N →ₗ[ℝ] ℝ) (h : ConfigurationFiniteEnergy μ σ) :
    ∃ v : Configuration d N → Configuration d N,
      AEStronglyMeasurable v μ ∧
      Integrable (fun x => productCost (v x) 0) μ ∧
      (∀ φ : ConfigurationTest d N,
        Integrable (fun x => ∑ i, ∑ a, v x i a * coordinateDerivative φ.val i a x) μ ∧
        σ φ = ∫ x, ∑ i, ∑ a, v x i a * coordinateDerivative φ.val i a x ∂μ) ∧
      configurationTangentEnergy μ σ = ∫ x, productCost (v x) 0 ∂μ := by
  refine ⟨configurationTangent μ σ, configurationTangent_aestronglyMeasurable μ σ,
    configurationTangent_energy_integrable μ σ, ?_, configurationTangent_energy μ σ h⟩
  intro φ
  exact ⟨configurationTangent_pairing_integrable μ σ φ, configurationTangent_divergence μ σ h φ⟩

end SharpWasserstein
