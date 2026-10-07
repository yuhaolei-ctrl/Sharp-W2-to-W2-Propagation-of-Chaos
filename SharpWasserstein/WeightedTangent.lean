module

public import SharpWasserstein.Compat
public import SharpWasserstein.DenseVariational
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Tactic.FunProp

@[expose] public section

/-!
# Weighted negative-Sobolev tangents on Euclidean space

The test space here consists of actual compactly supported smooth scalar
functions on a Euclidean space. Its derivative is the actual Fréchet gradient,
viewed in `L²(μ)`, and the tangent space is the closure of these gradients.
The representing vector's pairing is an actual weighted Lebesgue integral.
-/

noncomputable section

namespace SharpWasserstein.WeightedTangent

open MeasureTheory Set
open scoped InnerProductSpace Topology ContDiff

abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The vector space `C_c^∞` of compactly supported smooth test functions. -/
def testSpace (d : ℕ) : Submodule ℝ (Point d → ℝ) where
  carrier := {φ | ContDiff ℝ ∞ φ ∧ HasCompactSupport φ}
  zero_mem' := ⟨contDiff_const, by simp [HasCompactSupport]⟩
  add_mem' := fun hφ hψ => ⟨hφ.1.add hψ.1, hφ.2.add hψ.2⟩
  smul_mem' := fun c φ hφ => ⟨hφ.1.const_smul c,
    hφ.2.comp_left (g := fun r : ℝ => c • r) (by simp)⟩

abbrev Test (d : ℕ) := testSpace d

variable {d : ℕ}

/-- Smooth compact tests have genuine differentiable representatives. -/
theorem test_differentiable (φ : Test d) : Differentiable ℝ (φ : Point d → ℝ) :=
  φ.property.1.differentiable (by simp)

/-- The gradient is continuous, with no assumption on the probability weight. -/
theorem continuous_test_gradient (φ : Test d) : Continuous (gradient (φ : Point d → ℝ)) := by
  exact (InnerProductSpace.toDual ℝ (Point d)).symm.continuous.comp
    (φ.property.1.continuous_fderiv (by simp))

/-- Compact support of a test passes to its actual gradient. -/
theorem compactSupport_test_gradient (φ : Test d) :
    HasCompactSupport (gradient (φ : Point d → ℝ)) := by
  exact (φ.property.2.fderiv ℝ).comp_left
    (g := (InnerProductSpace.toDual ℝ (Point d)).symm) (by simp)

variable [MeasurableSpace (Point d)] [BorelSpace (Point d)]
variable (μ : Measure (Point d)) [IsFiniteMeasure μ]

/-- Compact smooth gradients belong to weighted `L²`, including for singular weights. -/
theorem test_gradient_memLp (φ : Test d) :
    MemLp (gradient (φ : Point d → ℝ)) 2 μ :=
  (continuous_test_gradient φ).memLp_of_hasCompactSupport (compactSupport_test_gradient φ)

/-- The squared gradient energy is an integrable function, so its integral is not totalized. -/
theorem integrable_test_gradient_sq (φ : Test d) :
    Integrable (fun x => ‖gradient (φ : Point d → ℝ) x‖ ^ 2) μ :=
  (memLp_two_iff_integrable_sq_norm (test_gradient_memLp μ φ).aestronglyMeasurable).mp
    (test_gradient_memLp μ φ)

/-- The actual test gradient as an equivalence class in weighted `L²`. -/
def testGradient (φ : Test d) : Lp (Point d) 2 μ :=
  (test_gradient_memLp μ φ).toLp (gradient (φ : Point d → ℝ))

theorem testGradient_ae (φ : Test d) :
    testGradient μ φ =ᵐ[μ] gradient (φ : Point d → ℝ) :=
  (test_gradient_memLp μ φ).coeFn_toLp

omit [MeasurableSpace (Point d)] [BorelSpace (Point d)] in
theorem gradient_test_add (φ ψ : Test d) :
    gradient ((φ + ψ : Test d) : Point d → ℝ) =
      gradient (φ : Point d → ℝ) + gradient (ψ : Point d → ℝ) := by
  funext x
  change (InnerProductSpace.toDual ℝ (Point d)).symm
      (fderiv ℝ ((φ : Point d → ℝ) + (ψ : Point d → ℝ)) x) = _
  rw [fderiv_add (test_differentiable φ x) (test_differentiable ψ x), map_add]
  rfl

omit [MeasurableSpace (Point d)] [BorelSpace (Point d)] in
theorem gradient_test_smul (c : ℝ) (φ : Test d) :
    gradient ((c • φ : Test d) : Point d → ℝ) =
      c • gradient (φ : Point d → ℝ) := by
  funext x
  change (InnerProductSpace.toDual ℝ (Point d)).symm
      (fderiv ℝ (c • (φ : Point d → ℝ)) x) = _
  rw [fderiv_const_smul (test_differentiable φ x)]
  simp [gradient]

/-- The gradient map is linear as a map into the genuine weighted `L²` space. -/
def testGradientLinear : Test d →ₗ[ℝ] Lp (Point d) 2 μ where
  toFun := testGradient μ
  map_add' φ ψ := by
    apply Lp.ext
    filter_upwards [testGradient_ae μ (φ + ψ),
      Lp.coeFn_add (testGradient μ φ) (testGradient μ ψ),
      testGradient_ae μ φ, testGradient_ae μ ψ] with x ha hb hc hd
    rw [ha, hb]
    simp only [Pi.add_apply, hc, hd]
    exact congrFun (gradient_test_add φ ψ) x
  map_smul' c φ := by
    apply Lp.ext
    filter_upwards [testGradient_ae μ (c • φ),
      Lp.coeFn_smul c (testGradient μ φ), testGradient_ae μ φ] with x ha hb hc
    simp only [RingHom.id_apply]
    rw [ha, hb]
    simp only [Pi.smul_apply, hc]
    exact congrFun (gradient_test_smul c φ) x

/-- Closure of the actual compact smooth gradients in weighted `L²`. -/
def gradientClosure : Submodule ℝ (Lp (Point d) 2 μ) :=
  (testGradientLinear μ).range.topologicalClosure

instance gradientClosure_completeSpace : CompleteSpace (gradientClosure μ) := by
  unfold gradientClosure
  infer_instance

/-- Shortcut instance: lets instance search see the normed structure of `gradientClosure μ`
directly when it is the ambient space of a further submodule. -/
instance (priority := 10) gradientClosure_normedAddCommGroup : NormedAddCommGroup (gradientClosure μ) :=
  Submodule.normedAddCommGroup _

/-- Shortcut instance, see `gradientClosure_normedAddCommGroup`. -/
instance (priority := 10) gradientClosure_innerProductSpace : InnerProductSpace ℝ (gradientClosure μ) :=
  Submodule.innerProductSpace _

/-- The test gradient regarded as a vector in its closed tangent space. -/
def gradientIntoClosure : Test d →ₗ[ℝ] gradientClosure μ :=
  (testGradientLinear μ).codRestrict (gradientClosure μ)
    (fun φ => (testGradientLinear μ).range.le_topologicalClosure
      (LinearMap.mem_range_self _ φ))

/-- This definition really is the gradient closure: test gradients are dense in it. -/
theorem dense_gradientIntoClosure : DenseRange (gradientIntoClosure μ) := by
  rw [DenseRange, Subtype.dense_iff]
  intro v hv
  change v ∈ closure (Set.range (testGradientLinear μ)) at hv
  convert hv using 1
  congr 1
  ext w
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨z, ⟨φ, rfl⟩, rfl⟩
    exact ⟨φ, rfl⟩
  · rintro ⟨φ, rfl⟩
    exact ⟨gradientIntoClosure μ φ, ⟨φ, rfl⟩, rfl⟩

/-- The squared gradient norm is precisely its weighted integral. -/
theorem testGradient_norm_sq (φ : Test d) :
    ‖testGradient μ φ‖ ^ 2 = ∫ x, ‖gradient (φ : Point d → ℝ) x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [testGradient_ae μ φ] with x hx
  rw [hx, real_inner_self_eq_norm_sq]


/-- The manuscript's actual compact-test variational objective. -/
def testObjective (σ : Test d →ₗ[ℝ] ℝ) (φ : Test d) : ℝ :=
  2 * σ φ - ∫ x, ‖gradient (φ : Point d → ℝ) x‖ ^ 2 ∂μ

/-- Weighted negative-Sobolev energy, as a supremum over actual smooth compact tests. -/
def energy (σ : Test d →ₗ[ℝ] ℝ) : ℝ := sSup (Set.range (testObjective μ σ))

/-- Finiteness means boundedness of the objective; this does not use totalized real `sSup`. -/
def FiniteEnergy (σ : Test d →ₗ[ℝ] ℝ) : Prop :=
  BddAbove (Set.range (testObjective μ σ))

theorem testObjective_eq_dense (σ : Test d →ₗ[ℝ] ℝ) (φ : Test d) :
    testObjective μ σ φ = DenseVariational.objective σ (gradientIntoClosure μ) φ := by
  unfold testObjective DenseVariational.objective
  change 2 * σ φ - _ = 2 * σ φ - ‖testGradient μ φ‖ ^ 2
  rw [testGradient_norm_sq]

theorem finiteEnergy_dense (σ : Test d →ₗ[ℝ] ℝ) (h : FiniteEnergy μ σ) :
    BddAbove (Set.range (DenseVariational.objective σ (gradientIntoClosure μ))) := by
  rw [← funext (testObjective_eq_dense μ σ)]
  exact h

/-- The actual minimal weighted tangent belongs to the closed gradient space. -/
def representative (σ : Test d →ₗ[ℝ] ℝ) : gradientClosure μ :=
  DenseVariational.representative σ (gradientIntoClosure μ)

/-- Every test/flux pairing is integrable, including for a singular finite weight. -/
theorem integrable_gradient_pairing (v : Lp (Point d) 2 μ) (φ : Test d) :
    Integrable (fun x => ⟪gradient (φ : Point d → ℝ) x, v x⟫_ℝ) μ := by
  apply (L2.integrable_inner (𝕜 := ℝ) (testGradient μ φ) v).congr
  filter_upwards [testGradient_ae μ φ] with x hx
  rw [hx]

/-- The Hilbert inner product here is the weighted integral of the real test gradient. -/
theorem gradient_pairing_eq_inner (v : Lp (Point d) 2 μ) (φ : Test d) :
    (∫ x, ⟪gradient (φ : Point d → ℝ) x, v x⟫_ℝ ∂μ) =
      ⟪testGradient μ φ, v⟫_ℝ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [testGradient_ae μ φ] with x hx
  rw [hx]

/-- The distributional identity `σ = -div(μ v)`, tested against every `C_c^∞` function. -/
theorem representative_divergence (σ : Test d →ₗ[ℝ] ℝ) (h : FiniteEnergy μ σ)
    (φ : Test d) :
    σ φ = ∫ x, ⟪gradient (φ : Point d → ℝ) x,
      (representative μ σ : Lp (Point d) 2 μ) x⟫_ℝ ∂μ := by
  rw [gradient_pairing_eq_inner]
  have hp := DenseVariational.representative_pairing σ (gradientIntoClosure μ)
    (dense_gradientIntoClosure μ) (finiteEnergy_dense μ σ h) φ
  change ⟪(representative μ σ : Lp (Point d) 2 μ), testGradient μ φ⟫_ℝ = σ φ at hp
  rw [real_inner_comm] at hp
  exact hp.symm

/-- The representing tangent is unique within the actual closed gradient space. -/
theorem representative_unique (σ : Test d →ₗ[ℝ] ℝ) (h : FiniteEnergy μ σ)
    (v : gradientClosure μ)
    (hv : ∀ φ : Test d, σ φ = ∫ x,
      ⟪gradient (φ : Point d → ℝ) x, (v : Lp (Point d) 2 μ) x⟫_ℝ ∂μ) :
    v = representative μ σ := by
  apply DenseVariational.representative_unique σ (gradientIntoClosure μ)
    (dense_gradientIntoClosure μ) (finiteEnergy_dense μ σ h)
  intro φ
  have hp := hv φ
  rw [gradient_pairing_eq_inner] at hp
  change ⟪(v : Lp (Point d) 2 μ), testGradient μ φ⟫_ℝ = σ φ
  rw [real_inner_comm]
  exact hp.symm

/-- Exact energy equality: the original test supremum is the squared `L²(μ)` norm. -/
theorem energy_eq_norm_sq (σ : Test d →ₗ[ℝ] ℝ) (h : FiniteEnergy μ σ) :
    energy μ σ = ‖representative μ σ‖ ^ 2 := by
  unfold energy
  rw [funext (testObjective_eq_dense μ σ)]
  exact DenseVariational.energy_eq_norm_sq σ (gradientIntoClosure μ)
    (dense_gradientIntoClosure μ) (finiteEnergy_dense μ σ h)

omit [BorelSpace (Point d)] [IsFiniteMeasure μ] in
/-- A weighted `L²` norm is the actual integral of the squared pointwise Euclidean norm. -/
theorem lp_norm_sq_eq_integral (v : Lp (Point d) 2 μ) :
    ‖v‖ ^ 2 = ∫ x, ‖v x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp_rw [real_inner_self_eq_norm_sq]

/-- The precise integral energy identity from the manuscript's tangent lemma. -/
theorem energy_eq_integral (σ : Test d →ₗ[ℝ] ℝ) (h : FiniteEnergy μ σ) :
    energy μ σ = ∫ x, ‖(representative μ σ : Lp (Point d) 2 μ) x‖ ^ 2 ∂μ := by
  rw [energy_eq_norm_sq μ σ h]
  exact lp_norm_sq_eq_integral μ (representative μ σ : Lp (Point d) 2 μ)

/-- Full existence and uniqueness, stated directly with compact tests and weighted integrals. -/
theorem existsUnique_tangent (σ : Test d →ₗ[ℝ] ℝ) (h : FiniteEnergy μ σ) :
    ∃! v : gradientClosure μ, ∀ φ : Test d,
      σ φ = ∫ x, ⟪gradient (φ : Point d → ℝ) x, (v : Lp (Point d) 2 μ) x⟫_ℝ ∂μ := by
  exact ⟨representative μ σ, representative_divergence μ σ h,
    fun v hv => representative_unique μ σ h v hv⟩

/-- Every weighted `L²` flux defines a genuine linear distribution on compact smooth tests. -/
def fluxFunctional (v : Lp (Point d) 2 μ) : Test d →ₗ[ℝ] ℝ :=
  (innerₗ (Lp (Point d) 2 μ) v).comp (testGradientLinear μ)

theorem fluxFunctional_apply (v : Lp (Point d) 2 μ) (φ : Test d) :
    fluxFunctional μ v φ = ∫ x, ⟪gradient (φ : Point d → ℝ) x, v x⟫_ℝ ∂μ := by
  rw [gradient_pairing_eq_inner]
  change ⟪v, testGradient μ φ⟫_ℝ = _
  exact real_inner_comm _ _

/-- Any representing `L²` flux bounds the test objective by its actual energy. -/
theorem testObjective_le_flux_norm_sq (σ : Test d →ₗ[ℝ] ℝ)
    (v : Lp (Point d) 2 μ)
    (hv : ∀ φ : Test d, σ φ = ∫ x, ⟪gradient (φ : Point d → ℝ) x, v x⟫_ℝ ∂μ)
    (φ : Test d) : testObjective μ σ φ ≤ ‖v‖ ^ 2 := by
  unfold testObjective
  rw [hv φ, gradient_pairing_eq_inner, ← testGradient_norm_sq]
  nlinarith [norm_sub_sq_real (testGradient μ φ) v, sq_nonneg ‖testGradient μ φ - v‖]

/-- Finite flux energy suffices for finite negative-Sobolev energy. -/
theorem finiteEnergy_of_divergence (σ : Test d →ₗ[ℝ] ℝ)
    (v : Lp (Point d) 2 μ)
    (hv : ∀ φ : Test d, σ φ = ∫ x, ⟪gradient (φ : Point d → ℝ) x, v x⟫_ℝ ∂μ) :
    FiniteEnergy μ σ := by
  refine ⟨‖v‖ ^ 2, ?_⟩
  rintro y ⟨φ, rfl⟩
  exact testObjective_le_flux_norm_sq μ σ v hv φ

/-- The minimum-energy inequality uses the integral of an arbitrary representing flux. -/
theorem energy_le_flux_integral (σ : Test d →ₗ[ℝ] ℝ)
    (v : Lp (Point d) 2 μ)
    (hv : ∀ φ : Test d, σ φ = ∫ x, ⟪gradient (φ : Point d → ℝ) x, v x⟫_ℝ ∂μ) :
    energy μ σ ≤ ∫ x, ‖v x‖ ^ 2 ∂μ := by
  rw [← lp_norm_sq_eq_integral]
  apply csSup_le (Set.range_nonempty _)
  rintro y ⟨φ, rfl⟩
  exact testObjective_le_flux_norm_sq μ σ v hv φ

/-- An arbitrary flux differs from the gradient representative by an orthogonal vector. -/
theorem flux_residual_orthogonal (σ : Test d →ₗ[ℝ] ℝ)
    (v : Lp (Point d) 2 μ)
    (hv : ∀ φ : Test d, σ φ = ∫ x, ⟪gradient (φ : Point d → ℝ) x, v x⟫_ℝ ∂μ)
    (w : gradientClosure μ) :
    ⟪v - (representative μ σ : Lp (Point d) 2 μ), (w : Lp (Point d) 2 μ)⟫_ℝ = 0 := by
  refine (dense_gradientIntoClosure μ).induction_on w
    (isClosed_eq (by fun_prop) continuous_const) ?_
  intro φ
  change ⟪v - (representative μ σ : Lp (Point d) 2 μ), testGradient μ φ⟫_ℝ = 0
  have hp := hv φ
  have hr := representative_divergence μ σ (finiteEnergy_of_divergence μ σ v hv) φ
  rw [gradient_pairing_eq_inner] at hp hr
  rw [inner_sub_left, real_inner_comm (testGradient μ φ) v,
    real_inner_comm (testGradient μ φ) (representative μ σ : Lp (Point d) 2 μ)]
  rw [← hp, ← hr, sub_self]

/-- The exact weighted Pythagorean identity strengthens minimality to an energy gap. -/
theorem flux_energy_decomposition (σ : Test d →ₗ[ℝ] ℝ)
    (v : Lp (Point d) 2 μ)
    (hv : ∀ φ : Test d, σ φ = ∫ x, ⟪gradient (φ : Point d → ℝ) x, v x⟫_ℝ ∂μ) :
    (∫ x, ‖v x‖ ^ 2 ∂μ) = energy μ σ +
      ‖v - (representative μ σ : Lp (Point d) 2 μ)‖ ^ 2 := by
  rw [← lp_norm_sq_eq_integral, energy_eq_norm_sq μ σ (finiteEnergy_of_divergence μ σ v hv)]
  have hp := flux_residual_orthogonal μ σ v hv (representative μ σ)
  rw [inner_sub_left, real_inner_self_eq_norm_sq] at hp
  have hn := norm_sub_sq_real v (representative μ σ : Lp (Point d) 2 μ)
  change ‖v‖ ^ 2 = ‖(representative μ σ : Lp (Point d) 2 μ)‖ ^ 2 + _
  nlinarith

/-- Finite energy is equivalent to existence of a genuine weighted `L²` divergence flux. -/
theorem finiteEnergy_iff_exists_flux (σ : Test d →ₗ[ℝ] ℝ) :
    FiniteEnergy μ σ ↔ ∃ v : Lp (Point d) 2 μ, ∀ φ : Test d,
      σ φ = ∫ x, ⟪gradient (φ : Point d → ℝ) x, v x⟫_ℝ ∂μ := by
  constructor
  · intro h
    exact ⟨representative μ σ, representative_divergence μ σ h⟩
  · rintro ⟨v, hv⟩
    exact finiteEnergy_of_divergence μ σ v hv

end SharpWasserstein.WeightedTangent
