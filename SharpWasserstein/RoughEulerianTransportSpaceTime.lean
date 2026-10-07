module

public import SharpWasserstein.Compat
public import SharpWasserstein.WeightedTangent
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

@[expose] public section

/-! An actual space-time L² flux from scalar distribution pairings. The construction
uses one Riesz theorem in the joint measure, with no measurable choice of a
separate canonical representative at each time. -/
noncomputable section
set_option maxHeartbeats 400000

open MeasureTheory ProbabilityTheory Set
open scoped InnerProductSpace ENNReal ProbabilityTheory
namespace SharpWasserstein.RoughEulerianTransport
open WeightedTangent
variable {α : Type*} [MeasurableSpace α] {d : ℕ}
  [MeasurableSpace (Point d)] [BorelSpace (Point d)]
  (ν : Measure α) [IsFiniteMeasure ν] (κ : Kernel α (Point d)) [IsMarkovKernel κ]
  (σ : α → Test d →ₗ[ℝ] ℝ)

/-- Actual spatial gradient of a time-dependent compact test. -/
def fieldGradient (φ : α → Test d) (z : α × Point d) : Point d :=
  gradient (φ z.1 : Point d → ℝ) z.2

omit [MeasurableSpace α] [MeasurableSpace (Point d)] [BorelSpace (Point d)] in
@[simp] theorem fieldGradient_add (φ ψ : α → Test d) :
    fieldGradient (φ + ψ) = fieldGradient φ + fieldGradient ψ := by
  funext z
  exact congrFun (gradient_test_add (φ z.1) (ψ z.1)) z.2

omit [MeasurableSpace α] [MeasurableSpace (Point d)] [BorelSpace (Point d)] in
@[simp] theorem fieldGradient_smul (c : ℝ) (φ : α → Test d) :
    fieldGradient (c • φ) = c • fieldGradient φ := by
  funext z
  exact congrFun (gradient_test_smul c (φ z.1)) z.2

omit [MeasurableSpace α] [MeasurableSpace (Point d)] [BorelSpace (Point d)] in
@[simp] theorem fieldGradient_zero : fieldGradient (0 : α → Test d) = 0 := by
  funext z
  simp [fieldGradient, gradient]

/-- Admissible test fields: genuine joint L² gradients and integrable scalar action.
These are properties of tests, not assumptions about a representing flux. -/
def fieldSpace : Submodule ℝ (α → Test d) where
  carrier := {φ | MemLp (fieldGradient φ) 2 (ν ⊗ₘ κ) ∧
    Integrable (fun t => σ t (φ t)) ν}
  zero_mem' := by
    constructor
    · simpa only [fieldGradient_zero] using (MemLp.zero : MemLp (0 : α × Point d → Point d) 2 (ν ⊗ₘ κ))
    · simp only [Pi.zero_apply,map_zero]
      exact integrable_zero α ℝ ν
  add_mem' := by
    intro φ ψ hφ hψ
    constructor
    · simpa only [fieldGradient_add] using hφ.1.add hψ.1
    · simp only [Pi.add_apply,map_add]
      exact hφ.2.add hψ.2
  smul_mem' := by
    intro c φ hφ
    constructor
    · simpa only [fieldGradient_smul] using hφ.1.const_smul c
    · simpa only [Pi.smul_apply, map_smul, smul_eq_mul] using hφ.2.const_mul c

abbrev Field := fieldSpace ν κ σ

/-- Scalar source action integrated in time. -/
def fieldAction : Field ν κ σ →ₗ[ℝ] ℝ where
  toFun φ := ∫ t, σ t (φ.val t) ∂ν
  map_add' φ ψ := by
    simpa only [Submodule.coe_add, Pi.add_apply, map_add] using integral_add φ.property.2 ψ.property.2
  map_smul' c φ := by simp only [Submodule.coe_smul, Pi.smul_apply, map_smul,
    smul_eq_mul, integral_const_mul, RingHom.id_apply]

/-- Actual gradient in the joint L² space. -/
def fieldGradientLp (φ : Field ν κ σ) : Lp (Point d) 2 (ν ⊗ₘ κ) :=
  φ.property.1.toLp (fieldGradient φ.val)

omit [IsMarkovKernel κ] [BorelSpace (Point d)] [IsFiniteMeasure ν] in
theorem fieldGradientLp_ae (φ : Field ν κ σ) :
    fieldGradientLp ν κ σ φ =ᵐ[ν ⊗ₘ κ] fieldGradient φ.val := φ.property.1.coeFn_toLp

def fieldGradientLinear : Field ν κ σ →ₗ[ℝ] Lp (Point d) 2 (ν ⊗ₘ κ) where
  toFun := fieldGradientLp ν κ σ
  map_add' φ ψ := by
    apply Lp.ext
    filter_upwards [fieldGradientLp_ae ν κ σ (φ+ψ),
      Lp.coeFn_add (fieldGradientLp ν κ σ φ) (fieldGradientLp ν κ σ ψ),
      fieldGradientLp_ae ν κ σ φ, fieldGradientLp_ae ν κ σ ψ] with z ha hb hc hd
    rw [ha, hb]
    simp only [Submodule.coe_add, fieldGradient_add, Pi.add_apply, hc, hd]
  map_smul' c φ := by
    apply Lp.ext
    filter_upwards [fieldGradientLp_ae ν κ σ (c • φ),
      Lp.coeFn_smul c (fieldGradientLp ν κ σ φ), fieldGradientLp_ae ν κ σ φ] with z ha hb hc
    simp only [RingHom.id_apply]
    rw [ha,hb]
    simp only [Submodule.coe_smul,fieldGradient_smul,Pi.smul_apply,hc]

/-- Closed joint gradient space. -/
def fieldClosure : Submodule ℝ (Lp (Point d) 2 (ν ⊗ₘ κ)) :=
  (fieldGradientLinear ν κ σ).range.topologicalClosure

instance fieldClosure_completeSpace : CompleteSpace (fieldClosure ν κ σ) := by
  unfold fieldClosure
  infer_instance

def fieldIntoClosure : Field ν κ σ →ₗ[ℝ] fieldClosure ν κ σ :=
  (fieldGradientLinear ν κ σ).codRestrict (fieldClosure ν κ σ)
    (fun φ => (fieldGradientLinear ν κ σ).range.le_topologicalClosure (LinearMap.mem_range_self _ φ))

omit [IsMarkovKernel κ] [BorelSpace (Point d)] [IsFiniteMeasure ν] in
theorem dense_fieldIntoClosure : DenseRange (fieldIntoClosure ν κ σ) := by
  rw [DenseRange,Subtype.dense_iff]
  intro v hv
  change v ∈ closure (Set.range (fieldGradientLinear ν κ σ)) at hv
  convert hv using 1
  congr 1
  ext w
  simp only [Set.mem_image,Set.mem_range]
  constructor
  · rintro ⟨z,⟨φ,rfl⟩,rfl⟩
    exact ⟨φ,rfl⟩
  · rintro ⟨φ,rfl⟩
    exact ⟨fieldIntoClosure ν κ σ φ,⟨φ,rfl⟩,rfl⟩

omit [BorelSpace (Point d)] in
theorem fieldGradientLp_norm_sq (φ : Field ν κ σ) :
    ‖fieldGradientLp ν κ σ φ‖ ^ 2 =
      ∫ t, ∫ x, ‖gradient (φ.val t : Point d → ℝ) x‖ ^ 2 ∂κ t ∂ν := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  have hi := (memLp_two_iff_integrable_sq_norm φ.property.1.aestronglyMeasurable).mp φ.property.1
  calc
    _ = ∫ z, ‖fieldGradient φ.val z‖ ^ 2 ∂(ν ⊗ₘ κ) := by
      apply integral_congr_ae
      filter_upwards [fieldGradientLp_ae ν κ σ φ] with z hz
      rw [hz,real_inner_self_eq_norm_sq]
    _ = _ := Measure.integral_compProd hi

omit [BorelSpace (Point d)] in
/-- Pointwise variational bounds integrate into a joint quadratic bound. -/
theorem field_objective_le_integral {E : α → ℝ} (hE : Integrable E ν)
    (hbound : ∀ᵐ t ∂ν, ∀ φ : Test d, testObjective (κ t) (σ t) φ ≤ E t)
    (φ : Field ν κ σ) :
    DenseVariational.objective (fieldAction ν κ σ) (fieldIntoClosure ν κ σ) φ ≤ ∫ t, E t ∂ν := by
  change 2*(∫ t, σ t (φ.val t) ∂ν)-‖fieldGradientLp ν κ σ φ‖^2 ≤ _
  rw [fieldGradientLp_norm_sq]
  have hi := (memLp_two_iff_integrable_sq_norm φ.property.1.aestronglyMeasurable).mp φ.property.1
  have he := (Measure.integrable_compProd_iff hi.1).mp hi
  have hn : Integrable (fun t => ∫ x, ‖gradient (φ.val t : Point d → ℝ) x‖^2 ∂κ t) ν := by
    simpa only [fieldGradient,Real.norm_eq_abs,abs_pow,abs_norm] using he.2
  rw [← integral_const_mul,← integral_sub (φ.property.2.const_mul 2) hn]
  apply integral_mono_ae ((φ.property.2.const_mul 2).sub hn) hE
  filter_upwards [hbound] with t ht
  exact ht (φ.val t)

/-- One actual jointly measurable L² Riesz flux; no separate timewise selection. -/
def spaceTimeRepresentative : fieldClosure ν κ σ :=
  DenseVariational.representative (V := Field ν κ σ) (H := fieldClosure ν κ σ)
    (fieldAction ν κ σ) (fieldIntoClosure ν κ σ)

def spaceTimeFlux : Lp (Point d) 2 (ν ⊗ₘ κ) :=
  (spaceTimeRepresentative ν κ σ).val

omit [BorelSpace (Point d)] in
theorem spaceTimeFlux_pairing {E : α → ℝ} (hE : Integrable E ν)
    (hbound : ∀ᵐ t ∂ν, ∀ φ : Test d, testObjective (κ t) (σ t) φ ≤ E t)
    (φ : Field ν κ σ) :
    (∫ t, σ t (φ.val t) ∂ν) =
      ∫ z, ⟪fieldGradient φ.val z, spaceTimeFlux ν κ σ z⟫_ℝ ∂(ν ⊗ₘ κ) := by
  have hfin : BddAbove (Set.range (DenseVariational.objective
      (fieldAction ν κ σ) (fieldIntoClosure ν κ σ))) :=
    ⟨∫ t,E t ∂ν, by rintro y ⟨ψ,rfl⟩; exact field_objective_le_integral ν κ σ hE hbound ψ⟩
  letI : AddCommGroup (Field ν κ σ) := (fieldSpace ν κ σ).addCommGroup
  letI : Module ℝ (Field ν κ σ) := (fieldSpace ν κ σ).module
  have hp := DenseVariational.representative_pairing (V := Field ν κ σ) (H := fieldClosure ν κ σ) (fieldAction ν κ σ)
    (fieldIntoClosure ν κ σ) (dense_fieldIntoClosure ν κ σ) hfin φ
  calc
    (∫ t, σ t (φ.val t) ∂ν) = ⟪spaceTimeFlux ν κ σ,fieldGradientLp ν κ σ φ⟫_ℝ := hp.symm
    _ = ∫ z, ⟪fieldGradient φ.val z, spaceTimeFlux ν κ σ z⟫_ℝ ∂(ν ⊗ₘ κ) := by
      rw [real_inner_comm,L2.inner_def]
      apply integral_congr_ae
      filter_upwards [fieldGradientLp_ae ν κ σ φ] with z hz
      rw [hz]

omit [BorelSpace (Point d)] in
/-- The constructed joint flux retains the exact supplied integrated energy bound. -/
theorem spaceTimeFlux_energy_le {E : α → ℝ} (hE : Integrable E ν)
    (hbound : ∀ᵐ t ∂ν, ∀ φ : Test d, testObjective (κ t) (σ t) φ ≤ E t) :
    (∫ z, ‖spaceTimeFlux ν κ σ z‖ ^ 2 ∂(ν ⊗ₘ κ)) ≤ ∫ t,E t ∂ν := by
  have hfin : BddAbove (Set.range (DenseVariational.objective
      (fieldAction ν κ σ) (fieldIntoClosure ν κ σ))) :=
    ⟨∫ t,E t ∂ν, by rintro y ⟨ψ,rfl⟩; exact field_objective_le_integral ν κ σ hE hbound ψ⟩
  have he := DenseVariational.energy_eq_norm_sq (V := Field ν κ σ) (H := fieldClosure ν κ σ) (fieldAction ν κ σ)
    (fieldIntoClosure ν κ σ) (dense_fieldIntoClosure ν κ σ) hfin
  have hn : ‖spaceTimeFlux ν κ σ‖^2 = ∫ z, ‖spaceTimeFlux ν κ σ z‖^2 ∂(ν ⊗ₘ κ) := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    simp_rw [real_inner_self_eq_norm_sq]
  rw [← hn]
  change ‖DenseVariational.representative (V := Field ν κ σ) (H := fieldClosure ν κ σ) (fieldAction ν κ σ) (fieldIntoClosure ν κ σ)‖^2 ≤ _
  rw [← he]
  apply csSup_le (Set.range_nonempty _)
  rintro y ⟨φ,rfl⟩
  exact field_objective_le_integral ν κ σ hE hbound φ

end SharpWasserstein.RoughEulerianTransport
