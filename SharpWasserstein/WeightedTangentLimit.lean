module

public import SharpWasserstein.Compat
public import SharpWasserstein.WeightedTangent
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Topology.Order.LiminfLimsup

@[expose] public section

/-!
# Varying-weight lower semicontinuity of weighted tangent energy

Weak convergence is the actual topology on Borel probability measures.
Distribution convergence is tested on every actual compact smooth test.
The extended energy takes values in `ℝ≥0∞`, so the lower semicontinuity
statement also covers an infinite limit energy without totalizing a real supremum.
-/

noncomputable section
namespace SharpWasserstein.WeightedTangent

open MeasureTheory Set Filter
open scoped InnerProductSpace Topology BoundedContinuousFunction ENNReal

variable {d : ℕ} [MeasurableSpace (Point d)] [BorelSpace (Point d)]

/-- The actual squared Euclidean test gradient is bounded and continuous. -/
def gradientSquare (φ : Test d) : Point d →ᵇ ℝ where
  toFun := fun x => ‖gradient (φ : Point d → ℝ) x‖ ^ 2
  continuous_toFun := (continuous_test_gradient φ).norm.pow 2
  map_bounded' := by
    have hc : HasCompactSupport (fun x => ‖gradient (φ : Point d → ℝ) x‖ ^ 2) :=
      (compactSupport_test_gradient φ).comp_left
        (g := fun v : Point d => ‖v‖ ^ 2) (by simp)
    exact Metric.isBounded_range_iff.mp
      (hc.isCompact_range ((continuous_test_gradient φ).norm.pow 2)).isBounded

/-- Weak convergence really controls the energy integral of each compact smooth test. -/
theorem tendsto_gradient_integral {I : Type*} {F : Filter I}
    {μs : I → ProbabilityMeasure (Point d)} {μ : ProbabilityMeasure (Point d)}
    (hμ : Tendsto μs F (𝓝 μ)) (φ : Test d) :
    Tendsto (fun i => ∫ x, ‖gradient (φ : Point d → ℝ) x‖ ^ 2 ∂(μs i : Measure (Point d))) F
      (𝓝 (∫ x, ‖gradient (φ : Point d → ℝ) x‖ ^ 2 ∂(μ : Measure (Point d)))) :=
  (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ) (gradientSquare φ)

/-- Joint convergence of the weight and distribution gives convergence of each variational test. -/
theorem tendsto_testObjective {I : Type*} {F : Filter I}
    {μs : I → ProbabilityMeasure (Point d)} {μ : ProbabilityMeasure (Point d)}
    {σs : I → (Test d →ₗ[ℝ] ℝ)} {σ : Test d →ₗ[ℝ] ℝ}
    (hμ : Tendsto μs F (𝓝 μ))
    (hσ : ∀ φ, Tendsto (fun i => σs i φ) F (𝓝 (σ φ))) (φ : Test d) :
    Tendsto (fun i => testObjective (μs i : Measure (Point d)) (σs i) φ) F
      (𝓝 (testObjective (μ : Measure (Point d)) σ φ)) :=
  ((hσ φ).const_mul 2).sub (tendsto_gradient_integral hμ φ)

/-- The nonnegative extended version of the same compact-test variational energy. -/
def extendedEnergy (μ : Measure (Point d)) [IsFiniteMeasure μ] (σ : Test d →ₗ[ℝ] ℝ) : ℝ≥0∞ :=
  ⨆ φ : Test d, ENNReal.ofReal (testObjective μ σ φ)

omit [BorelSpace (Point d)] in
/-- At finite energy the extended and real variational definitions agree exactly. -/
theorem extendedEnergy_eq_ofReal (μ : Measure (Point d)) [IsFiniteMeasure μ]
    (σ : Test d →ₗ[ℝ] ℝ) (h : FiniteEnergy μ σ) :
    extendedEnergy μ σ = ENNReal.ofReal (energy μ σ) := by
  apply le_antisymm
  · apply iSup_le
    intro φ
    exact ENNReal.ofReal_le_ofReal (le_csSup h ⟨φ, rfl⟩)
  · by_cases ht : extendedEnergy μ σ = ∞
    · simp [ht]
    · apply (ENNReal.ofReal_le_iff_le_toReal ht).mpr
      apply csSup_le (Set.range_nonempty _)
      rintro y ⟨φ, rfl⟩
      exact (ENNReal.ofReal_le_iff_le_toReal ht).mp (le_iSup (fun φ =>
        ENNReal.ofReal (testObjective μ σ φ)) φ)

omit [BorelSpace (Point d)] in
/-- The extended energy is finite precisely under the genuine bounded-test condition. -/
theorem finiteEnergy_iff_extendedEnergy_ne_top (μ : Measure (Point d)) [IsFiniteMeasure μ]
    (σ : Test d →ₗ[ℝ] ℝ) : FiniteEnergy μ σ ↔ extendedEnergy μ σ ≠ ∞ := by
  constructor
  · intro h
    rw [extendedEnergy_eq_ofReal μ σ h]
    exact ENNReal.ofReal_ne_top
  · intro ht
    refine ⟨(extendedEnergy μ σ).toReal, ?_⟩
    rintro y ⟨φ, rfl⟩
    exact (ENNReal.ofReal_le_iff_le_toReal ht).mp (le_iSup (fun φ =>
      ENNReal.ofReal (testObjective μ σ φ)) φ)

/-- Varying-weight lower semicontinuity, including infinite-energy limits. -/
theorem extendedEnergy_le_liminf {I : Type*} {F : Filter I} [F.NeBot]
    {μs : I → ProbabilityMeasure (Point d)} {μ : ProbabilityMeasure (Point d)}
    {σs : I → (Test d →ₗ[ℝ] ℝ)} {σ : Test d →ₗ[ℝ] ℝ}
    (hμ : Tendsto μs F (𝓝 μ))
    (hσ : ∀ φ, Tendsto (fun i => σs i φ) F (𝓝 (σ φ))) :
    extendedEnergy (μ : Measure (Point d)) σ ≤
      liminf (fun i => extendedEnergy (μs i : Measure (Point d)) (σs i)) F := by
  apply iSup_le
  intro φ
  have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (tendsto_testObjective hμ hσ φ)
  rw [← ht.liminf_eq]
  exact liminf_le_liminf (Eventually.of_forall fun i =>
    le_iSup (fun ψ => ENNReal.ofReal (testObjective (μs i : Measure (Point d)) (σs i) ψ)) φ)

/-- A uniform finite energy bound survives weak convergence of weights and test distributions. -/
theorem finiteEnergy_bound_of_tendsto {I : Type*} {F : Filter I} [F.NeBot]
    {μs : I → ProbabilityMeasure (Point d)} {μ : ProbabilityMeasure (Point d)}
    {σs : I → (Test d →ₗ[ℝ] ℝ)} {σ : Test d →ₗ[ℝ] ℝ} {A : ℝ}
    (hμ : Tendsto μs F (𝓝 μ))
    (hσ : ∀ φ, Tendsto (fun i => σs i φ) F (𝓝 (σ φ)))
    (hA : ∀ᶠ i in F, FiniteEnergy (μs i : Measure (Point d)) (σs i) ∧
      energy (μs i : Measure (Point d)) (σs i) ≤ A) :
    FiniteEnergy (μ : Measure (Point d)) σ ∧ energy (μ : Measure (Point d)) σ ≤ A := by
  have hb (φ : Test d) : testObjective (μ : Measure (Point d)) σ φ ≤ A := by
    apply le_of_tendsto (tendsto_testObjective hμ hσ φ)
    filter_upwards [hA] with i hi
    exact (le_csSup hi.1 ⟨φ, rfl⟩).trans hi.2
  constructor
  · exact ⟨A, by rintro y ⟨φ, rfl⟩; exact hb φ⟩
  · exact csSup_le (Set.range_nonempty _) (by rintro y ⟨φ, rfl⟩; exact hb φ)

/-- The weak limit admits an actual weighted divergence flux with the inherited energy bound. -/
theorem exists_tangent_of_weak_limit {I : Type*} {F : Filter I} [F.NeBot]
    {μs : I → ProbabilityMeasure (Point d)} {μ : ProbabilityMeasure (Point d)}
    {σs : I → (Test d →ₗ[ℝ] ℝ)} {σ : Test d →ₗ[ℝ] ℝ} {A : ℝ}
    (hμ : Tendsto μs F (𝓝 μ))
    (hσ : ∀ φ, Tendsto (fun i => σs i φ) F (𝓝 (σ φ)))
    (hA : ∀ᶠ i in F, FiniteEnergy (μs i : Measure (Point d)) (σs i) ∧
      energy (μs i : Measure (Point d)) (σs i) ≤ A) :
    ∃ v : gradientClosure (μ : Measure (Point d)),
      (∀ φ : Test d, σ φ = ∫ x, ⟪gradient (φ : Point d → ℝ) x,
        (v : Lp (Point d) 2 (μ : Measure (Point d))) x⟫_ℝ ∂(μ : Measure (Point d))) ∧
      (∫ x, ‖(v : Lp (Point d) 2 (μ : Measure (Point d))) x‖ ^ 2
        ∂(μ : Measure (Point d))) ≤ A := by
  obtain ⟨hfin, hb⟩ := finiteEnergy_bound_of_tendsto hμ hσ hA
  refine ⟨representative (μ : Measure (Point d)) σ,
    representative_divergence (μ : Measure (Point d)) σ hfin, ?_⟩
  rwa [← energy_eq_integral (μ : Measure (Point d)) σ hfin]

end SharpWasserstein.WeightedTangent
