import SharpWasserstein.WeightedTangent

/-! A genuine random-map flux defines a continuous functional on the weighted
output tangent space. Pullback is the actual measure-preserving L² isometry;
no conditional expectation or postulated divergence representation is used. -/
noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace
namespace SharpWasserstein.PropagatedFlux
open WeightedTangent
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
  [MeasurableSpace (Point d)] [BorelSpace (Point d)]
  (ρ : Measure Ω) [IsFiniteMeasure ρ] (X : Ω → Point d) (hX : Measurable X)

include hX

omit [BorelSpace (Point d)] [IsFiniteMeasure ρ] in
/-- The given random map preserves measure into its actual pushforward law. -/
theorem mapPreserving : MeasurePreserving X ρ (ρ.map X) := ⟨hX,rfl⟩

/-- The genuine weighted L² pullback along the random endpoint. -/
def pullback : Lp (Point d) 2 (ρ.map X) →ₗᵢ[ℝ] Lp (Point d) 2 ρ :=
  Lp.compMeasurePreservingₗᵢ ℝ X (mapPreserving ρ X hX)

/-- A square-integrable random velocity acts continuously on the output tangent space. -/
def tangentFunctional (V : Lp (Point d) 2 ρ) : gradientClosure (ρ.map X) →L[ℝ] ℝ :=
  (innerSL ℝ V).comp ((pullback ρ X hX).toContinuousLinearMap.comp
    (gradientClosure (ρ.map X)).subtypeL)

theorem tangentFunctional_norm_le (V : Lp (Point d) 2 ρ) :
    ‖tangentFunctional ρ X hX V‖ ≤ ‖V‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro g
  change ‖⟪V,pullback ρ X hX (g : Lp (Point d) 2 (ρ.map X))⟫_ℝ‖ ≤ ‖V‖*‖g‖
  simpa only [(pullback ρ X hX).norm_map,Submodule.coe_norm] using
    norm_inner_le_norm V (pullback ρ X hX (g : Lp (Point d) 2 (ρ.map X)))

/-- Distributional source obtained by testing the actual random-map flux. -/
def source (V : Lp (Point d) 2 ρ) : Test d →ₗ[ℝ] ℝ :=
  (tangentFunctional ρ X hX V).toLinearMap.comp (gradientIntoClosure (ρ.map X))

theorem source_eq_inner (V : Lp (Point d) 2 ρ) (φ : Test d) :
    source ρ X hX V φ = ⟪V,pullback ρ X hX (testGradient (ρ.map X) φ)⟫_ℝ := rfl

/-- The source's action is its actual integral pairing along the random map. -/
theorem source_apply (V : Lp (Point d) 2 ρ) (φ : Test d) :
    source ρ X hX V φ = ∫ z, ⟪gradient (φ : Point d → ℝ) (X z),V z⟫_ℝ ∂ρ := by
  rw [source_eq_inner,L2.inner_def]
  apply integral_congr_ae
  have hp := Lp.coeFn_compMeasurePreserving (testGradient (ρ.map X) φ) (mapPreserving ρ X hX)
  have hg := (mapPreserving ρ X hX).quasiMeasurePreserving.ae (testGradient_ae (ρ.map X) φ)
  filter_upwards [hp,hg] with z hpz hgz
  change ⟪V z,(Lp.compMeasurePreserving X (mapPreserving ρ X hX) (testGradient (ρ.map X) φ)) z⟫_ℝ = _
  rw [hpz]
  change ⟪V z,testGradient (ρ.map X) φ (X z)⟫_ℝ = _
  rw [hgz,real_inner_comm]

/-- Every compact-test objective is bounded by the actual input random energy. -/
theorem testObjective_le (V : Lp (Point d) 2 ρ) (φ : Test d) :
    testObjective (ρ.map X) (source ρ X hX V) φ ≤ ‖V‖^2 := by
  rw [testObjective,source_eq_inner,← testGradient_norm_sq]
  have hn := norm_sub_sq_real (pullback ρ X hX (testGradient (ρ.map X) φ)) V
  rw [(pullback ρ X hX).norm_map,real_inner_comm] at hn
  nlinarith [sq_nonneg ‖pullback ρ X hX (testGradient (ρ.map X) φ)-V‖]

theorem source_finiteEnergy (V : Lp (Point d) 2 ρ) :
    FiniteEnergy (ρ.map X) (source ρ X hX V) := by
  refine ⟨‖V‖^2,?_⟩
  rintro a ⟨φ,rfl⟩
  exact testObjective_le ρ X hX V φ

/-- The propagated source has no more energy than its actual random flux. -/
theorem source_energy_le (V : Lp (Point d) 2 ρ) :
    energy (ρ.map X) (source ρ X hX V) ≤ ∫ z, ‖V z‖^2 ∂ρ := by
  have he : ‖V‖^2 = ∫ z, ‖V z‖^2 ∂ρ := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    simp_rw [real_inner_self_eq_norm_sq]
  rw [← he]
  apply csSup_le (Set.range_nonempty _)
  rintro a ⟨φ,rfl⟩
  exact testObjective_le ρ X hX V φ

end SharpWasserstein.PropagatedFlux
