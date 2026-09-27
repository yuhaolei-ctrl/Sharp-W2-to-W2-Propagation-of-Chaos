import SharpWasserstein.PropagatedFlux

/-! Actual pushforward of a square-integrable vector flux. The output field is
constructed by Riesz on the full output L² space, rather than assumed as a
conditional expectation. The energy contracts with constant one. -/
noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace ENNReal
namespace SharpWasserstein.RoughEulerianCompression
open WeightedTangent
variable {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z] {d : ℕ}
  (ρ : Measure Ω) (X : Ω → Z) (hX : Measurable X)

def fluxPullback : Lp (Point d) 2 (ρ.map X) →ₗᵢ[ℝ] Lp (Point d) 2 ρ :=
  Lp.compMeasurePreservingₗᵢ ℝ X ⟨hX,rfl⟩

def pushFunctional (V : Lp (Point d) 2 ρ) : Lp (Point d) 2 (ρ.map X) →L[ℝ] ℝ :=
  (innerSL ℝ V).comp (fluxPullback ρ X hX).toContinuousLinearMap

theorem pushFunctional_norm_le (V : Lp (Point d) 2 ρ) : ‖pushFunctional ρ X hX V‖ ≤ ‖V‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro G
  change ‖⟪V,fluxPullback ρ X hX G⟫_ℝ‖ ≤ ‖V‖*‖G‖
  simpa only [(fluxPullback ρ X hX).norm_map] using norm_inner_le_norm V (fluxPullback ρ X hX G)

/-- A genuine output L² field representing the pushed vector flux. -/
def pushedFlux (V : Lp (Point d) 2 ρ) : Lp (Point d) 2 (ρ.map X) :=
  TangentEnergy.rieszRepresentative (pushFunctional ρ X hX V)

theorem pushedFlux_norm_le (V : Lp (Point d) 2 ρ) : ‖pushedFlux ρ X hX V‖ ≤ ‖V‖ := by
  simpa only [pushedFlux,TangentEnergy.rieszRepresentative,LinearIsometryEquiv.norm_map] using
    pushFunctional_norm_le ρ X hX V

/-- Exact Hilbert pairing for every output L² test vector, not only gradients. -/
theorem pushedFlux_inner (V : Lp (Point d) 2 ρ) (G : Lp (Point d) 2 (ρ.map X)) :
    ⟪G,pushedFlux ρ X hX V⟫_ℝ = ⟪fluxPullback ρ X hX G,V⟫_ℝ := by
  rw [real_inner_comm,pushedFlux,TangentEnergy.inner_rieszRepresentative]
  change ⟪V,fluxPullback ρ X hX G⟫_ℝ = ⟪fluxPullback ρ X hX G,V⟫_ℝ
  exact real_inner_comm _ _

/-- The Hilbert identity is the literal pushed vector-flux integral identity. -/
theorem pushedFlux_pairing (V : Lp (Point d) 2 ρ) (G : Z → Point d)
    (hG : MemLp G 2 (ρ.map X)) :
    (∫ y,⟪G y,pushedFlux ρ X hX V y⟫_ℝ ∂ρ.map X) =
      ∫ z,⟪G (X z),V z⟫_ℝ ∂ρ := by
  have hp := pushedFlux_inner ρ X hX V (hG.toLp G)
  rw [L2.inner_def,L2.inner_def] at hp
  have hl : (∫ y,⟪G y,pushedFlux ρ X hX V y⟫_ℝ ∂ρ.map X) =
      ∫ y,⟪hG.toLp G y,pushedFlux ρ X hX V y⟫_ℝ ∂ρ.map X := by
    apply integral_congr_ae
    filter_upwards [hG.coeFn_toLp] with y hy
    rw [hy]
  rw [hl,hp]
  apply integral_congr_ae
  have hmp : MeasurePreserving X ρ (ρ.map X) := ⟨hX,rfl⟩
  filter_upwards [Lp.coeFn_compMeasurePreserving (hG.toLp G) hmp,
    hmp.quasiMeasurePreserving.ae hG.coeFn_toLp] with z hz hg
  change ⟪(Lp.compMeasurePreserving X hmp (hG.toLp G)) z,V z⟫_ℝ = _
  rw [hz]
  simp only [Function.comp_apply,hg]

/-- Exact contraction of the genuine integrated Euclidean action. -/
theorem pushedFlux_energy_le (V : Lp (Point d) 2 ρ) :
    (∫ y,‖pushedFlux ρ X hX V y‖^2 ∂ρ.map X) ≤ ∫ z,‖V z‖^2 ∂ρ := by
  have hnV : ‖V‖^2 = ∫ z,‖V z‖^2 ∂ρ := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    simp_rw [real_inner_self_eq_norm_sq]
  have hnP : ‖pushedFlux ρ X hX V‖^2 = ∫ y,‖pushedFlux ρ X hX V y‖^2 ∂ρ.map X := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    simp_rw [real_inner_self_eq_norm_sq]
  rw [← hnP,← hnV]
  exact pow_le_pow_left₀ (norm_nonneg _) (pushedFlux_norm_le ρ X hX V) 2

end SharpWasserstein.RoughEulerianCompression
