module

public import SharpWasserstein.Compat
public import SharpWasserstein.RegularizedTrialEnergy

@[expose] public section

/-! Exact finite-trial marginal fluctuation identity. The positive coefficient
penalty improves the bound, so it can safely be removed only in this direction. -/
noncomputable section
open scoped InnerProductSpace
namespace SharpWasserstein.RegularizedTrialEnergy
variable {C H G : Type*} [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

/-- When the source pairing is the actual marginal pairing, its trial
fluctuation differs from next-level energy by the regularized trial energy
and an additional nonnegative coefficient penalty. -/
theorem lifted_energy_gap (T : C →L[ℝ] H) (L : H →ₗᵢ[ℝ] G)
    (U : H) (V : G) (δ : ℝ) (hδ : 0 < δ)
    (hp : ∀ c,⟪V,L (T c)⟫_ℝ = ⟪U,T c⟫_ℝ) :
    ‖V-L (T (solution T δ U))‖^2 = ‖V‖^2-energy T δ U-δ*‖solution T δ U‖^2 := by
  have he := energy_eq_penalized_norm T δ hδ U
  rw [norm_sub_sq_real,LinearIsometry.norm_map,hp]
  change ‖V‖^2-2*energy T δ U+‖T (solution T δ U)‖^2 = _
  linarith

theorem lifted_energy_gap_le (T : C →L[ℝ] H) (L : H →ₗᵢ[ℝ] G)
    (U : H) (V : G) (δ : ℝ) (hδ : 0 < δ)
    (hp : ∀ c,⟪V,L (T c)⟫_ℝ = ⟪U,T c⟫_ℝ) :
    ‖V-L (T (solution T δ U))‖^2 ≤ ‖V‖^2-energy T δ U := by
  rw [lifted_energy_gap T L U V δ hδ hp]
  exact sub_le_self _ (mul_nonneg hδ.le (sq_nonneg _))

end SharpWasserstein.RegularizedTrialEnergy
