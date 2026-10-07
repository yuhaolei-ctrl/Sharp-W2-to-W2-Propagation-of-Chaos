module

public import SharpWasserstein.Compat
public import SharpWasserstein.RegularizedSource

@[expose] public section

/-! Uniform finite-horizon constants for the actual regularized source estimate.
The coefficient is independent of both the full and the marginal particle count. -/
noncomputable section
open MeasureTheory InformationTheory
open scoped NNReal ENNReal BigOperators
namespace SharpWasserstein.RegularizationRates

def bridgeHorizonFactor (L U : ℝ) : ℝ := (1 + L * U + L ^ 2 * U ^ 2 / 3) / 4

theorem bridgeCost_le_horizonFactor_div {L s U : ℝ} (hL : 0 ≤ L) (hs : 0 < s) (hsU : s ≤ U) :
    bridgeCost L s ≤ bridgeHorizonFactor L U / s := by
  have hU : 0 ≤ U := hs.le.trans hsU
  have h₁ := mul_le_mul_of_nonneg_left hsU hL
  have h₂ := mul_le_mul_of_nonneg_left ((sq_le_sq₀ hs.le hU).mpr hsU) (sq_nonneg L)
  unfold bridgeCost bridgeHorizonFactor
  rw [div_div]
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

theorem affine_bridgeCost_le {a b L s U : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hs : 0 < s) (hsU : s ≤ U) :
    a + b * bridgeCost L s ≤ (a + b * bridgeHorizonFactor L U) * (1 + 1 / s) := by
  have hU : 0 ≤ U := hs.le.trans hsU
  have hD : 0 ≤ bridgeHorizonFactor L U := by unfold bridgeHorizonFactor; positivity
  have h := mul_le_mul_of_nonneg_left (bridgeCost_le_horizonFactor_div hL hs hsU) hb
  have has : 0 ≤ a / s := div_nonneg ha hs.le
  have hbd : 0 ≤ b * bridgeHorizonFactor L U := mul_nonneg hb hD
  calc
    _ ≤ a + b * (bridgeHorizonFactor L U / s) := add_le_add_right h a
    _ ≤ (a + b * (bridgeHorizonFactor L U / s)) +
        (a / s + b * bridgeHorizonFactor L U) :=
      le_add_of_nonneg_right (add_nonneg has hbd)
    _ = _ := by ring

/-- An explicit dimension/kernel/initial-profile/horizon constant. -/
def sourceHorizonConstant (d : ℕ) (B C₀ L U : ℝ) : ℝ :=
  2 * (d * internalSourceConstant B) +
    (2 * (d * internalSourceConstant B) + 16 * d * B ^ 2) * C₀ * bridgeHorizonFactor L U

theorem source_coefficient_le_singular {d : ℕ} {B C₀ L s U : ℝ}
    (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀) (hL : 0 ≤ L) (hs : 0 < s) (hsU : s ≤ U) :
    2 * (d * internalSourceConstant B) * (1 + bridgeCost L s * C₀) +
        16 * d * B ^ 2 * (bridgeCost L s * C₀) ≤
      sourceHorizonConstant d B C₀ L U * (1 + 1 / s) := by
  have hI := internalSourceConstant_nonneg hB
  have h := affine_bridgeCost_le
    (a := 2 * (d * internalSourceConstant B))
    (b := (2 * (d * internalSourceConstant B) + 16 * d * B ^ 2) * C₀)
    (by positivity) (by positivity) hL hs hsU
  unfold sourceHorizonConstant
  convert h using 1; ring

theorem full_source_coefficient_le_singular {d : ℕ} {B C₀ L s U : ℝ}
    (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀) (hL : 0 ≤ L) (hs : 0 < s) (hsU : s ≤ U) :
    (d * internalSourceConstant B) * (1 + bridgeCost L s * C₀) ≤
      sourceHorizonConstant d B C₀ L U * (1 + 1 / s) := by
  have hI : 0 ≤ d * internalSourceConstant B := mul_nonneg (Nat.cast_nonneg _) (internalSourceConstant_nonneg hB)
  have hH : 0 ≤ bridgeCost L s * C₀ := by unfold bridgeCost; positivity
  apply le_trans _ (source_coefficient_le_singular (d := d) hB hC₀ hL hs hsU)
  have hpart : 0 ≤ (16 : ℝ) * d * B ^ 2 * (bridgeCost L s * C₀) := by positivity
  nlinarith

end SharpWasserstein.RegularizationRates
