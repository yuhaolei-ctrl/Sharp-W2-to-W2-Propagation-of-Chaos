module

public import SharpWasserstein.Compat
public import SharpWasserstein.ExternalInteractionEnergy

@[expose] public section

/-! The sharp finite hierarchy uses a comparison coefficient depending only
on spatial dimension and the stated value/first-derivative kernel bounds. -/
noncomputable section
namespace SharpWasserstein.BrownianPeriodicHierarchy
open ExternalInteraction

def driftLipschitz (d : ℕ) (L₁ L₂ : ℝ) : ℝ :=
  Real.sqrt (2*(d:ℝ)*(L₁^2+L₂^2))

def baseline (d : ℕ) (L₁ L₂ : ℝ) : ℝ :=
  2*driftLipschitz d L₁ L₂+2*(d:ℝ)*L₁+1

def comparisonConstant (d : ℕ) (M L₁ L₂ : ℝ) : ℝ :=
  max (baseline d L₁ L₂) (2*gradientConstant d M L₁ L₂)

def externalFraction (N m : ℕ) : ℝ := ((N:ℝ)-m)/N

def rate (d : ℕ) (M L₁ L₂ : ℝ) (N m : ℕ) : ℝ :=
  2*externalFraction N m*gradientConstant d M L₁ L₂*(m:ℝ)

theorem driftLipschitz_nonneg (d : ℕ) (L₁ L₂ : ℝ) : 0 ≤ driftLipschitz d L₁ L₂ :=
  Real.sqrt_nonneg _

theorem baseline_nonneg (d : ℕ) {L₁ L₂ : ℝ} (hL₁ : 0 ≤ L₁) : 0 ≤ baseline d L₁ L₂ := by
  unfold baseline driftLipschitz
  positivity

theorem comparisonConstant_nonneg (d : ℕ) (M L₁ L₂ : ℝ) :
    0 ≤ comparisonConstant d M L₁ L₂ :=
  (mul_nonneg (by norm_num) (gradientConstant_nonneg d M L₁ L₂)).trans (le_max_right _ _)

theorem baseline_le_comparison (d : ℕ) (M L₁ L₂ : ℝ) :
    baseline d L₁ L₂ ≤ comparisonConstant d M L₁ L₂ := le_max_left _ _

theorem terminal_le_comparison (d : ℕ) (M L₁ L₂ : ℝ) (hL₁ : 0 ≤ L₁) :
    2*driftLipschitz d L₁ L₂+1 ≤ comparisonConstant d M L₁ L₂ := by
  apply le_trans _ (baseline_le_comparison d M L₁ L₂)
  unfold baseline
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) d) hL₁]

theorem externalFraction_bounds {N m : ℕ} (hN : 0 < N) (hm : m ≤ N) :
    0 ≤ externalFraction N m ∧ externalFraction N m ≤ 1 := by
  have hNr : (0:ℝ)<N := Nat.cast_pos.mpr hN
  constructor
  · exact div_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr hm)) hNr.le
  · exact (div_le_one hNr).mpr (by linarith [Nat.cast_nonneg (α := ℝ) m])

theorem rate_bounds (d : ℕ) (M L₁ L₂ : ℝ) {N m : ℕ} (hN : 0 < N) (hm : m ≤ N) :
    0 ≤ rate d M L₁ L₂ N m ∧ rate d M L₁ L₂ N m ≤ comparisonConstant d M L₁ L₂*m := by
  have hθ := externalFraction_bounds hN hm
  have hG := gradientConstant_nonneg d M L₁ L₂
  constructor
  · exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hθ.1) hG) (Nat.cast_nonneg m)
  · calc
      rate d M L₁ L₂ N m ≤ 2*gradientConstant d M L₁ L₂*m := by
        unfold rate
        nlinarith [mul_nonneg hG (Nat.cast_nonneg (α := ℝ) m),
          mul_le_mul_of_nonneg_right hθ.2 (mul_nonneg hG (Nat.cast_nonneg (α := ℝ) m))]
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Nat.cast_nonneg m)

theorem rate_top (d : ℕ) (M L₁ L₂ : ℝ) (N : ℕ) : rate d M L₁ L₂ N N = 0 := by
  simp [rate,externalFraction]

end SharpWasserstein.BrownianPeriodicHierarchy
