module

public import SharpWasserstein.Compat
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic

@[expose] public section

/-! Algebraic estimates with the manuscript's genuine real-valued constants.
These lemmas do not assert that a diffusion or a Gaussian law realizes them. -/

noncomputable section

namespace SharpWasserstein

def localRate (k N : ℕ) : ℝ := (k : ℝ) ^ 2 / (N : ℝ) ^ 2

theorem localRate_nonneg (k N : ℕ) : 0 ≤ localRate k N := by
  unfold localRate
  positivity

theorem triangle_sq_bound {D a b r C₁ C₂ : ℝ}
    (hD : 0 ≤ D) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (htriangle : D ≤ a + b) (h₁ : a ^ 2 ≤ C₁ * r) (h₂ : b ^ 2 ≤ C₂ * r) :
    D ^ 2 ≤ (2 * C₁ + 2 * C₂) * r := by
  have hsq : D ^ 2 ≤ (a + b) ^ 2 := sq_le_sq₀ hD (by linarith) |>.2 htriangle
  nlinarith [sq_nonneg (a - b)]

/-- Exact scalar cost of changing the variance of the common Gaussian mode. -/
def gaussianModeCost (a r : ℝ) : ℝ := (Real.sqrt (a + r) - Real.sqrt a) ^ 2

theorem gaussianModeCost_rationalized {a r : ℝ} (ha : 0 < a) (hr : 0 ≤ r) :
    gaussianModeCost a r = r ^ 2 / (Real.sqrt (a + r) + Real.sqrt a) ^ 2 := by
  have hsa := Real.sq_sqrt (le_of_lt ha)
  have hsar := Real.sq_sqrt (show 0 ≤ a + r by linarith)
  have hpos : 0 < Real.sqrt (a + r) + Real.sqrt a := by
    exact add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) (Real.sqrt_pos.2 ha)
  apply (eq_div_iff (ne_of_gt (sq_pos_of_pos hpos))).2
  unfold gaussianModeCost
  nlinarith [sq_nonneg (Real.sqrt (a + r) * Real.sqrt a)]

theorem gaussianModeCost_initial_upper {r : ℝ} (hr : 0 ≤ r) :
    gaussianModeCost 1 r ≤ r ^ 2 / 4 := by
  rw [gaussianModeCost_rationalized (by norm_num) hr]
  have hs : 1 ≤ Real.sqrt (1 + r) := by
    exact (Real.le_sqrt (by norm_num) (by linarith)).2 (by nlinarith)
  have hden : 4 ≤ (Real.sqrt (1 + r) + Real.sqrt 1) ^ 2 := by
    norm_num only [Real.sqrt_one]
    nlinarith [Real.sqrt_nonneg (1+r)]
  exact div_le_div_of_nonneg_left (sq_nonneg r) (by norm_num) hden

theorem gaussianModeCost_lower {a r : ℝ} (ha : 0 < a) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    r ^ 2 / (Real.sqrt (a + 1) + Real.sqrt a) ^ 2 ≤ gaussianModeCost a r := by
  rw [gaussianModeCost_rationalized ha hr]
  have hm : Real.sqrt (a + r) ≤ Real.sqrt (a + 1) := Real.sqrt_le_sqrt (by linarith)
  have hp : 0 < Real.sqrt (a + r) + Real.sqrt a :=
    add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) (Real.sqrt_pos.2 ha)
  apply div_le_div_of_nonneg_left (sq_nonneg r) (sq_pos_of_pos hp)
  nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg (a + r), Real.sqrt_nonneg (a + 1)]

end SharpWasserstein
