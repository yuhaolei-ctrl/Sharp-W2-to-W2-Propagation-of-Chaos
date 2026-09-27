import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Explicit regularization constants and the integrable endpoint singularity

This module verifies the time integral of the squared deterministic control
bound appearing in the entropy--cost argument. It also proves the integrability
and exact integral of `1 + s ^ (-1/2)` at zero. These are Lebesgue interval
integrals, not axiomatized numerical formulas.

Girsanov's theorem, the entropy data-processing step, and the Wasserstein
continuity-equation theorem are not asserted by these real-analysis results.
-/

noncomputable section

namespace SharpWasserstein.RegularizationRates

open MeasureTheory intervalIntegral

/-- Deterministic bound on the bridge-control magnitude per unit displacement. -/
def bridgeRate (L s u : ℝ) : ℝ := L * (1 - u / s) + 1 / s

/-- Entropy--cost coefficient for noise amplitude `sqrt 2`. -/
def bridgeCost (L s : ℝ) : ℝ := (1 + L * s + L ^ 2 * s ^ 2 / 3) / (4 * s)

/-- The integrable upper bound for the switch-parameter metric speed. -/
def speedRate (s : ℝ) : ℝ := 1 + s ^ (-(1 / 2 : ℝ))

/-- An auxiliary exact polynomial quadrature. -/
theorem integral_affine_square (a b s : ℝ) :
    (∫ u in (0 : ℝ)..s, (a + b * u) ^ 2) =
      a ^ 2 * s + a * b * s ^ 2 + b ^ 2 * s ^ 3 / 3 := by
  have h0 : IntervalIntegrable (fun _ : ℝ => a ^ 2) volume 0 s :=
    intervalIntegrable_const
  have h1 : IntervalIntegrable (fun u : ℝ => (2 * a * b) * u) volume 0 s :=
    (continuous_const.mul continuous_id).intervalIntegrable 0 s
  have h2 : IntervalIntegrable (fun u : ℝ => b ^ 2 * u ^ 2) volume 0 s :=
    (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable 0 s
  calc
    (∫ u in (0 : ℝ)..s, (a + b * u) ^ 2) =
        ∫ u in (0 : ℝ)..s, (a ^ 2 + (2 * a * b) * u) + b ^ 2 * u ^ 2 := by
      congr 1
      funext u
      ring
    _ = a ^ 2 * s + a * b * s ^ 2 + b ^ 2 * s ^ 3 / 3 := by
      rw [integral_add (h0.add h1) h2, integral_add h0 h1]
      rw [intervalIntegral.integral_const_mul (2 * a * b) (fun u : ℝ => u),
        intervalIntegral.integral_const_mul (b ^ 2) (fun u : ℝ => u ^ 2),
        integral_id, integral_pow]
      simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
      norm_num
      ring

/-- The bridge square is integrable on any finite interval. -/
theorem intervalIntegrable_bridgeRate_sq (L s : ℝ) :
    IntervalIntegrable (fun u => bridgeRate L s u ^ 2) volume 0 s := by
  apply Continuous.intervalIntegrable
  unfold bridgeRate
  exact (continuous_const.mul (continuous_const.sub
    (continuous_id.div_const s)) |>.add continuous_const).pow 2

/-- The exact entropy--cost coefficient obtained by integrating the control bound. -/
theorem integral_bridgeRate_sq (L s : ℝ) (hs : 0 < s) :
    (1 / 4 : ℝ) * (∫ u in (0 : ℝ)..s, bridgeRate L s u ^ 2) = bridgeCost L s := by
  have hfun : (fun u => bridgeRate L s u ^ 2) =
      (fun u : ℝ => ((L + 1 / s) + (-L / s) * u) ^ 2) := by
    funext u
    unfold bridgeRate
    ring
  rw [hfun, integral_affine_square]
  unfold bridgeCost
  field_simp
  ring

/-- The inverse square-root singularity is integrable even at the zero endpoint. -/
theorem intervalIntegrable_inv_sqrt (t : ℝ) :
    IntervalIntegrable (fun s : ℝ => s ^ (-(1 / 2 : ℝ))) volume 0 t :=
  intervalIntegrable_rpow' (by norm_num)

/-- Integrability of the complete speed bound on a finite interval. -/
theorem intervalIntegrable_speedRate (t : ℝ) :
    IntervalIntegrable speedRate volume 0 t :=
  intervalIntegrable_const.add (intervalIntegrable_inv_sqrt t)

/-- The singular part has exactly the integral used in the manuscript. -/
theorem integral_inv_sqrt (t : ℝ) :
    (∫ s in (0 : ℝ)..t, s ^ (-(1 / 2 : ℝ))) = 2 * Real.sqrt t := by
  rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ)))]
  norm_num
  rw [← Real.sqrt_eq_rpow]
  ring

/-- Exact finite length of the upper speed bound, including its singular endpoint. -/
theorem integral_speedRate (t : ℝ) :
    (∫ s in (0 : ℝ)..t, speedRate s) = t + 2 * Real.sqrt t := by
  unfold speedRate
  rw [integral_add intervalIntegrable_const (intervalIntegrable_inv_sqrt t),
    integral_inv_sqrt]
  simp

/-- A single finite-horizon constant bounds all shorter interpolation lengths. -/
theorem integral_speedRate_le (t T : ℝ) (htT : t ≤ T) :
    (∫ s in (0 : ℝ)..t, speedRate s) ≤ T + 2 * Real.sqrt T := by
  rw [integral_speedRate]
  have hroot := Real.sqrt_le_sqrt htT
  linarith

end SharpWasserstein.RegularizationRates
