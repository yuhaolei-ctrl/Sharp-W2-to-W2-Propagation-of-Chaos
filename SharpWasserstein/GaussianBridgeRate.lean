module

public import SharpWasserstein.Compat
public import SharpWasserstein.RegularizationRates
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! Exact finite Gaussian bridge coefficients and their limiting value. -/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace SharpWasserstein.GaussianBridge

def gridCost (K T : ℝ) (n : ℕ) : ℝ :=
  (T / (n+1) / 4) * ∑ j ∈ Finset.range (n+1),
    (RegularizationRates.bridgeRate K T ((j : ℝ) * (T/(n+1))))^2

theorem sum_real_range (n : ℕ) : (∑ j ∈ Finset.range n, (j : ℝ)) = (n : ℝ)*((n : ℝ)-1)/2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem sum_real_range_sq (n : ℕ) : (∑ j ∈ Finset.range n, (j : ℝ)^2) =
    (n : ℝ)*((n : ℝ)-1)*(2*(n : ℝ)-1)/6 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- The upper-sum correction is explicit and vanishes under mesh refinement. -/
theorem gridCost_eq (K : ℝ) {T : ℝ} (hT : T ≠ 0) (n : ℕ) :
    gridCost K T n = RegularizationRates.bridgeCost K T + K/(4*(n+1)) +
      K^2*T/(8*(n+1)) + K^2*T/(24*(n+1)^2) := by
  have hn : (n : ℝ)+1 ≠ 0 := by positivity
  have hp (j : ℕ) : (RegularizationRates.bridgeRate K T ((j : ℝ)*(T/(n+1))))^2 =
      (K+1/T)^2 - (2*(K+1/T)*K/((n : ℝ)+1))*(j : ℝ) +
        (K/((n : ℝ)+1))^2*(j : ℝ)^2 := by
    unfold RegularizationRates.bridgeRate
    field_simp
    ring
  unfold gridCost
  rw [Finset.sum_congr rfl (fun j _ ↦ hp j)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum, sum_real_range, sum_real_range_sq]
  push_cast
  unfold RegularizationRates.bridgeCost
  field_simp
  ring

/-- The finite-step Gaussian coefficient converges to the manuscript's exact
`(1+KT+K²T²/3)/(4T)` constant. -/
theorem gridCost_tendsto (K : ℝ) {T : ℝ} (hT : T ≠ 0) :
    Tendsto (gridCost K T) atTop (𝓝 (RegularizationRates.bridgeCost K T)) := by
  have hi : Tendsto (fun n : ℕ ↦ (1 : ℝ)/(n+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hc : Tendsto (fun _ : ℕ ↦ RegularizationRates.bridgeCost K T) atTop
      (𝓝 (RegularizationRates.bridgeCost K T)) := tendsto_const_nhds
  have h := ((hc.add (hi.const_mul (K/4))).add
    (hi.const_mul (K^2*T/8))).add ((hi.pow 2).const_mul (K^2*T/24))
  have he : gridCost K T = fun n : ℕ ↦ RegularizationRates.bridgeCost K T +
      K/4*(1/(n+1)) + K^2*T/8*(1/(n+1)) + K^2*T/24*(1/(n+1))^2 := by
    funext n
    rw [gridCost_eq K hT n]
    have hn : (n : ℝ)+1 ≠ 0 := by positivity
    field_simp
  rw [he]
  simpa using h

end SharpWasserstein.GaussianBridge
