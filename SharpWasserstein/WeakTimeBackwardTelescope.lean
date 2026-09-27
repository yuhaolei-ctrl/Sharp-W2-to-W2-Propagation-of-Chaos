import SharpWasserstein.WeakTimeBackwardStep
import SharpWasserstein.GaussianTimeBackward

/-! Discrete backward comparison for arbitrary time-dependent weak solutions.
All tests are genuine Gaussian Euler expectations with the correct drift
at each step, and all regularity and consistency moduli have been derived. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal ContDiff BigOperators
namespace SharpWasserstein.WeakEvolution
open WeightedTangent NoiseAverage BackwardEuler
variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  {v : ℝ → Configuration d N → Configuration d N} {P : ℝ → Measure (Configuration d N)}
  (h : WeakEvolution v P)
include h

theorem time_backward_telescope_error {K K₁ K₂ M L L₁ L₂ : ℝ≥0}
    (hvC : Continuous (Function.uncurry v))
    (hv : ∀ t, ContDiff ℝ ∞ (v t)) (hvB : ∀ t, AllDerivativesBounded (v t))
    (hvL : ∀ t, LipschitzWith K (v t))
    (hv₁ : ∀ t, LipschitzWith K₁ (fderiv ℝ (v t)))
    (hv₂ : ∀ t, LipschitzWith K₂ (fderiv ℝ (fderiv ℝ (v t))))
    (hM : ∀ t x, ‖v t x‖ ≤ M) {φ : Configuration d N → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφB : AllDerivativesBounded φ)
    (hL : LipschitzWith L φ) (hL₁ : LipschitzWith L₁ (fderiv ℝ φ))
    (hL₂ : LipschitzWith L₂ (fderiv ℝ (fderiv ℝ φ))) (T : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
      ∀ δ : ℝ≥0, ∀ n : ℕ, (n:ℝ≥0)*δ ≤ T → (δ:ℝ) < η →
      ‖(∫ x, φ x ∂P ((n:ℝ)*δ))-(∫ x, backwardTime v δ φ n 0 x ∂P 0)‖ ≤
        (n:ℝ)*δ*(ε+C*((M:ℝ)*δ+Real.sqrt (2*δ)*FrozenGaussian.noiseFirstMoment d N)) := by
  obtain ⟨U,U₁,U₂,hU⟩ := uniform_backwardTime_derivative_bounds
    hv hvB hvL hv₁ hv₂ hφ hφB hL hL₁ hL₂ T
  let C : ℝ := (N*d:ℕ)*(U₂:ℝ)+U₁*M
  refine ⟨C,by dsimp [C]; positivity,fun ε hε => ?_⟩
  obtain ⟨η,hη,he⟩ := uniform_time_backward_step_error h hvC hvL hM (T:ℝ) U U₁ U₂ hε
  refine ⟨η,hη,fun δ n hn hδ => ?_⟩
  let a : ℕ → ℝ := fun j => ∫ x, backwardTime v δ φ (n-j) j x ∂P ((j:ℝ)*δ)
  let B : ℝ := ε+C*((M:ℝ)*δ+Real.sqrt (2*δ)*FrozenGaussian.noiseFirstMoment d N)
  have htime (j : ℕ) (hj : j ≤ n) : (j:ℝ)*δ ∈ Icc 0 (T:ℝ) := by
    constructor
    · positivity
    · have hjn : (j:ℝ≥0)*δ ≤ T := (mul_le_mul_of_nonneg_right
        (show (j:ℝ≥0) ≤ (n:ℝ≥0) from Nat.cast_le.mpr hj) (show (0:ℝ≥0) ≤ δ from zero_le)).trans hn
      exact_mod_cast hjn
  have hstep {j : ℕ} (hj : j < n) : dist (a j) (a (j+1)) ≤ (δ:ℝ)*B := by
    let r := n-(j+1)
    have hr : (r:ℝ≥0)*δ ≤ T :=
      (mul_le_mul_of_nonneg_right (show (r:ℝ≥0) ≤ (n:ℝ≥0) from Nat.cast_le.mpr (Nat.sub_le _ _))
        (show (0:ℝ≥0) ≤ δ from zero_le)).trans hn
    have hreg := smooth_backwardTime hv hvB δ hφ hφB r (j+1)
    have hLip := hU δ r (j+1) hr
    have hst : (j:ℝ)*δ+(δ:ℝ) ∈ Icc 0 (T:ℝ) := by
      convert htime (j+1) (by omega) using 1
      push_cast
      ring
    have hh := he δ hδ ((j:ℝ)*δ) (htime j (by omega)) hst
      (backwardTime v δ φ r (j+1)) hreg.1 hreg.2 hLip.1 hLip.2.1 hLip.2.2
    have hnr : n-j = r+1 := by dsimp [r]; omega
    have htj : ((j+1:ℕ):ℝ)*(δ:ℝ) = (j:ℝ)*δ+(δ:ℝ) := by push_cast; ring
    rw [dist_comm,dist_eq_norm]
    dsimp only [a]
    rw [hnr,backwardTime,htj]
    exact hh
  have ht := dist_le_range_sum_of_dist_le (f := a) (d := fun _ => (δ:ℝ)*B) n hstep
  have hsum : (∑ _j ∈ Finset.range n, (δ:ℝ)*B) = (n:ℝ)*δ*B := by simp [mul_assoc]
  rw [hsum,dist_comm,dist_eq_norm] at ht
  simpa only [a,Nat.sub_self,Nat.sub_zero,backwardTime,Nat.cast_zero,zero_mul] using ht

end SharpWasserstein.WeakEvolution
