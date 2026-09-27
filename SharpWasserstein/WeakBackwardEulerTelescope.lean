import SharpWasserstein.WeakBackwardEulerStep
import SharpWasserstein.BackwardEulerUniform

/-! Discrete backward comparison for every actual weak solution. All tests
are constructed Gaussian Euler expectations; their uniform regularity and
the weak-equation consistency modulus have already been derived. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal ContDiff BigOperators
namespace SharpWasserstein.WeakEvolution
open WeightedTangent NoiseAverage BackwardEuler
variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  {b : Configuration d N → Configuration d N} {P : ℝ → Measure (Configuration d N)}
  (h : WeakEvolution (fun _ => b) P)
include h

theorem backward_telescope_error {K K₁ K₂ M L L₁ L₂ : ℝ≥0}
    (hb : ContDiff ℝ ∞ b) (hbB : AllDerivativesBounded b) (hbL : LipschitzWith K b)
    (hb₁ : LipschitzWith K₁ (fderiv ℝ b)) (hb₂ : LipschitzWith K₂ (fderiv ℝ (fderiv ℝ b)))
    (hM : ∀ x, ‖b x‖ ≤ M) {φ : Configuration d N → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφB : AllDerivativesBounded φ)
    (hL : LipschitzWith L φ) (hL₁ : LipschitzWith L₁ (fderiv ℝ φ))
    (hL₂ : LipschitzWith L₂ (fderiv ℝ (fderiv ℝ φ))) (T : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
      ∀ δ : ℝ≥0, ∀ n : ℕ, (n:ℝ≥0)*δ ≤ T → (δ:ℝ) < η →
      ‖(∫ x, φ x ∂P ((n:ℝ)*δ))-(∫ x, backward b δ φ n x ∂P 0)‖ ≤
        (n:ℝ)*δ*(ε+C*((M:ℝ)*δ+Real.sqrt (2*δ)*FrozenGaussian.noiseFirstMoment d N)) := by
  obtain ⟨A,_,hA⟩ := hφB.bounded
  have hb₂s : ContDiff ℝ 2 b := hb.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hφ₂s : ContDiff ℝ 2 φ := hφ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  obtain ⟨U,U₁,U₂,hU⟩ := uniform_backward_derivative_bounds hb₂s hbL hb₁ hb₂ hφ₂s hL hL₁ hL₂ hA T
  let C : ℝ := (N*d:ℕ)*(U₂:ℝ)+U₁*M
  refine ⟨C,by dsimp [C]; positivity,fun ε hε => ?_⟩
  obtain ⟨η,hη,he⟩ := uniform_backward_step_error h hbL hM (T:ℝ) U U₁ U₂ hε
  refine ⟨η,hη,fun δ n hn hδ => ?_⟩
  let a : ℕ → ℝ := fun j => ∫ x, backward b δ φ (n-j) x ∂P ((j:ℝ)*δ)
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
    have hreg := smooth_backward hb hbB δ hφ hφB r
    have hLip := hU δ r hr
    have hst : (j:ℝ)*δ+(δ:ℝ) ∈ Icc 0 (T:ℝ) := by
      convert htime (j+1) (by omega) using 1
      push_cast
      ring
    have hh := he δ hδ ((j:ℝ)*δ) (htime j (by omega)) hst
      (backward b δ φ r) hreg.1 hreg.2 hLip.1 hLip.2.1 hLip.2.2
    have hnr : n-j = r+1 := by dsimp [r]; omega
    have htj : ((j+1:ℕ):ℝ)*(δ:ℝ) = (j:ℝ)*δ+(δ:ℝ) := by push_cast; ring
    rw [dist_comm,dist_eq_norm]
    dsimp only [a]
    rw [hnr,backward,htj]
    exact hh
  have ht := dist_le_range_sum_of_dist_le (f := a) (d := fun _ => (δ:ℝ)*B) n hstep
  have hsum : (∑ _j ∈ Finset.range n, (δ:ℝ)*B) = (n:ℝ)*δ*B := by simp [mul_assoc]
  rw [hsum,dist_comm,dist_eq_norm] at ht
  simpa only [a,Nat.sub_self,Nat.sub_zero,backward,Nat.cast_zero,zero_mul] using ht

end SharpWasserstein.WeakEvolution
