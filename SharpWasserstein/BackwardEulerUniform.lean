import SharpWasserstein.GaussianEulerBackwardThird
import SharpWasserstein.GaussianEulerBackwardSmooth

/-! Actual backward Gaussian Euler tests have common first-, second-, and
third-derivative Lipschitz bounds for every mesh and every remaining step
count inside a fixed time horizon. -/
noncomputable section
open MeasureTheory
open scoped NNReal ContDiff
namespace SharpWasserstein.BackwardEuler
open NoiseAverage
variable {d N : ℕ}

theorem uniform_backward_derivative_bounds {b : Configuration d N → Configuration d N}
    {K K₁ K₂ L L₁ L₂ : ℝ≥0} (hb : ContDiff ℝ 2 b) (hbL : LipschitzWith K b)
    (hb₁ : LipschitzWith K₁ (fderiv ℝ b)) (hb₂ : LipschitzWith K₂ (fderiv ℝ (fderiv ℝ b)))
    {φ : Configuration d N → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hL : LipschitzWith L φ) (hL₁ : LipschitzWith L₁ (fderiv ℝ φ))
    (hL₂ : LipschitzWith L₂ (fderiv ℝ (fderiv ℝ φ))) {C : ℝ} (hC : ∀ x, ‖φ x‖ ≤ C)
    (T : ℝ≥0) : ∃ U U₁ U₂ : ℝ≥0, ∀ δ : ℝ≥0, ∀ n : ℕ, (n:ℝ≥0)*δ ≤ T →
      LipschitzWith U (backward b δ φ n) ∧
      LipschitzWith U₁ (fderiv ℝ (backward b δ φ n)) ∧
      LipschitzWith U₂ (fderiv ℝ (fderiv ℝ (backward b δ φ n))) := by
  let U : ℝ≥0 := ⟨(L:ℝ)*Real.exp ((T:ℝ)*K),by positivity⟩
  let U₁ : ℝ≥0 := ⟨((L₁:ℝ)+(T:ℝ)*K₁*L)*Real.exp (2*(T:ℝ)*K),by positivity⟩
  let U₂ : ℝ≥0 := ⟨((L₂:ℝ)+3*(T:ℝ)*K₁*(L₁+(T:ℝ)*K₁*L)+(T:ℝ)*L*K₂)*
    Real.exp (3*(T:ℝ)*K),by positivity⟩
  refine ⟨U,U₁,U₂,fun δ n hn => ⟨?_,?_,?_⟩⟩
  · apply (lipschitz_backward hbL δ hL hC n).weaken
    change ((L*(1+δ*K)^n:ℝ≥0):ℝ) ≤ (U:ℝ)
    rw [NNReal.coe_mul]
    have hn' : (n:ℝ)*(δ:ℝ) ≤ T := by exact_mod_cast hn
    exact (mul_le_mul_of_nonneg_left (eulerFactor_pow_le_exp K δ n) L.coe_nonneg).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hn' K.coe_nonneg)) L.coe_nonneg)
  · apply (lipschitz_fderiv_backward (hb.of_le (by norm_num)) hbL hb₁ δ
      (hφ.of_le (by norm_num)) hL hL₁ hC n).weaken
    change (secondBound K K₁ L L₁ δ n:ℝ) ≤ (U₁:ℝ)
    apply (secondBound_le_exp K K₁ L L₁ δ n).trans
    change ((L₁:ℝ)+(n:ℝ)*δ*K₁*L)*Real.exp (2*(n:ℝ)*δ*K) ≤
      ((L₁:ℝ)+(T:ℝ)*K₁*L)*Real.exp (2*(T:ℝ)*K)
    have hn' : (n:ℝ)*(δ:ℝ) ≤ T := by exact_mod_cast hn
    rw [mul_assoc 2 (n:ℝ) (δ:ℝ)]
    gcongr
  · apply (lipschitz_secondFDeriv_backward hb hbL hb₁ hb₂ δ hφ hL hL₁ hL₂ hC n).weaken
    change (thirdBound K K₁ K₂ L L₁ L₂ δ n:ℝ) ≤ (U₂:ℝ)
    apply (thirdBound_le_exp K K₁ K₂ L L₁ L₂ δ n).trans
    change ((L₂:ℝ)+3*(n:ℝ)*δ*K₁*(L₁+(n:ℝ)*δ*K₁*L)+(n:ℝ)*δ*L*K₂)*
        Real.exp (3*(n:ℝ)*δ*K) ≤
      ((L₂:ℝ)+3*(T:ℝ)*K₁*(L₁+(T:ℝ)*K₁*L)+(T:ℝ)*L*K₂)*Real.exp (3*(T:ℝ)*K)
    have hn' : (n:ℝ)*(δ:ℝ) ≤ T := by exact_mod_cast hn
    rw [mul_assoc 3 (n:ℝ) (δ:ℝ)]
    gcongr

end SharpWasserstein.BackwardEuler
