import SharpWasserstein.BackwardEulerUniform

/-! Genuine backward Gaussian Euler tests with a different drift at each
time step. Their regularity bounds are uniform in the starting time and mesh. -/
noncomputable section
open MeasureTheory
open scoped NNReal ContDiff
namespace SharpWasserstein.BackwardEuler
open NoiseAverage
variable {d N : ℕ}

def backwardTime (v : ℝ → Configuration d N → Configuration d N) (δ : ℝ≥0)
    (φ : Configuration d N → ℝ) : ℕ → ℕ → Configuration d N → ℝ
  | 0, _ => φ
  | n+1, j => step (v ((j:ℝ)*δ)) δ (backwardTime v δ φ n (j+1))

theorem norm_backwardTime_le (v : ℝ → Configuration d N → Configuration d N) (δ : ℝ≥0)
    {φ : Configuration d N → ℝ} {C : ℝ} (hC : ∀ x, ‖φ x‖ ≤ C) (n j : ℕ)
    (x : Configuration d N) : ‖backwardTime v δ φ n j x‖ ≤ C := by
  induction n generalizing j x with
  | zero => exact hC x
  | succ n ih => exact norm_step_le (v ((j:ℝ)*δ)) δ (ih (j+1)) x

theorem smooth_backwardTime {v : ℝ → Configuration d N → Configuration d N}
    (hv : ∀ t, ContDiff ℝ ∞ (v t)) (hvB : ∀ t, AllDerivativesBounded (v t)) (δ : ℝ≥0)
    {φ : Configuration d N → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφB : AllDerivativesBounded φ)
    (n j : ℕ) : ContDiff ℝ ∞ (backwardTime v δ φ n j) ∧
      AllDerivativesBounded (backwardTime v δ φ n j) := by
  induction n generalizing j with
  | zero => exact ⟨hφ,hφB⟩
  | succ n ih => exact smooth_step (hv _) (hvB _) δ (ih (j+1)).1 (ih (j+1)).2

theorem backwardTime_derivative_bounds {v : ℝ → Configuration d N → Configuration d N}
    (hv : ∀ t, ContDiff ℝ ∞ (v t)) (hvB : ∀ t, AllDerivativesBounded (v t))
    {K K₁ K₂ L L₁ L₂ : ℝ≥0} (hvL : ∀ t, LipschitzWith K (v t))
    (hv₁ : ∀ t, LipschitzWith K₁ (fderiv ℝ (v t)))
    (hv₂ : ∀ t, LipschitzWith K₂ (fderiv ℝ (fderiv ℝ (v t)))) (δ : ℝ≥0)
    {φ : Configuration d N → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφB : AllDerivativesBounded φ)
    (hL : LipschitzWith L φ) (hL₁ : LipschitzWith L₁ (fderiv ℝ φ))
    (hL₂ : LipschitzWith L₂ (fderiv ℝ (fderiv ℝ φ))) (n j : ℕ) :
    LipschitzWith (L*(1+δ*K)^n) (backwardTime v δ φ n j) ∧
      LipschitzWith (secondBound K K₁ L L₁ δ n) (fderiv ℝ (backwardTime v δ φ n j)) ∧
      LipschitzWith (thirdBound K K₁ K₂ L L₁ L₂ δ n) (fderiv ℝ (fderiv ℝ (backwardTime v δ φ n j))) := by
  obtain ⟨C,_,hC⟩ := hφB.bounded
  induction n generalizing j with
  | zero => simpa only [backwardTime,pow_zero,mul_one,secondBound,thirdBound] using And.intro hL ⟨hL₁,hL₂⟩
  | succ n ih =>
    have hh := ih (j+1)
    have hs := (smooth_backwardTime hv hvB δ hφ hφB n (j+1)).1
    have hn := norm_backwardTime_le v δ hC n (j+1)
    refine ⟨?_,?_,?_⟩
    · simpa only [backwardTime,pow_succ,mul_assoc] using lipschitz_step (hvL _) δ hh.1 hn
    · exact lipschitz_fderiv_step
        ((hv _).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)) (hvL _) (hv₁ _) δ
        (hs.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)) hh.1 hh.2.1 hn
    · exact lipschitz_secondFDeriv_step
        ((hv _).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) (hvL _) (hv₁ _) (hv₂ _) δ
        (hs.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hh.1 hh.2.1 hh.2.2 hn

theorem uniform_backwardTime_derivative_bounds {v : ℝ → Configuration d N → Configuration d N}
    (hv : ∀ t, ContDiff ℝ ∞ (v t)) (hvB : ∀ t, AllDerivativesBounded (v t))
    {K K₁ K₂ L L₁ L₂ : ℝ≥0} (hvL : ∀ t, LipschitzWith K (v t))
    (hv₁ : ∀ t, LipschitzWith K₁ (fderiv ℝ (v t)))
    (hv₂ : ∀ t, LipschitzWith K₂ (fderiv ℝ (fderiv ℝ (v t))))
    {φ : Configuration d N → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφB : AllDerivativesBounded φ)
    (hL : LipschitzWith L φ) (hL₁ : LipschitzWith L₁ (fderiv ℝ φ))
    (hL₂ : LipschitzWith L₂ (fderiv ℝ (fderiv ℝ φ))) (T : ℝ≥0) :
    ∃ U U₁ U₂ : ℝ≥0, ∀ δ : ℝ≥0, ∀ n j : ℕ, (n:ℝ≥0)*δ ≤ T →
      LipschitzWith U (backwardTime v δ φ n j) ∧
      LipschitzWith U₁ (fderiv ℝ (backwardTime v δ φ n j)) ∧
      LipschitzWith U₂ (fderiv ℝ (fderiv ℝ (backwardTime v δ φ n j))) := by
  let U : ℝ≥0 := ⟨(L:ℝ)*Real.exp ((T:ℝ)*K),by positivity⟩
  let U₁ : ℝ≥0 := ⟨((L₁:ℝ)+(T:ℝ)*K₁*L)*Real.exp (2*(T:ℝ)*K),by positivity⟩
  let U₂ : ℝ≥0 := ⟨((L₂:ℝ)+3*(T:ℝ)*K₁*(L₁+(T:ℝ)*K₁*L)+(T:ℝ)*L*K₂)*
    Real.exp (3*(T:ℝ)*K),by positivity⟩
  refine ⟨U,U₁,U₂,fun δ n j hn => ?_⟩
  have hh := backwardTime_derivative_bounds hv hvB hvL hv₁ hv₂ δ hφ hφB hL hL₁ hL₂ n j
  have hn' : (n:ℝ)*(δ:ℝ) ≤ T := by exact_mod_cast hn
  refine ⟨?_,?_,?_⟩
  · apply hh.1.weaken
    change ((L*(1+δ*K)^n:ℝ≥0):ℝ) ≤ (U:ℝ)
    rw [NNReal.coe_mul]
    exact (mul_le_mul_of_nonneg_left (eulerFactor_pow_le_exp K δ n) L.coe_nonneg).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hn' K.coe_nonneg)) L.coe_nonneg)
  · apply hh.2.1.weaken
    change (secondBound K K₁ L L₁ δ n:ℝ) ≤ (U₁:ℝ)
    apply (secondBound_le_exp K K₁ L L₁ δ n).trans
    change ((L₁:ℝ)+(n:ℝ)*δ*K₁*L)*Real.exp (2*(n:ℝ)*δ*K) ≤
      ((L₁:ℝ)+(T:ℝ)*K₁*L)*Real.exp (2*(T:ℝ)*K)
    rw [mul_assoc 2 (n:ℝ) (δ:ℝ)]
    gcongr
  · apply hh.2.2.weaken
    change (thirdBound K K₁ K₂ L L₁ L₂ δ n:ℝ) ≤ (U₂:ℝ)
    apply (thirdBound_le_exp K K₁ K₂ L L₁ L₂ δ n).trans
    change ((L₂:ℝ)+3*(n:ℝ)*δ*K₁*(L₁+(n:ℝ)*δ*K₁*L)+(n:ℝ)*δ*L*K₂)*
        Real.exp (3*(n:ℝ)*δ*K) ≤
      ((L₂:ℝ)+3*(T:ℝ)*K₁*(L₁+(T:ℝ)*K₁*L)+(T:ℝ)*L*K₂)*Real.exp (3*(T:ℝ)*K)
    rw [mul_assoc 3 (n:ℝ) (δ:ℝ)]
    gcongr

end SharpWasserstein.BackwardEuler
