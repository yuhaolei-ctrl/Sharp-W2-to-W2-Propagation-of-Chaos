module

public import SharpWasserstein.Compat
public import SharpWasserstein.GaussianEulerBackwardSecond
public import SharpWasserstein.DerivativeCompositionThird

@[expose] public section

/-! Third-order regularity and derivative bounds of genuine Gaussian Euler
backward tests, derived by averaging and the actual chain rule. -/
noncomputable section
open MeasureTheory
open scoped Topology NNReal
namespace SharpWasserstein.BackwardEuler
open GaussianSharpness
variable {d N : ℕ}
local instance standardLabels_probability_third (k : ℕ) : IsProbabilityMeasure (standardLabels k) :=
  standardLabels_probability k

theorem secondFDeriv_mean {b : Configuration d N → Configuration d N}
    (hb : ContDiff ℝ 2 b) (δ : ℝ≥0) :
    fderiv ℝ (fderiv ℝ (mean b δ)) = fun x => (δ:ℝ) • fderiv ℝ (fderiv ℝ b) x := by
  have he : fderiv ℝ (mean b δ) = fun x => ContinuousLinearMap.id ℝ (Configuration d N) +
      (δ : ℝ) • fderiv ℝ b x := funext (fderiv_mean (hb.differentiable (by norm_num)) δ)
  rw [he]
  funext x
  have hd := ((hb.fderiv_right (by norm_num) : ContDiff ℝ 1 _).differentiable (by norm_num) x).hasFDerivAt
  exact ((hd.const_smul (δ:ℝ)).const_add (ContinuousLinearMap.id ℝ (Configuration d N))).fderiv

theorem lipschitz_secondFDeriv_mean {b : Configuration d N → Configuration d N} {K₂ : ℝ≥0}
    (hb : ContDiff ℝ 2 b) (hb₂ : LipschitzWith K₂ (fderiv ℝ (fderiv ℝ b))) (δ : ℝ≥0) :
    LipschitzWith (δ*K₂) (fderiv ℝ (fderiv ℝ (mean b δ))) := by
  rw [secondFDeriv_mean hb δ]
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  have he := (smul_sub (δ:ℝ) (fderiv ℝ (fderiv ℝ b) x) (fderiv ℝ (fderiv ℝ b) y)).symm
  rw [he]
  apply (ContinuousLinearMap.opNorm_smul_le (δ:ℝ) _).trans
  simpa only [Real.norm_of_nonneg δ.coe_nonneg, NNReal.coe_mul, mul_assoc, dist_eq_norm] using
    mul_le_mul_of_nonneg_left (hb₂.norm_sub_le x y) δ.coe_nonneg

theorem contDiff_three_step {b : Configuration d N → Configuration d N}
    (hb : ContDiff ℝ 3 b) (δ : ℝ≥0) {φ : Configuration d N → ℝ}
    (hφ : ContDiff ℝ 3 φ) {L L₁ L₂ : ℝ≥0} (hL : LipschitzWith L φ)
    (hL₁ : LipschitzWith L₁ (fderiv ℝ φ)) (hL₂ : LipschitzWith L₂ (fderiv ℝ (fderiv ℝ φ)))
    {C : ℝ} (hC : ∀ x, ‖φ x‖ ≤ C) : ContDiff ℝ 3 (step b δ φ) :=
  (NoiseAverage.contDiff_three_average _ _ (noise_stronglyMeasurable δ) hφ hL hL₁ hL₂ hC).comp
    (contDiff_id.add (hb.const_smul (δ : ℝ)))

theorem lipschitz_secondFDeriv_step {b : Configuration d N → Configuration d N}
    {K K₁ K₂ L L₁ L₂ : ℝ≥0} (hb : ContDiff ℝ 2 b) (hbL : LipschitzWith K b)
    (hb₁ : LipschitzWith K₁ (fderiv ℝ b)) (hb₂ : LipschitzWith K₂ (fderiv ℝ (fderiv ℝ b)))
    (δ : ℝ≥0) {φ : Configuration d N → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hL : LipschitzWith L φ) (hL₁ : LipschitzWith L₁ (fderiv ℝ φ))
    (hL₂ : LipschitzWith L₂ (fderiv ℝ (fderiv ℝ φ))) {C : ℝ} (hC : ∀ x, ‖φ x‖ ≤ C) :
    LipschitzWith (L₂*(1+δ*K)^3 + 3*L₁*(1+δ*K)*(δ*K₁) + L*(δ*K₂))
      (fderiv ℝ (fderiv ℝ (step b δ φ))) := by
  apply lipschitz_secondFDeriv_comp
    (f := NoiseAverage.average (standardLabels (N*d+1)) (noise δ) φ) (g := mean b δ)
  · exact NoiseAverage.contDiff_two_average _ _ (noise_stronglyMeasurable δ) hφ hL hL₁ hC
  · exact contDiff_id.add (hb.const_smul (δ : ℝ))
  · exact NoiseAverage.lipschitz_average _ _ (noise_stronglyMeasurable δ) hL hC
  · exact NoiseAverage.lipschitz_fderiv_average _ _ (noise_stronglyMeasurable δ)
      (hφ.of_le (by norm_num)) hL hL₁ hC
  · exact NoiseAverage.lipschitz_secondFDeriv_average _ _ (noise_stronglyMeasurable δ) hφ hL hL₁ hL₂ hC
  · exact lipschitz_mean hbL δ
  · exact lipschitz_fderiv_mean (hb.differentiable (by norm_num)) hb₁ δ
  · exact lipschitz_secondFDeriv_mean hb hb₂ δ

def thirdBound (K K₁ K₂ L L₁ L₂ δ : ℝ≥0) : ℕ → ℝ≥0
  | 0 => L₂
  | n+1 => thirdBound K K₁ K₂ L L₁ L₂ δ n*(1+δ*K)^3 +
      3*(secondBound K K₁ L L₁ δ n)*(1+δ*K)*(δ*K₁) + (L*(1+δ*K)^n)*(δ*K₂)

theorem lipschitz_secondFDeriv_backward {b : Configuration d N → Configuration d N}
    {K K₁ K₂ L L₁ L₂ : ℝ≥0} (hb : ContDiff ℝ 2 b) (hbL : LipschitzWith K b)
    (hb₁ : LipschitzWith K₁ (fderiv ℝ b)) (hb₂ : LipschitzWith K₂ (fderiv ℝ (fderiv ℝ b)))
    (δ : ℝ≥0) {φ : Configuration d N → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hL : LipschitzWith L φ) (hL₁ : LipschitzWith L₁ (fderiv ℝ φ))
    (hL₂ : LipschitzWith L₂ (fderiv ℝ (fderiv ℝ φ))) {C : ℝ} (hC : ∀ x, ‖φ x‖ ≤ C) (n : ℕ) :
    LipschitzWith (thirdBound K K₁ K₂ L L₁ L₂ δ n)
      (fderiv ℝ (fderiv ℝ (backward b δ φ n))) := by
  induction n with
  | zero => exact hL₂
  | succ n ih =>
    exact lipschitz_secondFDeriv_step hb hbL hb₁ hb₂ δ
      (contDiff_two_backward hb hbL hb₁ δ hφ hL hL₁ hC n)
      (lipschitz_backward hbL δ hL hC n)
      (lipschitz_fderiv_backward (hb.of_le (by norm_num)) hbL hb₁ δ
        (hφ.of_le (by norm_num)) hL hL₁ hC n) ih (norm_backward_le b δ hC n)

theorem contDiff_three_backward {b : Configuration d N → Configuration d N}
    {K K₁ K₂ L L₁ L₂ : ℝ≥0} (hb : ContDiff ℝ 3 b) (hbL : LipschitzWith K b)
    (hb₁ : LipschitzWith K₁ (fderiv ℝ b)) (hb₂ : LipschitzWith K₂ (fderiv ℝ (fderiv ℝ b)))
    (δ : ℝ≥0) {φ : Configuration d N → ℝ} (hφ : ContDiff ℝ 3 φ)
    (hL : LipschitzWith L φ) (hL₁ : LipschitzWith L₁ (fderiv ℝ φ))
    (hL₂ : LipschitzWith L₂ (fderiv ℝ (fderiv ℝ φ))) {C : ℝ} (hC : ∀ x, ‖φ x‖ ≤ C) (n : ℕ) :
    ContDiff ℝ 3 (backward b δ φ n) := by
  induction n with
  | zero => exact hφ
  | succ n ih =>
    exact contDiff_three_step hb δ ih (lipschitz_backward hbL δ hL hC n)
      (lipschitz_fderiv_backward (hb.of_le (by norm_num)) hbL hb₁ δ
        (hφ.of_le (by norm_num)) hL hL₁ hC n)
      (lipschitz_secondFDeriv_backward (hb.of_le (by norm_num)) hbL hb₁ hb₂ δ
        (hφ.of_le (by norm_num)) hL hL₁ hL₂ hC n) (norm_backward_le b δ hC n)

/-- A polynomial-exponential bound uniform when the total elapsed time is fixed. -/
theorem thirdBound_le (K K₁ K₂ L L₁ L₂ δ : ℝ≥0) (n : ℕ) :
    thirdBound K K₁ K₂ L L₁ L₂ δ n ≤
      (L₂ + 3*(n:ℝ≥0)*δ*K₁*(L₁+(n:ℝ≥0)*δ*K₁*L) + (n:ℝ≥0)*δ*L*K₂)*(1+δ*K)^(3*n) := by
  have ha : 1 ≤ 1+δ*K := le_add_of_nonneg_right (by positivity)
  induction n with
  | zero => simp [thirdBound]
  | succ n ih =>
    have hp₁ : (1+δ*K)^(2*n+1) ≤ (1+δ*K)^(3*(n+1)) :=
      pow_le_pow_right₀ ha (by omega)
    have hp₂ : (1+δ*K)^n ≤ (1+δ*K)^(3*(n+1)) := pow_le_pow_right₀ ha (by omega)
    let A := L₂+3*(n:ℝ≥0)*δ*K₁*(L₁+(n:ℝ≥0)*δ*K₁*L)+(n:ℝ≥0)*δ*L*K₂
    have hfirst : A*(1+δ*K)^(3*n)*(1+δ*K)^3 = A*(1+δ*K)^(3*(n+1)) := by
      rw [mul_assoc, ← pow_add]
      congr 2
    have hmid : 3*((L₁+(n:ℝ≥0)*δ*K₁*L)*(1+δ*K)^(2*n))*(1+δ*K)*(δ*K₁) =
        (3*(L₁+(n:ℝ≥0)*δ*K₁*L)*(δ*K₁))*(1+δ*K)^(2*n+1) := by
      rw [pow_succ]
      ring
    have hcoef : A+3*(L₁+(n:ℝ≥0)*δ*K₁*L)*(δ*K₁)+L*(δ*K₂) ≤
        L₂+3*((n+1:ℕ):ℝ≥0)*δ*K₁*(L₁+((n+1:ℕ):ℝ≥0)*δ*K₁*L)+((n+1:ℕ):ℝ≥0)*δ*L*K₂ := by
      dsimp [A]
      push_cast
      nlinarith [show 0 ≤ 3*(n:ℝ≥0)*δ^2*K₁^2*L by positivity,
        show 0 ≤ 3*δ^2*K₁^2*L by positivity]
    calc
      _ ≤ A*(1+δ*K)^(3*n)*(1+δ*K)^3 +
          3*((L₁+(n:ℝ≥0)*δ*K₁*L)*(1+δ*K)^(2*n))*(1+δ*K)*(δ*K₁) +
          (L*(1+δ*K)^n)*(δ*K₂) := by
        unfold thirdBound
        gcongr
        exact secondBound_le K K₁ L L₁ δ n
      _ = A*(1+δ*K)^(3*(n+1)) +
          (3*(L₁+(n:ℝ≥0)*δ*K₁*L)*(δ*K₁))*(1+δ*K)^(2*n+1) +
          (L*(δ*K₂))*(1+δ*K)^n := by rw [hfirst,hmid]; ring
      _ ≤ (A+3*(L₁+(n:ℝ≥0)*δ*K₁*L)*(δ*K₁)+L*(δ*K₂))*(1+δ*K)^(3*(n+1)) := by
        calc
          _ ≤ A*(1+δ*K)^(3*(n+1)) +
              (3*(L₁+(n:ℝ≥0)*δ*K₁*L)*(δ*K₁))*(1+δ*K)^(3*(n+1)) +
              (L*(δ*K₂))*(1+δ*K)^(3*(n+1)) := by gcongr
          _ = _ := by ring
      _ ≤ _ := mul_le_mul_left hcoef _

theorem thirdBound_le_exp (K K₁ K₂ L L₁ L₂ δ : ℝ≥0) (n : ℕ) :
    (thirdBound K K₁ K₂ L L₁ L₂ δ n : ℝ) ≤
      ((L₂:ℝ)+3*(n:ℝ)*δ*K₁*(L₁+(n:ℝ)*δ*K₁*L)+(n:ℝ)*δ*L*K₂)*
        Real.exp (3*(n:ℝ)*δ*K) := by
  have he := eulerFactor_pow_le_exp K δ (3*n)
  have hi : ((3*n:ℕ):ℝ)*δ*K = 3*(n:ℝ)*δ*K := by push_cast; ring
  rw [hi] at he
  calc
    _ ≤ ((L₂:ℝ)+3*(n:ℝ)*δ*K₁*(L₁+(n:ℝ)*δ*K₁*L)+(n:ℝ)*δ*L*K₂)*
        (((1+δ*K:ℝ≥0)^(3*n)):ℝ) := by exact_mod_cast thirdBound_le K K₁ K₂ L L₁ L₂ δ n
    _ ≤ _ := mul_le_mul_of_nonneg_left he (by positivity)

end SharpWasserstein.BackwardEuler
