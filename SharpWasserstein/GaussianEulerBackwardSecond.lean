module

public import SharpWasserstein.Compat
public import SharpWasserstein.GaussianEulerBackward
public import SharpWasserstein.DerivativeCompositionBounds

@[expose] public section

/-! Second derivative bounds for the actual finite Gaussian Euler backward tests.
The recurrence is derived from the chain rule, with no backward PDE assumption. -/
noncomputable section
open MeasureTheory
open scoped Topology NNReal
namespace SharpWasserstein.BackwardEuler
open GaussianSharpness
variable {d N : ℕ}
local instance standardLabels_probability_second (k : ℕ) : IsProbabilityMeasure (standardLabels k) :=
  standardLabels_probability k

theorem fderiv_mean {b : Configuration d N → Configuration d N}
    (hb : Differentiable ℝ b) (δ : ℝ≥0) (x : Configuration d N) :
    fderiv ℝ (mean b δ) x = ContinuousLinearMap.id ℝ (Configuration d N) +
      (δ : ℝ) • fderiv ℝ b x :=
  ((hasFDerivAt_id x).add ((hb x).hasFDerivAt.const_smul (δ : ℝ))).fderiv

theorem lipschitz_fderiv_mean {b : Configuration d N → Configuration d N} {K₁ : ℝ≥0}
    (hb : Differentiable ℝ b) (hb₁ : LipschitzWith K₁ (fderiv ℝ b)) (δ : ℝ≥0) :
    LipschitzWith (δ*K₁) (fderiv ℝ (mean b δ)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, fderiv_mean hb, fderiv_mean hb, add_sub_add_left_eq_sub]
  have he : (δ : ℝ) • fderiv ℝ b x - (δ : ℝ) • fderiv ℝ b y =
      (δ : ℝ) • (fderiv ℝ b x - fderiv ℝ b y) := (smul_sub (δ : ℝ) _ _).symm
  rw [he, norm_smul, Real.norm_of_nonneg δ.coe_nonneg]
  simpa only [NNReal.coe_mul, dist_eq_norm, mul_assoc] using
    mul_le_mul_of_nonneg_left (hb₁.norm_sub_le x y) δ.coe_nonneg

theorem contDiff_two_step {b : Configuration d N → Configuration d N}
    (hb : ContDiff ℝ 2 b) (δ : ℝ≥0) {φ : Configuration d N → ℝ}
    (hφ : ContDiff ℝ 2 φ) {L L₁ : ℝ≥0} (hL : LipschitzWith L φ)
    (hL₁ : LipschitzWith L₁ (fderiv ℝ φ)) {C : ℝ} (hC : ∀ x, ‖φ x‖ ≤ C) :
    ContDiff ℝ 2 (step b δ φ) :=
  (NoiseAverage.contDiff_two_average _ _ (noise_stronglyMeasurable δ) hφ hL hL₁ hC).comp
    (contDiff_id.add (hb.const_smul (δ : ℝ)))

theorem lipschitz_fderiv_step {b : Configuration d N → Configuration d N}
    {K K₁ L L₁ : ℝ≥0} (hb : ContDiff ℝ 1 b) (hbL : LipschitzWith K b)
    (hb₁ : LipschitzWith K₁ (fderiv ℝ b)) (δ : ℝ≥0)
    {φ : Configuration d N → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hL : LipschitzWith L φ) (hL₁ : LipschitzWith L₁ (fderiv ℝ φ))
    {C : ℝ} (hC : ∀ x, ‖φ x‖ ≤ C) :
    LipschitzWith (L₁*(1+δ*K)^2 + L*(δ*K₁)) (fderiv ℝ (step b δ φ)) := by
  apply lipschitz_fderiv_comp
    (f := NoiseAverage.average (standardLabels (N*d+1)) (noise δ) φ) (g := mean b δ)
  · exact (NoiseAverage.contDiff_one_average _ _ (noise_stronglyMeasurable δ) hφ hL hC).differentiable (by norm_num)
  · exact (contDiff_id.add (hb.const_smul (δ : ℝ))).differentiable (by norm_num)
  · exact NoiseAverage.lipschitz_average _ _ (noise_stronglyMeasurable δ) hL hC
  · exact NoiseAverage.lipschitz_fderiv_average _ _ (noise_stronglyMeasurable δ) hφ hL hL₁ hC
  · exact lipschitz_mean hbL δ
  · exact lipschitz_fderiv_mean (hb.differentiable (by norm_num)) hb₁ δ

/-- Quantitative second derivative recurrence for finite backward Euler tests. -/
def secondBound (K K₁ L L₁ δ : ℝ≥0) : ℕ → ℝ≥0
  | 0 => L₁
  | n+1 => secondBound K K₁ L L₁ δ n * (1+δ*K)^2 +
      (L*(1+δ*K)^n)*(δ*K₁)

theorem lipschitz_fderiv_backward {b : Configuration d N → Configuration d N}
    {K K₁ L L₁ : ℝ≥0} (hb : ContDiff ℝ 1 b) (hbL : LipschitzWith K b)
    (hb₁ : LipschitzWith K₁ (fderiv ℝ b)) (δ : ℝ≥0)
    {φ : Configuration d N → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hL : LipschitzWith L φ) (hL₁ : LipschitzWith L₁ (fderiv ℝ φ))
    {C : ℝ} (hC : ∀ x, ‖φ x‖ ≤ C) (n : ℕ) :
    LipschitzWith (secondBound K K₁ L L₁ δ n) (fderiv ℝ (backward b δ φ n)) := by
  induction n with
  | zero => exact hL₁
  | succ n ih =>
    exact lipschitz_fderiv_step hb hbL hb₁ δ
      (contDiff_one_backward hb hbL δ hφ hL hC n)
      (lipschitz_backward hbL δ hL hC n) ih (norm_backward_le b δ hC n)

theorem contDiff_two_backward {b : Configuration d N → Configuration d N}
    {K K₁ L L₁ : ℝ≥0} (hb : ContDiff ℝ 2 b) (hbL : LipschitzWith K b)
    (hb₁ : LipschitzWith K₁ (fderiv ℝ b)) (δ : ℝ≥0)
    {φ : Configuration d N → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hL : LipschitzWith L φ) (hL₁ : LipschitzWith L₁ (fderiv ℝ φ))
    {C : ℝ} (hC : ∀ x, ‖φ x‖ ≤ C) (n : ℕ) : ContDiff ℝ 2 (backward b δ φ n) := by
  induction n with
  | zero => exact hφ
  | succ n ih =>
    exact contDiff_two_step hb δ ih (lipschitz_backward hbL δ hL hC n)
      (lipschitz_fderiv_backward (hb.of_le (by norm_num)) hbL hb₁ δ
        (hφ.of_le (by norm_num)) hL hL₁ hC n) (norm_backward_le b δ hC n)

theorem secondFDeriv_backward_norm_le {b : Configuration d N → Configuration d N}
    {K K₁ L L₁ : ℝ≥0} (hb : ContDiff ℝ 1 b) (hbL : LipschitzWith K b)
    (hb₁ : LipschitzWith K₁ (fderiv ℝ b)) (δ : ℝ≥0)
    {φ : Configuration d N → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hL : LipschitzWith L φ) (hL₁ : LipschitzWith L₁ (fderiv ℝ φ))
    {C : ℝ} (hC : ∀ x, ‖φ x‖ ≤ C) (n : ℕ) (x : Configuration d N) :
    ‖fderiv ℝ (fderiv ℝ (backward b δ φ n)) x‖ ≤ secondBound K K₁ L L₁ δ n :=
  norm_fderiv_le_of_lipschitz ℝ (lipschitz_fderiv_backward hb hbL hb₁ δ hφ hL hL₁ hC n)

theorem secondBound_le (K K₁ L L₁ δ : ℝ≥0) (n : ℕ) :
    secondBound K K₁ L L₁ δ n ≤ (L₁ + (n:ℝ≥0)*δ*K₁*L)*(1+δ*K)^(2*n) := by
  have ha : 1 ≤ 1+δ*K := le_add_of_nonneg_right (by positivity)
  induction n with
  | zero => simp [secondBound]
  | succ n ih =>
    have hp : (1+δ*K)^n ≤ (1+δ*K)^(2*(n+1)) :=
      pow_le_pow_right₀ ha (by omega)
    calc
      _ ≤ (L₁ + (n:ℝ≥0)*δ*K₁*L)*(1+δ*K)^(2*n)*(1+δ*K)^2 +
          (L*(1+δ*K)^n)*(δ*K₁) := by
            change secondBound K K₁ L L₁ δ n * (1+δ*K)^2 + _ ≤ _
            exact add_le_add (mul_le_mul_left ih _) le_rfl
      _ ≤ (L₁ + (n:ℝ≥0)*δ*K₁*L)*(1+δ*K)^(2*n)*(1+δ*K)^2 +
          (L*(1+δ*K)^(2*(n+1)))*(δ*K₁) := by gcongr
      _ = _ := by
        rw [mul_assoc, ← pow_add]
        have hi : 2*n+2 = 2*(n+1) := by omega
        rw [hi]
        push_cast
        ring

/-- Geometric Euler derivative growth is bounded uniformly at a fixed time horizon. -/
theorem eulerFactor_pow_le_exp (K δ : ℝ≥0) (n : ℕ) :
    ((1+δ*K : ℝ≥0)^n : ℝ) ≤ Real.exp ((n:ℝ)*δ*K) := by
  have he : (1+δ*K : ℝ) ≤ Real.exp ((δ:ℝ)*K) := by
    linarith [Real.add_one_le_exp ((δ:ℝ)*K)]
  calc
    _ ≤ (Real.exp ((δ:ℝ)*K))^n := by
      simp only [NNReal.coe_add, NNReal.coe_one, NNReal.coe_mul]
      exact pow_le_pow_left₀ (by positivity) he n
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem secondBound_le_exp (K K₁ L L₁ δ : ℝ≥0) (n : ℕ) :
    (secondBound K K₁ L L₁ δ n : ℝ) ≤
      ((L₁:ℝ)+(n:ℝ)*δ*K₁*L) * Real.exp (2*(n:ℝ)*δ*K) := by
  have h := eulerFactor_pow_le_exp K δ (2*n)
  have he : ((2*n:ℕ):ℝ)*δ*K = 2*(n:ℝ)*δ*K := by push_cast; ring
  rw [he] at h
  calc
    _ ≤ ((L₁:ℝ)+(n:ℝ)*δ*K₁*L)*(((1+δ*K : ℝ≥0)^(2*n)):ℝ) := by
      exact_mod_cast secondBound_le K K₁ L L₁ δ n
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)

end SharpWasserstein.BackwardEuler
