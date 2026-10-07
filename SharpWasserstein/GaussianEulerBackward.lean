module

public import SharpWasserstein.Compat
public import SharpWasserstein.BoundedNoiseAverage
public import SharpWasserstein.FrozenGaussianLaw

@[expose] public section

/-! Actual backward Gaussian Euler tests. These are the integrals of the real
Gaussian transition law, not an assumed backward equation. The uniform value,
Lipschitz and first-derivative bounds are proved for every finite number of steps. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal
namespace SharpWasserstein.BackwardEuler
open GaussianSharpness
variable {d N : ℕ}
local instance standardLabels_probability_local (k : ℕ) : IsProbabilityMeasure (standardLabels k) :=
  standardLabels_probability k

def noise (δ : ℝ≥0) (ω : Fin (N*d+1) → ℝ) : Configuration d N :=
  Real.sqrt (2*(δ : ℝ)) • FrozenGaussian.noiseMap d N ω

theorem noise_stronglyMeasurable (δ : ℝ≥0) : StronglyMeasurable (noise (d := d) (N := N) δ) := by
  apply Continuous.stronglyMeasurable
  unfold noise
  fun_prop

def mean (b : Configuration d N → Configuration d N) (δ : ℝ≥0) (x : Configuration d N) : Configuration d N :=
  x + (δ : ℝ) • b x

def step (b : Configuration d N → Configuration d N) (δ : ℝ≥0)
    (φ : Configuration d N → ℝ) (x : Configuration d N) : ℝ :=
  NoiseAverage.average (standardLabels (N*d+1)) (noise δ) φ (mean b δ x)

def backward (b : Configuration d N → Configuration d N) (δ : ℝ≥0)
    (φ : Configuration d N → ℝ) : ℕ → Configuration d N → ℝ
  | 0 => φ
  | n+1 => step b δ (backward b δ φ n)

/-- Each backward step is exactly integration against the genuine Gaussian Euler transition. -/
theorem step_eq_integral_transitionLaw (b : Configuration d N → Configuration d N)
    (δ : ℝ≥0) {φ : Configuration d N → ℝ} (hφ : Continuous φ) (x : Configuration d N) :
    step b δ φ x = ∫ y, φ y ∂FrozenGaussian.transitionLaw x (b x) δ := by
  rw [FrozenGaussian.integral_transitionLaw hφ]
  have hc : (Real.sqrt (2*(δ : ℝ)))^2 / 2 = δ := by
    rw [Real.sq_sqrt (by positivity)]
    ring
  simp only [step, NoiseAverage.average, mean, noise, FrozenGaussian.timeExpectation,
    FrozenGaussian.expectation, FrozenGaussian.label, hc]

theorem norm_step_le (b : Configuration d N → Configuration d N) (δ : ℝ≥0)
    {φ : Configuration d N → ℝ} {C : ℝ} (hφ : ∀ x, ‖φ x‖ ≤ C) (x : Configuration d N) :
    ‖step b δ φ x‖ ≤ C := NoiseAverage.norm_average_le _ _ hφ _

theorem norm_backward_le (b : Configuration d N → Configuration d N) (δ : ℝ≥0)
    {φ : Configuration d N → ℝ} {C : ℝ} (hφ : ∀ x, ‖φ x‖ ≤ C) (n : ℕ) (x : Configuration d N) :
    ‖backward b δ φ n x‖ ≤ C := by
  induction n generalizing x with
  | zero => exact hφ x
  | succ n ih => exact norm_step_le b δ ih x

theorem lipschitz_mean {b : Configuration d N → Configuration d N} {K : ℝ≥0}
    (hb : LipschitzWith K b) (δ : ℝ≥0) : LipschitzWith (1 + δ*K) (mean b δ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  simp only [mean, NNReal.coe_add, NNReal.coe_one, NNReal.coe_mul]
  rw [add_sub_add_comm, ← smul_sub, dist_eq_norm]
  calc
    _ ≤ ‖x-y‖ + ‖(δ : ℝ) • (b x-b y)‖ := norm_add_le _ _
    _ = ‖x-y‖ + (δ : ℝ) * ‖b x-b y‖ := by rw [norm_smul, Real.norm_of_nonneg δ.coe_nonneg]
    _ ≤ ‖x-y‖ + (δ : ℝ) * ((K : ℝ) * ‖x-y‖) :=
      add_le_add_right (mul_le_mul_of_nonneg_left (hb.norm_sub_le x y) δ.coe_nonneg) _
    _ = _ := by ring

theorem lipschitz_step {b : Configuration d N → Configuration d N} {K L : ℝ≥0}
    (hb : LipschitzWith K b) (δ : ℝ≥0) {φ : Configuration d N → ℝ}
    (hφ : LipschitzWith L φ) {C : ℝ} (hC : ∀ x, ‖φ x‖ ≤ C) :
    LipschitzWith (L * (1 + δ*K)) (step b δ φ) :=
  (NoiseAverage.lipschitz_average _ _ (noise_stronglyMeasurable δ) hφ hC).comp (lipschitz_mean hb δ)

/-- The Lipschitz bound grows geometrically with the correct Euler step factor. -/
theorem lipschitz_backward {b : Configuration d N → Configuration d N} {K L : ℝ≥0}
    (hb : LipschitzWith K b) (δ : ℝ≥0) {φ : Configuration d N → ℝ}
    (hφ : LipschitzWith L φ) {C : ℝ} (hC : ∀ x, ‖φ x‖ ≤ C) (n : ℕ) :
    LipschitzWith (L * (1 + δ*K)^n) (backward b δ φ n) := by
  induction n with
  | zero => simpa only [backward, pow_zero, mul_one] using hφ
  | succ n ih =>
    simpa only [backward, pow_succ, mul_assoc] using lipschitz_step hb δ ih (norm_backward_le b δ hC n)

/-- Differentiating the genuine Gaussian expectation gives the exact backward Euler derivative. -/
theorem hasFDerivAt_step {b : Configuration d N → Configuration d N} {K L : ℝ≥0}
    (hb : ContDiff ℝ 1 b) (_hbL : LipschitzWith K b) (δ : ℝ≥0)
    {φ : Configuration d N → ℝ} (hφ : ContDiff ℝ 1 φ) (hφL : LipschitzWith L φ)
    {C : ℝ} (hC : ∀ x, ‖φ x‖ ≤ C) (x : Configuration d N) :
    HasFDerivAt (step b δ φ)
      ((∫ ω, fderiv ℝ φ (mean b δ x + noise δ ω) ∂standardLabels (N*d+1)).comp
        (ContinuousLinearMap.id ℝ (Configuration d N) + (δ : ℝ) • fderiv ℝ b x)) x := by
  have hm := (hasFDerivAt_id x).add (((hb.differentiable (by norm_num)) x).hasFDerivAt.const_smul (δ : ℝ))
  exact (NoiseAverage.hasFDerivAt_average _ _ (noise_stronglyMeasurable δ) hφ hφL hC _).comp x hm

theorem contDiff_one_step {b : Configuration d N → Configuration d N} {K L : ℝ≥0}
    (hb : ContDiff ℝ 1 b) (_hbL : LipschitzWith K b) (δ : ℝ≥0)
    {φ : Configuration d N → ℝ} (hφ : ContDiff ℝ 1 φ) (hφL : LipschitzWith L φ)
    {C : ℝ} (hC : ∀ x, ‖φ x‖ ≤ C) : ContDiff ℝ 1 (step b δ φ) :=
  (NoiseAverage.contDiff_one_average _ _ (noise_stronglyMeasurable δ) hφ hφL hC).comp
    (contDiff_id.add (hb.const_smul (δ : ℝ)))

theorem contDiff_one_backward {b : Configuration d N → Configuration d N} {K L : ℝ≥0}
    (hb : ContDiff ℝ 1 b) (hbL : LipschitzWith K b) (δ : ℝ≥0)
    {φ : Configuration d N → ℝ} (hφ : ContDiff ℝ 1 φ) (hφL : LipschitzWith L φ)
    {C : ℝ} (hC : ∀ x, ‖φ x‖ ≤ C) (n : ℕ) : ContDiff ℝ 1 (backward b δ φ n) := by
  induction n with
  | zero => exact hφ
  | succ n ih =>
    simpa only [backward] using contDiff_one_step hb hbL δ ih
      (lipschitz_backward hbL δ hφL hC n) (norm_backward_le b δ hC n)

/-- The derivative norm estimate is about the actual Fréchet derivative of the constructed test. -/
theorem fderiv_backward_norm_le {b : Configuration d N → Configuration d N} {K L : ℝ≥0}
    (hb : LipschitzWith K b) (δ : ℝ≥0) {φ : Configuration d N → ℝ}
    (hφ : LipschitzWith L φ) {C : ℝ} (hC : ∀ x, ‖φ x‖ ≤ C) (n : ℕ) (x : Configuration d N) :
    ‖fderiv ℝ (backward b δ φ n) x‖ ≤ (L * (1+δ*K)^n : ℝ≥0) :=
  norm_fderiv_le_of_lipschitz ℝ (lipschitz_backward hb δ hφ hC n)

end SharpWasserstein.BackwardEuler
