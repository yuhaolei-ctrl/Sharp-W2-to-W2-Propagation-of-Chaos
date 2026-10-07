module

public import SharpWasserstein.Compat
public import SharpWasserstein.GaussianEulerBackwardSmooth

@[expose] public section

/-! Deterministic backward Euler tests for the genuine zero-diffusion continuity
operator. The maps are explicitly composed Euler characteristics; smoothness,
bounded derivatives, uniform derivative bounds, and consistency are conclusions. -/

noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ContDiff Topology
namespace SharpWasserstein.EulerianTransport
open NoiseAverage
variable {d N : ℕ}

/-- The actual first-order continuity operator, with no diffusion term. -/
def generator (b : Configuration d N → Configuration d N)
    (φ : Configuration d N → ℝ) (x : Configuration d N) : ℝ := fderiv ℝ φ x (b x)

/-- Pullback by one explicitly constructed deterministic Euler step. -/
def step (b : Configuration d N → Configuration d N) (δ : ℝ≥0)
    (φ : Configuration d N → ℝ) : Configuration d N → ℝ := φ ∘ BackwardEuler.mean b δ

/-- Actual finite backward Euler compositions for a time-dependent vector field. -/
def backward (v : ℝ → Configuration d N → Configuration d N) (δ : ℝ≥0)
    (φ : Configuration d N → ℝ) : ℕ → ℕ → Configuration d N → ℝ
  | 0, _ => φ
  | n+1, j => step (v ((j:ℝ)*δ)) δ (backward v δ φ n (j+1))

theorem norm_backward_le (v : ℝ → Configuration d N → Configuration d N) (δ : ℝ≥0)
    {φ : Configuration d N → ℝ} {C : ℝ} (hC : ∀ x, ‖φ x‖ ≤ C) (n j : ℕ)
    (x : Configuration d N) : ‖backward v δ φ n j x‖ ≤ C := by
  induction n generalizing j x with
  | zero => exact hC x
  | succ n ih => exact ih (j+1) _

theorem smooth_step {b : Configuration d N → Configuration d N}
    (hb : ContDiff ℝ ∞ b) (hB : AllDerivativesBounded b) (δ : ℝ≥0)
    {φ : Configuration d N → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφB : AllDerivativesBounded φ) :
    ContDiff ℝ ∞ (step b δ φ) ∧ AllDerivativesBounded (step b δ φ) := by
  have hm : ContDiff ℝ ∞ (BackwardEuler.mean b δ) := contDiff_id.add (hb.const_smul (δ:ℝ))
  exact ⟨hφ.comp hm, hφB.comp_of_fderiv hφ hm
    (BackwardEuler.allDerivativesBounded_fderiv_mean hb hB δ)⟩

theorem smooth_backward {v : ℝ → Configuration d N → Configuration d N}
    (hv : ∀ t, ContDiff ℝ ∞ (v t)) (hvB : ∀ t, AllDerivativesBounded (v t)) (δ : ℝ≥0)
    {φ : Configuration d N → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφB : AllDerivativesBounded φ)
    (n j : ℕ) : ContDiff ℝ ∞ (backward v δ φ n j) ∧ AllDerivativesBounded (backward v δ φ n j) := by
  induction n generalizing j with
  | zero => exact ⟨hφ, hφB⟩
  | succ n ih => exact smooth_step (hv _) (hvB _) δ (ih (j+1)).1 (ih (j+1)).2

theorem lipschitz_step {b : Configuration d N → Configuration d N} {K L : ℝ≥0}
    (hb : LipschitzWith K b) (δ : ℝ≥0) {φ : Configuration d N → ℝ}
    (hφ : LipschitzWith L φ) : LipschitzWith (L*(1+δ*K)) (step b δ φ) :=
  hφ.comp (BackwardEuler.lipschitz_mean hb δ)

theorem lipschitz_fderiv_step {b : Configuration d N → Configuration d N}
    {K K₁ L L₁ : ℝ≥0} (hb : Differentiable ℝ b) (hbL : LipschitzWith K b)
    (hb₁ : LipschitzWith K₁ (fderiv ℝ b)) (δ : ℝ≥0)
    {φ : Configuration d N → ℝ} (hφ : Differentiable ℝ φ)
    (hL : LipschitzWith L φ) (hL₁ : LipschitzWith L₁ (fderiv ℝ φ)) :
    LipschitzWith (L₁*(1+δ*K)^2+L*(δ*K₁)) (fderiv ℝ (step b δ φ)) :=
  lipschitz_fderiv_comp hφ (differentiable_id.add (hb.const_smul (δ:ℝ))) hL hL₁
    (BackwardEuler.lipschitz_mean hbL δ) (BackwardEuler.lipschitz_fderiv_mean hb hb₁ δ)

theorem backward_derivative_bounds {v : ℝ → Configuration d N → Configuration d N}
    (hv : ∀ t, ContDiff ℝ ∞ (v t)) (hvB : ∀ t, AllDerivativesBounded (v t))
    {K K₁ L L₁ : ℝ≥0} (hvL : ∀ t, LipschitzWith K (v t))
    (hv₁ : ∀ t, LipschitzWith K₁ (fderiv ℝ (v t))) (δ : ℝ≥0)
    {φ : Configuration d N → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφB : AllDerivativesBounded φ)
    (hL : LipschitzWith L φ) (hL₁ : LipschitzWith L₁ (fderiv ℝ φ)) (n j : ℕ) :
    LipschitzWith (L*(1+δ*K)^n) (backward v δ φ n j) ∧
      LipschitzWith (BackwardEuler.secondBound K K₁ L L₁ δ n) (fderiv ℝ (backward v δ φ n j)) := by
  induction n generalizing j with
  | zero => simpa only [backward, pow_zero, mul_one, BackwardEuler.secondBound] using And.intro hL hL₁
  | succ n ih =>
    have hh := ih (j+1)
    have hs := (smooth_backward hv hvB δ hφ hφB n (j+1)).1
    refine ⟨?_, ?_⟩
    · simpa only [backward, pow_succ, mul_assoc] using lipschitz_step (hvL _) δ hh.1
    · exact lipschitz_fderiv_step ((hv _).differentiable (by simp)) (hvL _) (hv₁ _) δ
        (hs.differentiable (by simp)) hh.1 hh.2

/-- Uniform first and second derivative bounds for all meshes and all remaining step counts. -/
theorem uniform_backward_derivative_bounds {v : ℝ → Configuration d N → Configuration d N}
    (hv : ∀ t, ContDiff ℝ ∞ (v t)) (hvB : ∀ t, AllDerivativesBounded (v t))
    {K K₁ L L₁ : ℝ≥0} (hvL : ∀ t, LipschitzWith K (v t))
    (hv₁ : ∀ t, LipschitzWith K₁ (fderiv ℝ (v t)))
    {φ : Configuration d N → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφB : AllDerivativesBounded φ)
    (hL : LipschitzWith L φ) (hL₁ : LipschitzWith L₁ (fderiv ℝ φ)) (T : ℝ≥0) :
    ∃ U U₁ : ℝ≥0, ∀ δ : ℝ≥0, ∀ n j : ℕ, (n:ℝ≥0)*δ ≤ T →
      LipschitzWith U (backward v δ φ n j) ∧
      LipschitzWith U₁ (fderiv ℝ (backward v δ φ n j)) := by
  let U : ℝ≥0 := ⟨(L:ℝ)*Real.exp ((T:ℝ)*K), by positivity⟩
  let U₁ : ℝ≥0 := ⟨((L₁:ℝ)+(T:ℝ)*K₁*L)*Real.exp (2*(T:ℝ)*K), by positivity⟩
  refine ⟨U, U₁, fun δ n j hn => ?_⟩
  have hh := backward_derivative_bounds hv hvB hvL hv₁ δ hφ hφB hL hL₁ n j
  have hn' : (n:ℝ)*(δ:ℝ) ≤ T := by exact_mod_cast hn
  refine ⟨?_, ?_⟩
  · apply hh.1.weaken
    change ((L*(1+δ*K)^n:ℝ≥0):ℝ) ≤ (U:ℝ)
    rw [NNReal.coe_mul]
    exact (mul_le_mul_of_nonneg_left (BackwardEuler.eulerFactor_pow_le_exp K δ n) L.coe_nonneg).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right hn' K.coe_nonneg)) L.coe_nonneg)
  · apply hh.2.weaken
    change (BackwardEuler.secondBound K K₁ L L₁ δ n:ℝ) ≤ (U₁:ℝ)
    apply (BackwardEuler.secondBound_le_exp K K₁ L L₁ δ n).trans
    change ((L₁:ℝ)+(n:ℝ)*δ*K₁*L)*Real.exp (2*(n:ℝ)*δ*K) ≤
      ((L₁:ℝ)+(T:ℝ)*K₁*L)*Real.exp (2*(T:ℝ)*K)
    rw [mul_assoc 2 (n:ℝ) (δ:ℝ)]
    gcongr

/-- A genuine first-order Taylor remainder estimate, from the actual derivative. -/
theorem taylor_error_le {φ : Configuration d N → ℝ} {L₁ : ℝ≥0}
    (hφ : Differentiable ℝ φ) (hL₁ : LipschitzWith L₁ (fderiv ℝ φ))
    (x y : Configuration d N) :
    ‖φ y - φ x - fderiv ℝ φ x (y-x)‖ ≤ (L₁:ℝ)*‖y-x‖^2 := by
  have hh := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le'
    (f := φ) (φ := fderiv ℝ φ x) (fun z _ => hφ z)
    (fun z hz => (hL₁.norm_sub_le z x).trans
      (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hz) L₁.coe_nonneg))
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simpa only [pow_two, mul_assoc] using hh

/-- One actual Euler pullback approximates the continuity operator with quadratic mesh error. -/
theorem step_error_le {b : Configuration d N → Configuration d N} {M L₁ : ℝ≥0}
    (hM : ∀ x, ‖b x‖ ≤ M) (δ : ℝ≥0) {φ : Configuration d N → ℝ}
    (hφ : Differentiable ℝ φ) (hL₁ : LipschitzWith L₁ (fderiv ℝ φ)) (x : Configuration d N) :
    ‖step b δ φ x - φ x - (δ:ℝ)*generator b φ x‖ ≤ (L₁:ℝ)*(δ:ℝ)^2*(M:ℝ)^2 := by
  have h := taylor_error_le hφ hL₁ x (BackwardEuler.mean b δ x)
  simp only [BackwardEuler.mean, add_sub_cancel_left, map_smul, smul_eq_mul,
    norm_smul, Real.norm_of_nonneg δ.coe_nonneg] at h
  exact h.trans (by
    change (L₁:ℝ)*((δ:ℝ)*‖b x‖)^2 ≤ _
    have hh := pow_le_pow_left₀ (norm_nonneg (b x)) (hM x) 2
    nlinarith [mul_le_mul_of_nonneg_left hh (show 0 ≤ (L₁:ℝ)*(δ:ℝ)^2 by positivity)])

end SharpWasserstein.EulerianTransport
