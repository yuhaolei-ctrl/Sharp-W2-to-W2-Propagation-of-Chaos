import SharpWasserstein.WeightedIntegralSquare
import SharpWasserstein.WeightedConvolutionSmooth
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Adding a stationary positive density to an actual convolved density and
flux. The denominator is proved positive, the flux is preserved exactly, and
the Euclidean quadratic action decreases. Compact support of the flux gives
global bounds for every derivative of the resulting smooth velocity. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff NNReal
namespace SharpWasserstein.RoughEulerianSmoothing

universe u
variable {Ω : Type*} {E F : Type u} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Weighted Cauchy--Schwarz remains valid after a strictly positive mass with
zero velocity is added. No positivity of the original convolution is assumed. -/
theorem weighted_norm_integral_sq_le_add {μ : Measure Ω} {w : Ω → ℝ} {v : Ω → E}
    (hw : Integrable w μ) (hwn : Integrable (fun z => w z * ‖v z‖) μ)
    (hwn₂ : Integrable (fun z => w z * ‖v z‖^2) μ)
    (hw₀ : ∀ᵐ z ∂μ, 0 ≤ w z) {c : ℝ} (hc : 0 < c) :
    ‖∫ z, w z • v z ∂μ‖^2 / ((∫ z, w z ∂μ) + c) ≤
      ∫ z, w z * ‖v z‖^2 ∂μ := by
  have hZ : 0 ≤ ∫ z, w z ∂μ := integral_nonneg_of_ae hw₀
  rcases hZ.eq_or_lt with hzero | hpos
  · have hwzero := (integral_eq_zero_iff_of_nonneg_ae hw₀ hw).mp hzero.symm
    have hflux : (∫ z, w z • v z ∂μ) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hwzero] with z hz
      simp only [Pi.zero_apply] at hz
      simp only [hz, zero_smul, Pi.zero_apply]
    rw [hflux, norm_zero, zero_pow (by norm_num : 2 ≠ 0), zero_div]
    exact integral_nonneg_of_ae (hw₀.mono fun z hz => mul_nonneg hz (sq_nonneg _))
  · exact (div_le_div_of_nonneg_left (sq_nonneg _) hpos (le_add_of_nonneg_right hc.le)).trans
      (WeightedIntegralSquare.weighted_norm_integral_sq_le hw hwn hwn₂ hw₀ hpos)

/-- Smooth compactly supported functions have genuine global bounds on all
iterated derivatives. This is also applied to the constructed velocity. -/
theorem allDerivativesBounded_of_compact {f : E → F}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    NoiseAverage.AllDerivativesBounded f := by
  intro n
  obtain ⟨C,hC⟩ := (hc.iteratedFDeriv (𝕜 := ℝ) n).exists_bound_of_continuous
    (ContDiff.continuous_iteratedFDeriv
      (by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top)) hf)
  exact ⟨max C 0, le_max_right _ _, fun x => (hC x).trans (le_max_left _ _)⟩

def floorDensity (a : ℝ) (ρ g : E → ℝ) (x : E) : ℝ := a * ρ x + g x

def floorVelocity (a : ℝ) (ρ g : E → ℝ) (j : E → F) (x : E) : F :=
  (floorDensity a ρ g x)⁻¹ • (a • j x)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem floorDensity_pos {a : ℝ} (ha : 0 ≤ a) {ρ g : E → ℝ}
    (hρ : ∀ x, 0 ≤ ρ x) (hg : ∀ x, 0 < g x) (x : E) :
    0 < floorDensity a ρ g x := add_pos_of_nonneg_of_pos (mul_nonneg ha (hρ x)) (hg x)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem floorVelocity_flux {a : ℝ} (ha : 0 ≤ a) {ρ g : E → ℝ}
    (hρ : ∀ x, 0 ≤ ρ x) (hg : ∀ x, 0 < g x) (j : E → F) (x : E) :
    floorDensity a ρ g x • floorVelocity a ρ g j x = a • j x := by
  rw [floorVelocity, smul_smul, mul_inv_cancel₀ (floorDensity_pos ha hρ hg x).ne', one_smul]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem floorVelocity_action {a : ℝ} (ha : 0 ≤ a) {ρ g : E → ℝ}
    (hρ : ∀ x, 0 ≤ ρ x) (hg : ∀ x, 0 < g x) (j : E → F) (x : E) :
    floorDensity a ρ g x * ‖floorVelocity a ρ g j x‖^2 =
      ‖a • j x‖^2 / floorDensity a ρ g x := by
  have hp := floorDensity_pos ha hρ hg x
  simp only [floorVelocity, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hp]
  field_simp

theorem floorVelocity_smooth {a : ℝ} (ha : 0 ≤ a) {ρ g : E → ℝ} {j : E → F}
    (hρ : ∀ x, 0 ≤ ρ x) (hg : ∀ x, 0 < g x)
    (hρs : ContDiff ℝ ∞ ρ) (hgs : ContDiff ℝ ∞ g) (hjs : ContDiff ℝ ∞ j) :
    ContDiff ℝ ∞ (floorVelocity a ρ g j) := by
  exact (((contDiff_const.mul hρs).add hgs).inv
    (fun x => (floorDensity_pos ha hρ hg x).ne')).smul (contDiff_const.smul hjs)

omit [NormedSpace ℝ E] in
theorem floorVelocity_compact {a : ℝ} {ρ g : E → ℝ} {j : E → F}
    (hj : HasCompactSupport j) : HasCompactSupport (floorVelocity a ρ g j) :=
  (hj.smul_left (f := fun _ => a)).smul_left

/-- The actual floor-regularized velocity meets the spatial regularity
hypotheses of the already proved smooth Eulerian transport theorem. -/
theorem floorVelocity_regular {a : ℝ} (ha : 0 ≤ a) {ρ g : E → ℝ} {j : E → F}
    (hρ : ∀ x, 0 ≤ ρ x) (hg : ∀ x, 0 < g x)
    (hρs : ContDiff ℝ ∞ ρ) (hgs : ContDiff ℝ ∞ g) (hjs : ContDiff ℝ ∞ j)
    (hjc : HasCompactSupport j) :
    NoiseAverage.AllDerivativesBounded (floorVelocity a ρ g j) ∧
      (∃ K : ℝ≥0, LipschitzWith K (floorVelocity a ρ g j)) ∧
      (∃ K₁ : ℝ≥0, LipschitzWith K₁ (fderiv ℝ (floorVelocity a ρ g j))) := by
  have hs := floorVelocity_smooth ha hρ hg hρs hgs hjs
  have hB := allDerivativesBounded_of_compact hs (floorVelocity_compact hjc)
  exact ⟨hB, hB.lipschitz (hs.differentiable (by simp)),
    hB.fderiv.lipschitz ((contDiff_infty_iff_fderiv.mp hs).2.differentiable (by simp))⟩

end SharpWasserstein.RoughEulerianSmoothing
