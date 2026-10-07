module

public import SharpWasserstein.Compat
public import SharpWasserstein.PeriodicConvolutionDensity
public import SharpWasserstein.WeightedIntegralSquare

@[expose] public section

/-! The actual drift flux of a convolved probability law, its exact
commutator, and the weighted quadratic bound. The estimate does not divide
by a global lower bound for the smoothing density. -/
noncomputable section
open MeasureTheory Filter Set
namespace SharpWasserstein.PeriodicConvolution
open PeriodicIntegrationByParts PeriodicPositiveKernel

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (κ : ℝ) (μ : Measure (Coordinates n)) [IsProbabilityMeasure μ]

def flux (b : Coordinates n → E) (x : Coordinates n) : E :=
  ∫ y, kernel κ (x-y) • b y ∂μ

def commutator (b : Coordinates n → E) (x : Coordinates n) : E :=
  flux κ μ b x - density κ μ x • b x

omit [CompleteSpace E] in
theorem kernel_smul_integrable {b : Coordinates n → E} (hb : Continuous b)
    {M : ℝ} (hM : ∀ y, ‖b y‖ ≤ M) (x : Coordinates n) :
    Integrable (fun y => kernel κ (x-y) • b y) μ :=
  (kernel_translate_integrable κ μ x).smul_bdd M hb.aestronglyMeasurable
    (Eventually.of_forall hM)

theorem commutator_eq_integral {b : Coordinates n → E} (hb : Continuous b)
    {M : ℝ} (hM : ∀ y, ‖b y‖ ≤ M) (x : Coordinates n) :
    commutator κ μ b x = ∫ y, kernel κ (x-y) • (b y-b x) ∂μ := by
  simp_rw [smul_sub]
  rw [integral_sub (kernel_smul_integrable κ μ hb hM x)
    ((kernel_translate_integrable κ μ x).smul_const (b x)),integral_smul_const]
  rfl

theorem commutator_action_le {b : Coordinates n → E} (hb : Continuous b)
    {M : ℝ} (hM : ∀ y, ‖b y‖ ≤ M) (x : Coordinates n) :
    ‖commutator κ μ b x‖^2 / density κ μ x ≤
      ∫ y, kernel κ (x-y)*‖b y-b x‖^2 ∂μ := by
  have hn (y : Coordinates n) : ‖b y-b x‖ ≤ 2*M :=
    (norm_sub_le _ _).trans (by linarith [hM y,hM x])
  have hi := kernel_translate_integrable κ μ x
  have h₁ : Integrable (fun y => kernel κ (x-y)*‖b y-b x‖) μ :=
    hi.mul_bdd (hb.sub continuous_const).norm.aestronglyMeasurable
      (Eventually.of_forall (fun y => by simpa only [norm_norm] using hn y))
  have h₂ : Integrable (fun y => kernel κ (x-y)*‖b y-b x‖^2) μ :=
    hi.mul_bdd ((hb.sub continuous_const).norm.pow 2).aestronglyMeasurable
      (Eventually.of_forall (fun y => by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hn y) 2))
  rw [commutator_eq_integral κ μ hb hM x]
  exact WeightedIntegralSquare.weighted_norm_integral_sq_le hi h₁ h₂
    (Eventually.of_forall (fun y => (kernel_pos κ (x-y)).le)) (density_pos κ μ x)

end SharpWasserstein.PeriodicConvolution
