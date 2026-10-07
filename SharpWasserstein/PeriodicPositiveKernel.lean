module

public import SharpWasserstein.Compat
public import SharpWasserstein.PeriodicSmoothBounds
public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section

/-! A concrete strictly positive smooth product kernel on the unit torus.
Every mass normalization and lower bound is proved for actual integrals. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff BigOperators
namespace SharpWasserstein.PeriodicPositiveKernel
open PeriodicIntegrationByParts

def weight (κ x : ℝ) : ℝ := Real.exp (κ*Real.cos (2*Real.pi*x))
def normalizer (κ : ℝ) : ℝ := ∫ x, weight κ x ∂unitInterval
def scalar (κ x : ℝ) : ℝ := weight κ x/normalizer κ

theorem weight_smooth (κ : ℝ) : ContDiff ℝ ∞ (weight κ) := by
  unfold weight
  fun_prop

theorem weight_pos (κ x : ℝ) : 0 < weight κ x := Real.exp_pos _

theorem weight_periodic (κ : ℝ) : Function.Periodic (weight κ) 1 := by
  intro x
  have he : 2*Real.pi*(x+1) = 2*Real.pi*x+2*Real.pi := by ring
  simp only [weight,he,Real.cos_add_two_pi]

theorem weight_bounds (κ x : ℝ) : Real.exp (-|κ|) ≤ weight κ x ∧ weight κ x ≤ Real.exp |κ| := by
  have ha : |κ*Real.cos (2*Real.pi*x)| ≤ |κ| := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)).trans_eq (mul_one _)
  exact ⟨Real.exp_le_exp.mpr (abs_le.mp ha).1,Real.exp_le_exp.mpr (abs_le.mp ha).2⟩

theorem weight_integrable (κ : ℝ) : Integrable (weight κ) unitInterval :=
  Integrable.of_bound (weight_smooth κ).continuous.aestronglyMeasurable (Real.exp |κ|)
    (Eventually.of_forall (fun x => by rw [Real.norm_eq_abs,abs_of_pos (weight_pos κ x)]; exact (weight_bounds κ x).2))

theorem normalizer_bounds (κ : ℝ) : Real.exp (-|κ|) ≤ normalizer κ ∧ normalizer κ ≤ Real.exp |κ| := by
  constructor
  · have h := integral_mono (integrable_const (Real.exp (-|κ|))) (weight_integrable κ)
      (fun x => (weight_bounds κ x).1)
    simpa only [integral_const,probReal_univ,one_smul,normalizer] using h
  · have h := integral_mono (weight_integrable κ) (integrable_const (Real.exp |κ|))
      (fun x => (weight_bounds κ x).2)
    simpa only [integral_const,probReal_univ,one_smul,normalizer] using h

theorem normalizer_pos (κ : ℝ) : 0 < normalizer κ := (Real.exp_pos _).trans_le (normalizer_bounds κ).1

theorem scalar_pos (κ x : ℝ) : 0 < scalar κ x := div_pos (weight_pos κ x) (normalizer_pos κ)

theorem scalar_smooth (κ : ℝ) : ContDiff ℝ ∞ (scalar κ) := (weight_smooth κ).div_const _

theorem scalar_periodic (κ : ℝ) : Function.Periodic (scalar κ) 1 := by
  intro x
  simp only [scalar,weight_periodic κ x]

theorem scalar_integrable (κ : ℝ) : Integrable (scalar κ) unitInterval :=
  (weight_integrable κ).div_const _

theorem scalar_integral (κ : ℝ) : (∫ x, scalar κ x ∂unitInterval) = 1 := by
  change (∫ x, weight κ x/normalizer κ ∂unitInterval) = 1
  simp_rw [div_eq_mul_inv]
  rw [integral_mul_const]
  exact mul_inv_cancel₀ (normalizer_pos κ).ne'

theorem scalar_bounds (κ x : ℝ) :
    Real.exp (-|κ|)/normalizer κ ≤ scalar κ x ∧ scalar κ x ≤ Real.exp |κ|/normalizer κ :=
  ⟨div_le_div_of_nonneg_right (weight_bounds κ x).1 (normalizer_pos κ).le,
    div_le_div_of_nonneg_right (weight_bounds κ x).2 (normalizer_pos κ).le⟩

def kernel {n : ℕ} (κ : ℝ) (x : Coordinates n) : ℝ := ∏ i, scalar κ (x i)

theorem kernel_smooth (n : ℕ) (κ : ℝ) : ContDiff ℝ ∞ (kernel (n := n) κ) := by
  exact contDiff_prod (fun i _ => (scalar_smooth κ).comp (contDiff_apply ℝ ℝ i))

theorem kernel_pos {n : ℕ} (κ : ℝ) (x : Coordinates n) : 0 < kernel κ x :=
  Finset.prod_pos (fun i _ => scalar_pos κ (x i))

theorem kernel_periodic (n : ℕ) (κ : ℝ) : Periodic (kernel (n := n) κ) := by
  intro i x
  unfold kernel
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : j = i
  · subst j
    simpa only [Pi.add_apply,Pi.single_eq_same] using scalar_periodic κ (x i)
  · simp [Pi.single_eq_of_ne hj]

theorem kernel_bounds {n : ℕ} (κ : ℝ) (x : Coordinates n) :
    (Real.exp (-|κ|)/normalizer κ)^n ≤ kernel κ x ∧
      kernel κ x ≤ (Real.exp |κ|/normalizer κ)^n := by
  have hlow : 0 ≤ Real.exp (-|κ|)/normalizer κ := (div_pos (Real.exp_pos _) (normalizer_pos κ)).le
  have hlo := Finset.prod_le_prod₀ (s := Finset.univ) (f := fun _ : Fin n => Real.exp (-|κ|)/normalizer κ)
    (g := fun i => scalar κ (x i)) (fun _ _ => hlow) (fun i _ => (scalar_bounds κ (x i)).1)
  have hhi := Finset.prod_le_prod₀ (s := Finset.univ) (f := fun i : Fin n => scalar κ (x i))
    (g := fun _ => Real.exp |κ|/normalizer κ) (fun i _ => (scalar_pos κ (x i)).le)
    (fun i _ => (scalar_bounds κ (x i)).2)
  simpa only [kernel,Finset.prod_const,Finset.card_univ,Fintype.card_fin] using And.intro hlo hhi

theorem kernel_integrable (n : ℕ) (κ : ℝ) : Integrable (kernel (n := n) κ) (cube n) :=
  continuous_integrable_cube (kernel_smooth n κ).continuous

theorem kernel_integral (n : ℕ) (κ : ℝ) : (∫ x, kernel κ x ∂cube n) = 1 := by
  unfold kernel cube
  rw [integral_fintype_prod_eq_prod]
  simp only [scalar_integral,Finset.prod_const_one]

theorem kernel_derivatives_bounded (n : ℕ) (κ : ℝ) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ m (kernel (n := n) κ) x‖ ≤ C :=
  PeriodicSmoothBounds.iteratedFDeriv_bound (kernel_periodic n κ) (kernel_smooth n κ) m

end SharpWasserstein.PeriodicPositiveKernel
