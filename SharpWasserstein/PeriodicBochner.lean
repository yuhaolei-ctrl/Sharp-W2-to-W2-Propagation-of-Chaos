import SharpWasserstein.PeriodicFourierTests
import SharpWasserstein.BochnerIdentity

/-! The genuine Euclidean Bochner identity transported to periodic coordinates,
then integrated over the actual fundamental domain. The Galerkin estimate uses
only smooth trial potentials, not unproved smoothness of the limiting optimizer. -/

noncomputable section
namespace SharpWasserstein.PeriodicBochner
open MeasureTheory PeriodicIntegrationByParts PeriodicFourierTests WeightedTangent
open scoped InnerProductSpace BigOperators ContDiff

/-- The coordinate change is linear and continuous, not a sup-norm isometry. -/
def coordinateEquiv (n : ℕ) : Point n ≃L[ℝ] Coordinates n :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)

def pullback {n : ℕ} (f : Coordinates n → ℝ) : Point n → ℝ := f ∘ coordinateEquiv n

def gradientSquare {n : ℕ} (f : Coordinates n → ℝ) (x : Coordinates n) : ℝ :=
  ∑ i : Fin n, coordinatePartial f i x ^ 2

def hessianSquare {n : ℕ} (f : Coordinates n → ℝ) (x : Coordinates n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, coordinatePartial (coordinatePartial f j) i x ^ 2

/-- Exact chain rule for actual derivatives under the coordinate equivalence. -/
theorem directionDeriv_pullback {n : ℕ} (f : Coordinates n → ℝ) (i : Fin n) (y : Point n) :
    PDEPairings.directionDeriv (EuclideanSpace.single i 1) (pullback f) y =
      coordinatePartial f i (coordinateEquiv n y) := by
  unfold PDEPairings.directionDeriv pullback coordinatePartial
  rw [(coordinateEquiv n).comp_right_fderiv]
  rfl

theorem laplacian_pullback {n : ℕ} (f : Coordinates n → ℝ) (y : Point n) :
    PDEPairings.laplacian (pullback f) y =
      PeriodicIntegrationByParts.laplacian f (coordinateEquiv n y) := by
  unfold PDEPairings.laplacian PeriodicIntegrationByParts.laplacian
  apply Finset.sum_congr rfl
  intro i _
  rw [show PDEPairings.directionDeriv (EuclideanSpace.single i 1) (pullback f) =
      pullback (coordinatePartial f i) from funext (directionDeriv_pullback f i)]
  exact directionDeriv_pullback _ i y

theorem gradientSquare_pullback {n : ℕ} (f : Coordinates n → ℝ) (y : Point n) :
    ‖gradient (pullback f) y‖ ^ 2 = gradientSquare f (coordinateEquiv n y) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  rw [← PDEPairings.directionDeriv_eq_gradient_component, directionDeriv_pullback]

theorem hessianSquare_pullback {n : ℕ} (f : Coordinates n → ℝ) (y : Point n) :
    HierarchyAlgebra.frobeniusSq (BochnerIdentity.hessian (pullback f) y) =
      hessianSquare f (coordinateEquiv n y) := by
  unfold HierarchyAlgebra.frobeniusSq BochnerIdentity.hessian hessianSquare
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [show PDEPairings.directionDeriv (EuclideanSpace.single j 1) (pullback f) =
      pullback (coordinatePartial f j) from funext (directionDeriv_pullback f j),
    directionDeriv_pullback]

theorem gradientPairing_pullback {n : ℕ} (f g : Coordinates n → ℝ) (y : Point n) :
    ⟪gradient (pullback f) y, gradient (pullback g) y⟫_ℝ =
      ∑ i : Fin n, coordinatePartial f i (coordinateEquiv n y) *
        coordinatePartial g i (coordinateEquiv n y) := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [RCLike.inner_apply, conj_trivial]
  rw [← PDEPairings.directionDeriv_eq_gradient_component,
    ← PDEPairings.directionDeriv_eq_gradient_component, directionDeriv_pullback,
    directionDeriv_pullback]
  ring

/-- The pointwise Bochner identity uses the genuine coordinate Hessian square. -/
theorem laplacian_gradientSquare {n : ℕ} {f : Coordinates n → ℝ}
    (hf : ContDiff ℝ ∞ f) (x : Coordinates n) :
    PeriodicIntegrationByParts.laplacian (gradientSquare f) x =
      2 * hessianSquare f x + 2 * ∑ i : Fin n,
        coordinatePartial f i x * coordinatePartial (PeriodicIntegrationByParts.laplacian f) i x := by
  have h := BochnerIdentity.laplacian_gradient_norm_sq (f := pullback f)
    (hf.comp (coordinateEquiv n).contDiff) ((coordinateEquiv n).symm x)
  change PDEPairings.laplacian (fun y => ‖gradient (pullback f) y‖ ^ 2)
    ((coordinateEquiv n).symm x) = _ at h
  rw [show (fun y => ‖gradient (pullback f) y‖ ^ 2) = pullback (gradientSquare f) from
      funext (gradientSquare_pullback f), laplacian_pullback,
    hessianSquare_pullback,
    show PDEPairings.laplacian (pullback f) = pullback (PeriodicIntegrationByParts.laplacian f) from
      funext (laplacian_pullback f), gradientPairing_pullback] at h
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using h

theorem smooth_gradientSquare {n : ℕ} {f : Coordinates n → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (gradientSquare f) :=
  ContDiff.sum (fun i _ => (smooth_coordinatePartial hf i).pow 2)

theorem continuous_gradientSquare {n : ℕ} {f : Coordinates n → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous (gradientSquare f) :=
  continuous_finsetSum Finset.univ (fun i _ => (continuous_coordinatePartial hf i).pow 2)

theorem smooth_hessianSquare {n : ℕ} {f : Coordinates n → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (hessianSquare f) :=
  ContDiff.sum (fun i _ => ContDiff.sum (fun j _ =>
    (smooth_coordinatePartial (smooth_coordinatePartial hf j) i).pow 2))

theorem smooth_laplacian {n : ℕ} {f : Coordinates n → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (PeriodicIntegrationByParts.laplacian f) :=
  ContDiff.sum (fun i _ => smooth_coordinatePartial (smooth_coordinatePartial hf i) i)

theorem periodic_gradientSquare {n : ℕ} {f : Coordinates n → ℝ} (hp : Periodic f) :
    Periodic (gradientSquare f) := by
  intro j x
  apply Finset.sum_congr rfl
  intro i _
  rw [periodic_coordinatePartial hp i j x]

theorem hessianSquare_nonneg {n : ℕ} (f : Coordinates n → ℝ) (x : Coordinates n) :
    0 ≤ hessianSquare f x :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem gradientSquare_nonneg {n : ℕ} (f : Coordinates n → ℝ) (x : Coordinates n) :
    0 ≤ gradientSquare f x := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- Bochner dissipation integrated over a genuine periodic fundamental domain. -/
theorem integral_weighted_bochner {n : ℕ} {ρ f : Coordinates n → ℝ}
    (hρ : ContDiff ℝ 2 ρ) (hpρ : Periodic ρ) (hf : ContDiff ℝ ∞ f) (hpf : Periodic f) :
    2 * (∫ x, ρ x * hessianSquare f x ∂cube n) =
      (∫ x, gradientSquare f x * PeriodicIntegrationByParts.laplacian ρ x ∂cube n) -
      2 * (∫ x, ρ x * ∑ i : Fin n,
        coordinatePartial f i x * coordinatePartial (PeriodicIntegrationByParts.laplacian f) i x ∂cube n) := by
  have hswap := integral_mul_laplacian_swap hρ
    ((smooth_gradientSquare hf).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    hpρ (periodic_gradientSquare hpf)
  have hi1 := continuous_integrable_cube (hρ.continuous.mul (smooth_hessianSquare hf).continuous)
  have hi2 := continuous_integrable_cube (hρ.continuous.mul
    (continuous_finsetSum Finset.univ (fun i _ =>
      (smooth_coordinatePartial hf i).continuous.mul
        (smooth_coordinatePartial (smooth_laplacian hf) i).continuous)))
  have he : (∫ x, ρ x * PeriodicIntegrationByParts.laplacian (gradientSquare f) x ∂cube n) =
      2 * (∫ x, ρ x * hessianSquare f x ∂cube n) +
      2 * (∫ x, ρ x * ∑ i : Fin n,
        coordinatePartial f i x * coordinatePartial (PeriodicIntegrationByParts.laplacian f) i x ∂cube n) := by
    simp_rw [laplacian_gradientSquare hf, mul_add, mul_left_comm (ρ _) 2]
    rw [integral_add (f := fun x => 2 * (ρ x * hessianSquare f x))
      (g := fun x => 2 * (ρ x * ∑ i : Fin n,
        coordinatePartial f i x * coordinatePartial (PeriodicIntegrationByParts.laplacian f) i x))
      (hi1.const_mul 2) (hi2.const_mul 2), integral_const_mul, integral_const_mul]
  linarith

/-- Testing the actual Galerkin elliptic equation with its Laplacian is legitimate
because the concrete Fourier trial space is invariant under that operator. -/
theorem galerkin_hessian_identity {n : ℕ} (s : Finset ((Fin n → ℤ) × Bool))
    {ρ σ f : Coordinates n → ℝ} (hρ : ContDiff ℝ 2 ρ) (hpρ : Periodic ρ)
    (hσ : ContDiff ℝ 1 σ) (hpσ : Periodic σ) (hf : f ∈ frequencySpace s)
    (hEq : ∀ ψ ∈ frequencySpace s,
      (∫ x, σ x * ψ x ∂cube n) =
      ∫ x, ρ x * ∑ i : Fin n, coordinatePartial f i x * coordinatePartial ψ i x ∂cube n) :
    2 * (∫ x, ρ x * hessianSquare f x ∂cube n) =
      (∫ x, gradientSquare f x * PeriodicIntegrationByParts.laplacian ρ x ∂cube n) +
      2 * (∫ x, ∑ i : Fin n, coordinatePartial σ i x * coordinatePartial f i x ∂cube n) := by
  have hfp := frequencySpace_properties s hf
  have hboch := integral_weighted_bochner hρ hpρ hfp.1 hfp.2.1
  rw [← hEq _ hfp.2.2,
    integral_mul_laplacian hσ
      (hfp.1.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hpσ hfp.2.1] at hboch
  linarith

/-- Elementary coordinate Cauchy--Young bound, independent of the Fourier cutoff. -/
theorem gradientPairing_le {n : ℕ} (f g : Coordinates n → ℝ) (x : Coordinates n) :
    2 * (∑ i : Fin n, coordinatePartial f i x * coordinatePartial g i x) ≤
      gradientSquare f x + gradientSquare g x := by
  rw [Finset.mul_sum, gradientSquare, gradientSquare, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  nlinarith [sq_nonneg (coordinatePartial f i x - coordinatePartial g i x)]

/-- A genuine uniform `H²` estimate for Fourier Galerkin potentials. The constants
come only from the positive density bound and its smooth derivatives, never from
the number of Fourier modes. No regularity of the limiting optimizer is assumed. -/
theorem galerkin_hessian_bound {n : ℕ} (s : Finset ((Fin n → ℤ) × Bool))
    {ρ σ f : Coordinates n → ℝ} {a B : ℝ} (ha : 0 < a)
    (hρ : ContDiff ℝ 2 ρ) (hpρ : Periodic ρ) (hρlower : ∀ᵐ x ∂cube n, a ≤ ρ x)
    (hΔρ : ∀ᵐ x ∂cube n, PeriodicIntegrationByParts.laplacian ρ x ≤ B)
    (hσ : ContDiff ℝ 1 σ) (hpσ : Periodic σ) (hf : f ∈ frequencySpace s)
    (hEq : ∀ ψ ∈ frequencySpace s,
      (∫ x, σ x * ψ x ∂cube n) =
      ∫ x, ρ x * ∑ i : Fin n, coordinatePartial f i x * coordinatePartial ψ i x ∂cube n) :
    (∫ x, hessianSquare f x ∂cube n) ≤
      ((B + 1) * (∫ x, gradientSquare f x ∂cube n) +
        (∫ x, gradientSquare σ x ∂cube n)) / (2 * a) := by
  have hfp := frequencySpace_properties s hf
  have hfi : ContDiff ℝ 1 f := hfp.1.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)
  have hH := continuous_integrable_cube (smooth_hessianSquare hfp.1).continuous
  have hG := continuous_integrable_cube (continuous_gradientSquare hfi)
  have hS := continuous_integrable_cube (continuous_gradientSquare hσ)
  have hρH := continuous_integrable_cube (hρ.continuous.mul (smooth_hessianSquare hfp.1).continuous)
  have hD : Continuous (PeriodicIntegrationByParts.laplacian ρ) :=
    continuous_finsetSum Finset.univ (fun i _ => continuous_coordinatePartial (contDiff_coordinatePartial hρ i) i)
  have hDG := continuous_integrable_cube ((continuous_gradientSquare hfi).mul hD)
  have hCross := continuous_integrable_cube (continuous_finsetSum Finset.univ (fun i _ =>
    (continuous_coordinatePartial hσ i).mul (continuous_coordinatePartial hfi i)))
  have hLower : a * (∫ x, hessianSquare f x ∂cube n) ≤
      ∫ x, ρ x * hessianSquare f x ∂cube n := by
    rw [← integral_const_mul]
    exact integral_mono_ae (hH.const_mul a) hρH
      (hρlower.mono fun x hx => mul_le_mul_of_nonneg_right hx (hessianSquare_nonneg f x))
  have hUpper : (∫ x, gradientSquare f x * PeriodicIntegrationByParts.laplacian ρ x ∂cube n) ≤
      B * (∫ x, gradientSquare f x ∂cube n) := by
    rw [← integral_const_mul]
    apply integral_mono_ae hDG (hG.const_mul B)
    filter_upwards [hΔρ] with x hx
    change gradientSquare f x * PeriodicIntegrationByParts.laplacian ρ x ≤ B * gradientSquare f x
    nlinarith [gradientSquare_nonneg f x]
  have hY : 2 * (∫ x, ∑ i : Fin n, coordinatePartial σ i x * coordinatePartial f i x ∂cube n) ≤
      (∫ x, gradientSquare σ x ∂cube n) + (∫ x, gradientSquare f x ∂cube n) := by
    rw [← integral_const_mul, ← integral_add hS hG]
    exact integral_mono_ae (hCross.const_mul 2) (hS.add hG)
      (Filter.Eventually.of_forall (gradientPairing_le σ f))
  have he := galerkin_hessian_identity s hρ hpρ hσ hpσ hf hEq
  apply (le_div_iff₀ (by positivity : 0 < 2 * a)).mpr
  nlinarith

end SharpWasserstein.PeriodicBochner
