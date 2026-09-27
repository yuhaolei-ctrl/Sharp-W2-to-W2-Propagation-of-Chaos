import SharpWasserstein.PeriodicDriftEnergy
import SharpWasserstein.PeriodicWeakHessian

/-! Actual gradient bounds for periodic drift tests. Applied to the concrete
Fourier optimizers, the existing elliptic H² estimate supplies a uniform L²
bound needed to remove the Galerkin drift residual. -/
noncomputable section
namespace SharpWasserstein.PeriodicDriftGradientBound
open MeasureTheory Set Filter PeriodicIntegrationByParts PeriodicFourierTests PeriodicBochner
open PeriodicGalerkin PeriodicGradientClosure PeriodicSmoothGradient PeriodicWeakHessian
open PeriodicDriftEnergy WeightedTangent WeightedDensity
open scoped Topology BigOperators ContDiff InnerProductSpace BoundedContinuousFunction
variable {n : ℕ}

theorem coordinatePartial_sum {ι : Type*} (s : Finset ι) {f : ι → Coordinates n → ℝ}
    (hf : ∀ j ∈ s, Differentiable ℝ (f j)) (i : Fin n) (x : Coordinates n) :
    coordinatePartial (fun y => ∑ j ∈ s, f j y) i x = ∑ j ∈ s, coordinatePartial (f j) i x := by
  unfold coordinatePartial
  rw [fderiv_fun_sum (fun j hj => hf j hj x)]
  simp only [sum_apply]

theorem coordinatePartial_drift {f : Coordinates n → ℝ} (hf : ContDiff ℝ ∞ f)
    {b : Coordinates n → Coordinates n} (hb : ContDiff ℝ ∞ b) (i : Fin n) (x : Coordinates n) :
    coordinatePartial (drift b f) i x = ∑ j : Fin n,
      (b x j*coordinatePartial (coordinatePartial f j) i x+
        coordinatePartial f j x*coordinatePartial (fun y => b y j) i x) := by
  change coordinatePartial (fun y => ∑ j : Fin n, b y j*coordinatePartial f j y) i x = _
  rw [coordinatePartial_sum Finset.univ (fun j _ =>
    (((contDiff_pi.mp hb) j).mul (smooth_coordinatePartial hf j)).differentiable (by simp))]
  apply Finset.sum_congr rfl
  intro j _
  exact coordinatePartial_mul (((contDiff_pi.mp hb) j).differentiable (by simp))
    ((smooth_coordinatePartial hf j).differentiable (by simp)) i x

theorem gradientSquare_drift_le {f : Coordinates n → ℝ} (hf : ContDiff ℝ ∞ f)
    {b : Coordinates n → Coordinates n} (hb : ContDiff ℝ ∞ b) {A D : ℝ}
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hbA : ∀ x j, ‖b x j‖ ≤ A)
    (hbD : ∀ x i j, ‖coordinatePartial (fun y => b y j) i x‖ ≤ D) (x : Coordinates n) :
    gradientSquare (drift b f) x ≤
      2*(n:ℝ)^2*D^2*gradientSquare f x+2*(n:ℝ)*A^2*hessianSquare f x := by
  have hterm (i j : Fin n) :
      (b x j*coordinatePartial (coordinatePartial f j) i x+
        coordinatePartial f j x*coordinatePartial (fun y => b y j) i x)^2 ≤
      2*A^2*(coordinatePartial (coordinatePartial f j) i x)^2+
        2*D^2*(coordinatePartial f j x)^2 := by
    have hb₁ : (b x j)^2 ≤ A^2 := by
      have hh := (sq_le_sq₀ (norm_nonneg _) hA).mpr (hbA x j)
      simpa only [Real.norm_eq_abs,sq_abs] using hh
    have hb₂ : (coordinatePartial (fun y => b y j) i x)^2 ≤ D^2 := by
      have hh := (sq_le_sq₀ (norm_nonneg _) hD).mpr (hbD x i j)
      simpa only [Real.norm_eq_abs,sq_abs] using hh
    have hh₁ := mul_le_mul_of_nonneg_right hb₁ (sq_nonneg (coordinatePartial (coordinatePartial f j) i x))
    have hh₂ := mul_le_mul_of_nonneg_right hb₂ (sq_nonneg (coordinatePartial f j x))
    nlinarith [sq_nonneg (b x j*coordinatePartial (coordinatePartial f j) i x-
      coordinatePartial f j x*coordinatePartial (fun y => b y j) i x)]
  have hcoord (i : Fin n) : (coordinatePartial (drift b f) i x)^2 ≤
      (n:ℝ)*(∑ j : Fin n, (2*A^2*(coordinatePartial (coordinatePartial f j) i x)^2+
        2*D^2*(coordinatePartial f j x)^2)) := by
    rw [coordinatePartial_drift hf hb]
    have hh := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _j : Fin n => (1:ℝ))
      (fun j => b x j*coordinatePartial (coordinatePartial f j) i x+
        coordinatePartial f j x*coordinatePartial (fun y => b y j) i x)
    simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hterm i j)) (Nat.cast_nonneg n))
  calc
    _ ≤ ∑ i : Fin n, (n:ℝ)*(∑ j : Fin n,
      (2*A^2*(coordinatePartial (coordinatePartial f j) i x)^2+2*D^2*(coordinatePartial f j x)^2)) :=
      Finset.sum_le_sum (fun i _ => hcoord i)
    _ = _ := by
      simp only [Finset.sum_add_distrib,← Finset.mul_sum,mul_add,Finset.sum_const,
        Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,gradientSquare,hessianSquare]
      ring

variable [MeasurableSpace (Point n)] [BorelSpace (Point n)]

theorem gradientVector_norm_sq (f : Coordinates n → ℝ) (hf : ContDiff ℝ ∞ f) :
    ‖gradientVector f hf‖^2 = ∫ x, gradientSquare f x ∂cube n := by
  change ‖testGradient cubePoint (compactTest f hf)‖^2 = _
  rw [testGradient_norm_sq,integral_cubePoint]
  apply integral_congr_ae
  filter_upwards [cube_ae_mem n] with x hx
  rw [compactTest_gradient_on_cube f hf hx,gradientSquare_pullback,
    ContinuousLinearEquiv.apply_symm_apply]

theorem gradientVector_drift_norm_sq_le {f : Coordinates n → ℝ} (hf : ContDiff ℝ ∞ f)
    {b : Coordinates n → Coordinates n} (hb : ContDiff ℝ ∞ b) {A D : ℝ}
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hbA : ∀ x j, ‖b x j‖ ≤ A)
    (hbD : ∀ x i j, ‖coordinatePartial (fun y => b y j) i x‖ ≤ D) :
    ‖gradientVector (drift b f) (smooth_drift hf hb)‖^2 ≤
      2*(n:ℝ)^2*D^2*‖gradientVector f hf‖^2+
        2*(n:ℝ)*A^2*(∫ x, hessianSquare f x ∂cube n) := by
  rw [gradientVector_norm_sq,gradientVector_norm_sq]
  have hi := continuous_integrable_cube (smooth_gradientSquare hf).continuous
  have hj := continuous_integrable_cube (smooth_hessianSquare hf).continuous
  calc
    _ ≤ ∫ x, (2*(n:ℝ)^2*D^2*gradientSquare f x+2*(n:ℝ)*A^2*hessianSquare f x) ∂cube n :=
      integral_mono (continuous_integrable_cube (smooth_gradientSquare (smooth_drift hf hb)).continuous)
        ((hi.const_mul _).add (hj.const_mul _)) (gradientSquare_drift_le hf hb hA hD hbA hbD)
    _ = _ := by rw [integral_add (hi.const_mul _) (hj.const_mul _),integral_const_mul,integral_const_mul]

theorem potential_drift_gradient_uniform_bound (ρ : Point n →ᵇ ℝ)
    (ℓ : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)
    {σ : Coordinates n → ℝ} {a B A D : ℝ}
    (ha : 0 < a) (hB : 0 ≤ B) (hp : ∀ y, a ≤ ρ y)
    (hρ : ContDiff ℝ 2 (fun x => ρ ((coordinateEquiv n).symm x)))
    (hpρ : Periodic (fun x => ρ ((coordinateEquiv n).symm x)))
    (hΔρ : ∀ᵐ x ∂cube n, PeriodicIntegrationByParts.laplacian
      (fun x => ρ ((coordinateEquiv n).symm x)) x ≤ B)
    (hσ : ContDiff ℝ 1 σ) (hpσ : Periodic σ)
    (hsource : ∀ (s : Finset ((Fin n → ℤ) × Bool)) (ψ : frequencySpace s),
      ℓ (trialGradient s ψ) = ∫ x, σ x*ψ.val x ∂cube n)
    {b : Coordinates n → Coordinates n} (hb : ContDiff ℝ ∞ b)
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hbA : ∀ x j, ‖b x j‖ ≤ A)
    (hbD : ∀ x i j, ‖coordinatePartial (fun y => b y j) i x‖ ≤ D)
    (s : Finset ((Fin n → ℤ) × Bool)) :
    ‖gradientVector (drift b (potential ρ ℓ s).val)
        (smooth_drift (frequencySpace_properties s (potential ρ ℓ s).property).1 hb)‖ ≤
      Real.sqrt (2*(n:ℝ)^2*D^2*(‖ℓ‖/a)^2+2*(n:ℝ)*A^2*regularityBound ℓ σ a B) := by
  have hf := (frequencySpace_properties s (potential ρ ℓ s).property).1
  have hh := gradientVector_drift_norm_sq_le hf hb hA hD hbA hbD
  have he : gradientVector (potential ρ ℓ s).val hf = vector ρ ℓ s := gradient_potential ρ ℓ s
  rw [he] at hh
  have hv := vector_norm_le ρ ℓ ha (Filter.Eventually.of_forall hp) s
  have hH := potential_hessian_bound_uniform ρ ℓ s ha hB hp hρ hpρ hΔρ hσ hpσ (hsource s)
  have hbnd : ‖gradientVector (drift b (potential ρ ℓ s).val) (smooth_drift hf hb)‖^2 ≤
      2*(n:ℝ)^2*D^2*(‖ℓ‖/a)^2+2*(n:ℝ)*A^2*regularityBound ℓ σ a B := by
    apply hh.trans
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hv 2) (by positivity)
    · exact mul_le_mul_of_nonneg_left hH (by positivity)
  have hreg := regularityBound_nonneg ℓ σ ha hB
  exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr hbnd

end SharpWasserstein.PeriodicDriftGradientBound
