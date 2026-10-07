module

public import SharpWasserstein.Compat
public import SharpWasserstein.PeriodicSmoothGradient

@[expose] public section

/-! Genuine `L²` Hessian columns of smooth periodic potentials. The compact
representatives agree to every derivative near the full fundamental cube, so
these are actual coordinate Hessians. Their uniform bounds prepare the weak
Hessian construction for the limiting elliptic optimizer. -/

noncomputable section
namespace SharpWasserstein.PeriodicHessianBounds
open MeasureTheory Filter Set PeriodicIntegrationByParts PeriodicFourierTests PeriodicBochner
open PeriodicGalerkin PeriodicGradientClosure PeriodicSmoothGradient WeightedTangent
open scoped ENNReal Topology BigOperators ContDiff BoundedContinuousFunction

/-- The compact representative agrees on a neighborhood of every point in the closed cube. -/
theorem compactTest_eq_near_cube {n : ℕ} (f : Coordinates n → ℝ)
    (hf : ContDiff ℝ ∞ f) {x : Coordinates n}
    (hx : x ∈ Set.pi Set.univ (fun _ : Fin n => Icc (0 : ℝ) 1)) :
    (compactTest f hf : Point n → ℝ) =ᶠ[𝓝 ((coordinateEquiv n).symm x)] pullback f := by
  filter_upwards [cutoff_eq_one_near_cube hx] with y hy
  change SmoothCutoff.cutoff n n y * pullback f y = pullback f y
  rw [hy, one_mul]

/-- Genuine second derivatives are preserved by the fixed compactification. -/
theorem directionGradient_on_cube {n : ℕ} (f : Coordinates n → ℝ)
    (hf : ContDiff ℝ ∞ f) (j : Fin n) {x : Coordinates n}
    (hx : x ∈ Set.pi Set.univ (fun _ : Fin n => Icc (0 : ℝ) 1)) :
    gradient (PDEPairings.directionTest (compactTest f hf) (EuclideanSpace.single j 1) : Point n → ℝ)
        ((coordinateEquiv n).symm x) =
      gradient (pullback (coordinatePartial f j)) ((coordinateEquiv n).symm x) := by
  have h := compactTest_eq_near_cube f hf hx
  have hd : PDEPairings.directionDeriv (EuclideanSpace.single j 1) (compactTest f hf) =ᶠ[
      𝓝 ((coordinateEquiv n).symm x)] PDEPairings.directionDeriv (EuclideanSpace.single j 1) (pullback f) := by
    filter_upwards [h.gradient] with y hy
    rw [PDEPairings.directionDeriv_eq_gradient_component,
      PDEPairings.directionDeriv_eq_gradient_component, hy]
  have he : PDEPairings.directionDeriv (EuclideanSpace.single j 1) (pullback f) =
      pullback (coordinatePartial f j) := funext (directionDeriv_pullback f j)
  rw [he] at hd
  exact hd.gradient_eq

variable {n : ℕ} [MeasurableSpace (Point n)] [BorelSpace (Point n)]

/-- The actual `j`-th Hessian column as an equivalence class in the cube's Euclidean `L²`. -/
def hessianColumn (f : Coordinates n → ℝ) (hf : ContDiff ℝ ∞ f) (j : Fin n) :
    Lp (Point n) 2 (cubePoint (n := n)) :=
  testGradient cubePoint (PDEPairings.directionTest (compactTest f hf) (EuclideanSpace.single j 1))

theorem hessianColumn_norm_sq (f : Coordinates n → ℝ) (hf : ContDiff ℝ ∞ f) (j : Fin n) :
    ‖hessianColumn f hf j‖ ^ 2 =
      ∫ x, ∑ i : Fin n, coordinatePartial (coordinatePartial f j) i x ^ 2 ∂cube n := by
  rw [hessianColumn, testGradient_norm_sq, integral_cubePoint]
  apply integral_congr_ae
  filter_upwards [cube_ae_mem n] with x hx
  rw [directionGradient_on_cube f hf j hx, gradientSquare_pullback,
    ContinuousLinearEquiv.apply_symm_apply]
  rfl

/-- One Hessian column is controlled by the full actual Hessian square. -/
theorem hessianColumn_norm_sq_le (f : Coordinates n → ℝ) (hf : ContDiff ℝ ∞ f) (j : Fin n) :
    ‖hessianColumn f hf j‖ ^ 2 ≤ ∫ x, hessianSquare f x ∂cube n := by
  rw [hessianColumn_norm_sq]
  apply integral_mono
    (continuous_integrable_cube (smooth_gradientSquare (smooth_coordinatePartial hf j)).continuous)
    (continuous_integrable_cube (smooth_hessianSquare hf).continuous)
  intro x
  apply Finset.sum_le_sum
  intro i _
  exact Finset.single_le_sum (fun k _ => sq_nonneg (coordinatePartial (coordinatePartial f k) i x))
    (Finset.mem_univ j)

/-- The constructed Galerkin Hessian columns have an actual, mode-independent `L²` bound. -/
theorem potential_hessianColumn_norm_sq_le (ρ : Point n →ᵇ ℝ)
    (ℓ : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)
    (s : Finset ((Fin n → ℤ) × Bool)) {σ : Coordinates n → ℝ} {a B : ℝ}
    (ha : 0 < a) (hB : 0 ≤ B) (hp : ∀ y, a ≤ ρ y)
    (hρ : ContDiff ℝ 2 (fun x => ρ ((coordinateEquiv n).symm x)))
    (hpρ : Periodic (fun x => ρ ((coordinateEquiv n).symm x)))
    (hΔρ : ∀ᵐ x ∂cube n,
      PeriodicIntegrationByParts.laplacian (fun x => ρ ((coordinateEquiv n).symm x)) x ≤ B)
    (hσ : ContDiff ℝ 1 σ) (hpσ : Periodic σ)
    (hsource : ∀ ψ : frequencySpace s,
      ℓ (trialGradient s ψ) = ∫ x, σ x * ψ.val x ∂cube n) (j : Fin n) :
    ‖hessianColumn (potential ρ ℓ s).val (frequencySpace_properties s (potential ρ ℓ s).property).1 j‖ ^ 2 ≤
      ((B + 1) * (‖ℓ‖ / a) ^ 2 + (∫ x, gradientSquare σ x ∂cube n)) / (2 * a) :=
  (hessianColumn_norm_sq_le _ _ j).trans
    (potential_hessian_bound_uniform ρ ℓ s ha hB hp hρ hpρ hΔρ hσ hpσ hsource)

end SharpWasserstein.PeriodicHessianBounds
