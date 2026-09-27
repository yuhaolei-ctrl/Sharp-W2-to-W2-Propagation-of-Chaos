import SharpWasserstein.PeriodicCoefficientBounds
import SharpWasserstein.PeriodicJacobianLimit

/-! Drift-diffusion energy propagation for the actual periodic weighted elliptic
optimizer. The Galerkin error is constructed and shown to vanish; neither an
energy inequality nor optimizer smoothness is an input. -/
noncomputable section
namespace SharpWasserstein.PeriodicParabolicEnergy
open MeasureTheory Set Filter PeriodicIntegrationByParts PeriodicFourierTests PeriodicBochner
open PeriodicGalerkin PeriodicGradientClosure PeriodicSmoothGradient PeriodicWeakHessian
open PeriodicDriftEnergy PeriodicDriftResidual PeriodicDiffusionEnergy PeriodicJacobianLimit
open WeightedTangent WeightedDensity PeriodicCoefficientBounds
open scoped Topology BigOperators ContDiff InnerProductSpace BoundedContinuousFunction
variable {n : ℕ} [MeasurableSpace (Point n)] [BorelSpace (Point n)]

/-- Exact finite-dimensional parabolic identity, with the explicit vanishing drift residual. -/
theorem finiteDerivativePairing_eq (ρ ρ' : Point n →ᵇ ℝ)
    (ℓ ℓ' J : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ) {a : ℝ}
    (ha : 0 < a) (hp : ∀ᵐ y ∂cubePoint, a ≤ ρ y)
    (hρ : ContDiff ℝ ∞ (fun x => ρ ((coordinateEquiv n).symm x)))
    (hpρ : Periodic (fun x => ρ ((coordinateEquiv n).symm x)))
    {b : Coordinates n → Coordinates n} (hb : ContDiff ℝ ∞ b)
    (hpb : ∀ j, Periodic (fun x => b x j))
    (hρpde : ∀ᵐ x ∂cube n, ρ' ((coordinateEquiv n).symm x) =
      PeriodicIntegrationByParts.laplacian (fun y => ρ ((coordinateEquiv n).symm y)) x -
        PeriodicDriftEnergy.divergence (fun y => ρ ((coordinateEquiv n).symm y) • b y) x)
    (s : Finset ((Fin n → ℤ) × Bool))
    (hℓpde : ∀ ψ : frequencySpace s,
      ℓ' (trialGradient s ψ) = ℓ (trialGradient s (laplacianTrial s ψ)) +
        ℓ (gradientVector (drift b ψ.val)
          (smooth_drift (frequencySpace_properties s ψ.property).1 hb)) + J (trialGradient s ψ)) :
    2*ℓ' (vector ρ ℓ s)-
      (∫ y, ρ' y*‖(vector ρ ℓ s : Lp (Point n) 2 cubePoint) y‖^2 ∂cubePoint) =
      -2*(∫ x, ρ ((coordinateEquiv n).symm x)*hessianSquare (potential ρ ℓ s).val x ∂cube n)+
      2*(∫ x, ρ ((coordinateEquiv n).symm x)*jacobianForm b (potential ρ ℓ s).val x ∂cube n)+
      2*residual ρ ℓ b hb s+2*J (vector ρ ℓ s) := by
  have hf := frequencySpace_properties s (potential ρ ℓ s).property
  have hρ2 := hρ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hρ1 := hρ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)
  have hd := diffusion_identity ρ ℓ ha hp hρ2 hpρ s
  have hbI := finite_drift_pairing_integral ρ ℓ ha hp hρ1 hpρ hb hpb s
  have he := hℓpde (potential ρ ℓ s)
  rw [gradient_potential] at he
  have hprod : ContDiff ℝ ∞ (fun y => ρ ((coordinateEquiv n).symm y) • b y) := hρ.smul hb
  have hdiv : Continuous (PeriodicDriftEnergy.divergence
      (fun y => ρ ((coordinateEquiv n).symm y) • b y)) :=
    continuous_finsetSum Finset.univ (fun i _ =>
      (smooth_coordinatePartial ((contDiff_pi.mp hprod) i) i).continuous)
  have hi := continuous_integrable_cube
    ((smooth_laplacian hρ).continuous.mul (smooth_gradientSquare hf.1).continuous)
  have hj := continuous_integrable_cube (hdiv.mul (smooth_gradientSquare hf.1).continuous)
  have hI : (∫ y, ρ' y*‖(vector ρ ℓ s : Lp (Point n) 2 cubePoint) y‖^2 ∂cubePoint) =
      (∫ x, PeriodicIntegrationByParts.laplacian (fun y => ρ ((coordinateEquiv n).symm y)) x*
        gradientSquare (potential ρ ℓ s).val x ∂cube n)-
      (∫ x, PeriodicDriftEnergy.divergence (fun y => ρ ((coordinateEquiv n).symm y) • b y) x*
        gradientSquare (potential ρ ℓ s).val x ∂cube n) := by
    rw [integral_vector_square,← integral_sub
      (f := fun x => PeriodicIntegrationByParts.laplacian
        (fun y => ρ ((coordinateEquiv n).symm y)) x*gradientSquare (potential ρ ℓ s).val x)
      (g := fun x => PeriodicDriftEnergy.divergence
        (fun y => ρ ((coordinateEquiv n).symm y) • b y) x*gradientSquare (potential ρ ℓ s).val x) hi hj]
    exact integral_congr_ae (hρpde.mono fun x hx => by dsimp only; rw [hx]; ring)
  rw [hI,he]
  linarith

/-- The genuine closed-space parabolic pairing is controlled by its genuine
Jacobian integral and forcing. Auxiliary coefficient bounds are derived from
smooth periodic data solely to prove the Galerkin residual tends to zero. -/
theorem derivativePairing_le_jacobian (ρ ρ' : Point n →ᵇ ℝ)
    (ℓ ℓ' J : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)
    {σ : Coordinates n → ℝ} {a : ℝ}
    (ha : 0 < a) (hp : ∀ y, a ≤ ρ y)
    (hρ : ContDiff ℝ ∞ (fun x => ρ ((coordinateEquiv n).symm x)))
    (hpρ : Periodic (fun x => ρ ((coordinateEquiv n).symm x)))
    (hσ : ContDiff ℝ 1 σ) (hpσ : Periodic σ)
    (hsource : ∀ (s : Finset ((Fin n → ℤ) × Bool)) (ψ : frequencySpace s),
      ℓ (trialGradient s ψ) = ∫ x, σ x*ψ.val x ∂cube n)
    {b : Coordinates n → Coordinates n} (hb : ContDiff ℝ ∞ b)
    (hpb : ∀ j, Periodic (fun x => b x j))
    (hρpde : ∀ᵐ x ∂cube n, ρ' ((coordinateEquiv n).symm x) =
      PeriodicIntegrationByParts.laplacian (fun y => ρ ((coordinateEquiv n).symm y)) x -
        PeriodicDriftEnergy.divergence (fun y => ρ ((coordinateEquiv n).symm y) • b y) x)
    (hℓpde : ∀ (s : Finset ((Fin n → ℤ) × Bool)) (ψ : frequencySpace s),
      ℓ' (trialGradient s ψ) = ℓ (trialGradient s (laplacianTrial s ψ)) +
        ℓ (gradientVector (drift b ψ.val)
          (smooth_drift (frequencySpace_properties s ψ.property).1 hb)) + J (trialGradient s ψ)) :
    let U : Lp (Point n) 2 cubePoint := (optimizer ρ ℓ : gradientClosure (cubePoint (n := n)))
    2*ℓ' (optimizer ρ ℓ)-(∫ y, ρ' y*‖U y‖^2 ∂cubePoint) ≤
      2*(∫ y, ρ y*⟪fderiv ℝ (vectorPullback b) y (U y),U y⟫_ℝ ∂cubePoint)+2*J (optimizer ρ ℓ) := by
  dsimp only
  have hpos : ∀ᵐ y ∂cubePoint, a ≤ ρ y := Filter.Eventually.of_forall hp
  have hleft := derivativePairing_tendsto ρ ρ' ℓ ℓ' ha hpos
  have hres := residual_tendsto_zero_of_smooth ρ ℓ ha hp
    (hρ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hpρ hσ hpσ hsource hb hpb
  have hJac := potential_jacobianForm_tendsto ρ ℓ b hb hpb ha hpos
  have hJ := J.continuous.continuousAt.tendsto.comp (vector_tendsto ρ ℓ ha hpos)
  have hright := ((hJac.const_mul 2).add (hres.const_mul 2)).add (hJ.const_mul 2)
  simp only [mul_zero,add_zero,Function.comp_apply] at hright
  apply le_of_tendsto_of_tendsto hleft hright
  apply Filter.Eventually.of_forall
  intro s
  dsimp only
  rw [finiteDerivativePairing_eq ρ ρ' ℓ ℓ' J ha hpos hρ hpρ hb hpb hρpde s (hℓpde s)]
  have hH : 0 ≤ ∫ x, ρ ((coordinateEquiv n).symm x)*
      hessianSquare (potential ρ ℓ s).val x ∂cube n :=
    integral_nonneg fun x => mul_nonneg (ha.le.trans (hp _)) (hessianSquare_nonneg _ x)
  linarith

theorem derivativePairing_le (ρ ρ' : Point n →ᵇ ℝ)
    (ℓ ℓ' J : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)
    {σ : Coordinates n → ℝ} {a L : ℝ}
    (ha : 0 < a) (hp : ∀ y, a ≤ ρ y)
    (hρ : ContDiff ℝ ∞ (fun x => ρ ((coordinateEquiv n).symm x)))
    (hpρ : Periodic (fun x => ρ ((coordinateEquiv n).symm x)))
    (hσ : ContDiff ℝ 1 σ) (hpσ : Periodic σ)
    (hsource : ∀ (s : Finset ((Fin n → ℤ) × Bool)) (ψ : frequencySpace s),
      ℓ (trialGradient s ψ) = ∫ x, σ x*ψ.val x ∂cube n)
    {b : Coordinates n → Coordinates n} (hb : ContDiff ℝ ∞ b)
    (hpb : ∀ j, Periodic (fun x => b x j))
    (hρpde : ∀ᵐ x ∂cube n, ρ' ((coordinateEquiv n).symm x) =
      PeriodicIntegrationByParts.laplacian (fun y => ρ ((coordinateEquiv n).symm y)) x -
        PeriodicDriftEnergy.divergence (fun y => ρ ((coordinateEquiv n).symm y) • b y) x)
    (hℓpde : ∀ (s : Finset ((Fin n → ℤ) × Bool)) (ψ : frequencySpace s),
      ℓ' (trialGradient s ψ) = ℓ (trialGradient s (laplacianTrial s ψ)) +
        ℓ (gradientVector (drift b ψ.val)
          (smooth_drift (frequencySpace_properties s ψ.property).1 hb)) + J (trialGradient s ψ))
    (hDb : ∀ᵐ y ∂cubePoint, ‖fderiv ℝ (vectorPullback b) y‖ ≤ L) :
    2*ℓ' (optimizer ρ ℓ)-(∫ y, ρ' y*
      ‖((optimizer ρ ℓ : gradientClosure (cubePoint (n := n))) : Lp (Point n) 2 cubePoint) y‖^2 ∂cubePoint) ≤
      2*L*ℓ (optimizer ρ ℓ)+2*J (optimizer ρ ℓ) := by
  have h := derivativePairing_le_jacobian ρ ρ' ℓ ℓ' J ha hp hρ hpρ hσ hpσ hsource hb hpb hρpde hℓpde
  have hJac := optimizer_jacobian_integral_le ρ ℓ b hb hpb ha (Filter.Eventually.of_forall hp) hDb
  dsimp only at h hJac
  linarith

theorem deriv_energy_le
    {ρ : ℝ → (Point n →ᵇ ℝ)} {ρ' : Point n →ᵇ ℝ}
    {ℓ : ℝ → (gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)}
    {ℓ' : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ}
    (J : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)
    {t : ℝ} (hρt : HasDerivAt ρ ρ' t) (hℓt : HasDerivAt ℓ ℓ' t)
    {σ : Coordinates n → ℝ} {a L : ℝ}
    (ha : 0 < a) (hp : ∀ y, a ≤ ρ t y)
    (hρ : ContDiff ℝ ∞ (fun x => ρ t ((coordinateEquiv n).symm x)))
    (hpρ : Periodic (fun x => ρ t ((coordinateEquiv n).symm x)))
    (hσ : ContDiff ℝ 1 σ) (hpσ : Periodic σ)
    (hsource : ∀ (s : Finset ((Fin n → ℤ) × Bool)) (ψ : frequencySpace s),
      ℓ t (trialGradient s ψ) = ∫ x, σ x*ψ.val x ∂cube n)
    {b : Coordinates n → Coordinates n} (hb : ContDiff ℝ ∞ b)
    (hpb : ∀ j, Periodic (fun x => b x j))
    (hρpde : ∀ᵐ x ∂cube n, ρ' ((coordinateEquiv n).symm x) =
      PeriodicIntegrationByParts.laplacian (fun y => ρ t ((coordinateEquiv n).symm y)) x -
        PeriodicDriftEnergy.divergence (fun y => ρ t ((coordinateEquiv n).symm y) • b y) x)
    (hℓpde : ∀ (s : Finset ((Fin n → ℤ) × Bool)) (ψ : frequencySpace s),
      ℓ' (trialGradient s ψ) = ℓ t (trialGradient s (laplacianTrial s ψ)) +
        ℓ t (gradientVector (drift b ψ.val)
          (smooth_drift (frequencySpace_properties s ψ.property).1 hb)) + J (trialGradient s ψ))
    (hDb : ∀ᵐ y ∂cubePoint, ‖fderiv ℝ (vectorPullback b) y‖ ≤ L) :
    deriv (fun r => ℓ r (optimizer (ρ r) (ℓ r))) t ≤
      2*L*ℓ t (optimizer (ρ t) (ℓ t))+2*J (optimizer (ρ t) (ℓ t)) := by
  rw [(PeriodicGradientClosure.hasDerivAt_energy hρt hℓt ha (Filter.Eventually.of_forall hp)).deriv]
  exact derivativePairing_le (ρ t) ρ' (ℓ t) ℓ' J ha hp hρ hpρ hσ hpσ hsource hb hpb hρpde hℓpde hDb

end SharpWasserstein.PeriodicParabolicEnergy
