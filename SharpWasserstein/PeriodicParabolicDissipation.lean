import SharpWasserstein.PeriodicParabolicEnergy
import SharpWasserstein.PeriodicHessianDissipation

/-! The actual periodic parabolic optimizer retains its full weighted Hessian
dissipation after Galerkin passage. The Hessian, its weak equations, and the
negative dissipation term are conclusions, never regularity assumptions. -/
noncomputable section
namespace SharpWasserstein.PeriodicParabolicDissipation
open MeasureTheory Set Filter PeriodicIntegrationByParts PeriodicFourierTests PeriodicBochner
open PeriodicGalerkin PeriodicGradientClosure PeriodicSmoothGradient PeriodicWeakHessian
open PeriodicDriftEnergy PeriodicDriftResidual PeriodicDiffusionEnergy PeriodicJacobianLimit
open WeightedTangent WeightedDensity PeriodicCoefficientBounds PeriodicParabolicEnergy
open PeriodicHessianDissipation PeriodicTestL2
open scoped Topology BigOperators ContDiff InnerProductSpace BoundedContinuousFunction
variable {n : ℕ} [MeasurableSpace (Point n)] [BorelSpace (Point n)]

/-- The ordinary weak coordinate derivative equations on the actual cube. -/
def IsWeakHessian (U : Lp (Point n) 2 (cubePoint (n := n)))
    (H : Fin n → Fin n → Lp ℝ 2 (cubePoint (n := n))) : Prop :=
  ∀ i j (φ : SmoothPeriodicTest n),
    (∫ x,H i j ((coordinateEquiv n).symm x)*φ.val x ∂cube n) =
      -(∫ x,U ((coordinateEquiv n).symm x) j*coordinatePartial φ.val i x ∂cube n)

/-- The full actual weighted matrix-square integral. -/
def dissipation (ρ : Point n →ᵇ ℝ) (H : Fin n → Fin n → Lp ℝ 2 (cubePoint (n := n))) : ℝ :=
  ∑ i : Fin n,∑ j : Fin n,∫ y,ρ y*(H i j y)^2 ∂cubePoint

section Pairing
variable (ρ ρ' : Point n →ᵇ ℝ)
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
          (smooth_drift (frequencySpace_properties s ψ.property).1 hb)) + J (trialGradient s ψ))
include ha hp hρ hpρ hσ hpσ hsource hb hpb hρpde hℓpde

/-- The exact finite parabolic identity and proved residual convergence force
the genuine Galerkin Hessian energies to converge. -/
theorem potential_hessian_integral_tendsto :
    let U : Lp (Point n) 2 cubePoint := (optimizer ρ ℓ : gradientClosure (cubePoint (n := n)))
    Tendsto (fun s => ∫ x,ρ ((coordinateEquiv n).symm x)*
      hessianSquare (potential ρ ℓ s).val x ∂cube n) atTop
      (𝓝 ((2*(∫ y,ρ y*⟪fderiv ℝ (vectorPullback b) y (U y),U y⟫_ℝ ∂cubePoint)+
        2*J (optimizer ρ ℓ)-(2*ℓ' (optimizer ρ ℓ)-∫ y,ρ' y*‖U y‖^2 ∂cubePoint))/2)) := by
  dsimp only
  have hpos : ∀ᵐ y ∂cubePoint,a ≤ ρ y := Filter.Eventually.of_forall hp
  have hleft := derivativePairing_tendsto ρ ρ' ℓ ℓ' ha hpos
  have hres := residual_tendsto_zero_of_smooth ρ ℓ ha hp
    (hρ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hpρ hσ hpσ hsource hb hpb
  have hJac := potential_jacobianForm_tendsto ρ ℓ b hb hpb ha hpos
  have hJ := J.continuous.continuousAt.tendsto.comp (vector_tendsto ρ ℓ ha hpos)
  have ht := ((((hJac.const_mul 2).add (hres.const_mul 2)).add (hJ.const_mul 2)).sub hleft).div_const 2
  simp only [mul_zero,add_zero,Function.comp_apply] at ht
  apply ht.congr'
  apply Filter.Eventually.of_forall
  intro s
  have he := finiteDerivativePairing_eq ρ ρ' ℓ ℓ' J ha hpos hρ hpρ hb hpb hρpde s (hℓpde s)
  dsimp only
  linarith

/-- The optimizer's genuine weak Hessian retains the full negative diffusion
term, while the genuine drift Jacobian form passes by strong gradient convergence. -/
theorem exists_derivativePairing_le_dissipation_jacobian :
    let U : Lp (Point n) 2 cubePoint := (optimizer ρ ℓ : gradientClosure (cubePoint (n := n)))
    ∃ H : Fin n → Fin n → Lp ℝ 2 (cubePoint (n := n)),
      (∀ i j,H i j ∈ WeakDerivativeLimit.testClosure value) ∧ IsWeakHessian U H ∧
      2*ℓ' (optimizer ρ ℓ)-(∫ y,ρ' y*‖U y‖^2 ∂cubePoint) ≤
        -2*dissipation ρ H+
        2*(∫ y,ρ y*⟪fderiv ℝ (vectorPullback b) y (U y),U y⟫_ℝ ∂cubePoint)+
        2*J (optimizer ρ ℓ) := by
  dsimp only
  obtain ⟨B,hB,hΔρ⟩ := exists_laplacian_upper_bound
    (hρ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hpρ
  obtain ⟨H,hm,_,he,_,hlim⟩ := exists_optimizer_hessian_weighted_liminf ρ ℓ ha hB hp hρ hpρ
    (Filter.Eventually.of_forall hΔρ) hσ hpσ hsource
  refine ⟨H,hm,he,?_⟩
  have ht := potential_hessian_integral_tendsto ρ ρ' ℓ ℓ' J ha hp hρ hpρ hσ hpσ hsource hb hpb hρpde hℓpde
  dsimp only at ht
  rw [ht.liminf_eq] at hlim
  change dissipation ρ H ≤ _ at hlim
  linarith

/-- A bound on the actual drift Jacobian gives the usual energy term while
preserving the entire Hessian dissipation, with coefficient exactly `-2`. -/
theorem exists_derivativePairing_le_dissipation {L : ℝ}
    (hDb : ∀ᵐ y ∂cubePoint,‖fderiv ℝ (vectorPullback b) y‖ ≤ L) :
    let U : Lp (Point n) 2 cubePoint := (optimizer ρ ℓ : gradientClosure (cubePoint (n := n)))
    ∃ H : Fin n → Fin n → Lp ℝ 2 (cubePoint (n := n)),
      (∀ i j,H i j ∈ WeakDerivativeLimit.testClosure value) ∧ IsWeakHessian U H ∧
      2*ℓ' (optimizer ρ ℓ)-(∫ y,ρ' y*‖U y‖^2 ∂cubePoint) ≤
        -2*dissipation ρ H+2*L*ℓ (optimizer ρ ℓ)+2*J (optimizer ρ ℓ) := by
  obtain ⟨H,hm,he,h⟩ := exists_derivativePairing_le_dissipation_jacobian
    ρ ρ' ℓ ℓ' J ha hp hρ hpρ hσ hpσ hsource hb hpb hρpde hℓpde
  refine ⟨H,hm,he,?_⟩
  have hJac := optimizer_jacobian_integral_le ρ ℓ b hb hpb ha (Filter.Eventually.of_forall hp) hDb
  dsimp only at h hJac ⊢
  linarith
end Pairing

/-- The actual time derivative of optimizer energy satisfies the sharp
parabolic estimate with its constructed full weak-Hessian dissipation. -/
theorem exists_deriv_energy_le_dissipation
    {ρ : ℝ → (Point n →ᵇ ℝ)} {ρ' : Point n →ᵇ ℝ}
    {ℓ : ℝ → (gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)}
    {ℓ' : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ}
    (J : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)
    {t : ℝ} (hρt : HasDerivAt ρ ρ' t) (hℓt : HasDerivAt ℓ ℓ' t)
    {σ : Coordinates n → ℝ} {a L : ℝ}
    (ha : 0 < a) (hp : ∀ y,a ≤ ρ t y)
    (hρ : ContDiff ℝ ∞ (fun x => ρ t ((coordinateEquiv n).symm x)))
    (hpρ : Periodic (fun x => ρ t ((coordinateEquiv n).symm x)))
    (hσ : ContDiff ℝ 1 σ) (hpσ : Periodic σ)
    (hsource : ∀ (s : Finset ((Fin n → ℤ) × Bool)) (ψ : frequencySpace s),
      ℓ t (trialGradient s ψ) = ∫ x,σ x*ψ.val x ∂cube n)
    {b : Coordinates n → Coordinates n} (hb : ContDiff ℝ ∞ b)
    (hpb : ∀ j,Periodic (fun x => b x j))
    (hρpde : ∀ᵐ x ∂cube n,ρ' ((coordinateEquiv n).symm x) =
      PeriodicIntegrationByParts.laplacian (fun y => ρ t ((coordinateEquiv n).symm y)) x-
        PeriodicDriftEnergy.divergence (fun y => ρ t ((coordinateEquiv n).symm y) • b y) x)
    (hℓpde : ∀ (s : Finset ((Fin n → ℤ) × Bool)) (ψ : frequencySpace s),
      ℓ' (trialGradient s ψ) = ℓ t (trialGradient s (laplacianTrial s ψ))+
        ℓ t (gradientVector (drift b ψ.val)
          (smooth_drift (frequencySpace_properties s ψ.property).1 hb))+J (trialGradient s ψ))
    (hDb : ∀ᵐ y ∂cubePoint,‖fderiv ℝ (vectorPullback b) y‖ ≤ L) :
    ∃ H : Fin n → Fin n → Lp ℝ 2 (cubePoint (n := n)),
      (∀ i j,H i j ∈ WeakDerivativeLimit.testClosure value) ∧
      IsWeakHessian ((optimizer (ρ t) (ℓ t) : gradientClosure (cubePoint (n := n))) :
        Lp (Point n) 2 cubePoint) H ∧
      deriv (fun r => ℓ r (optimizer (ρ r) (ℓ r))) t ≤
        -2*dissipation (ρ t) H+2*L*ℓ t (optimizer (ρ t) (ℓ t))+2*J (optimizer (ρ t) (ℓ t)) := by
  obtain ⟨H,hm,he,h⟩ := exists_derivativePairing_le_dissipation
    (ρ t) ρ' (ℓ t) ℓ' J ha hp hρ hpρ hσ hpσ hsource hb hpb hρpde hℓpde hDb
  refine ⟨H,hm,he,?_⟩
  rw [(PeriodicGradientClosure.hasDerivAt_energy hρt hℓt ha (Filter.Eventually.of_forall hp)).deriv]
  exact h

end SharpWasserstein.PeriodicParabolicDissipation
