import SharpWasserstein.PeriodicGradientClosure

/-! Actual diffusion dissipation for periodic weighted negative-Sobolev energy.
Finite Fourier spaces are Laplacian invariant, so the diffusion calculation
has no Galerkin residual. The limiting inequality follows from strong gradient
convergence; no smoothness or Hessian of the limiting optimizer is assumed. -/

noncomputable section
namespace SharpWasserstein.PeriodicDiffusionEnergy
open MeasureTheory Set Filter PeriodicIntegrationByParts PeriodicFourierTests PeriodicBochner
open WeightedTangent WeightedDensity WeightedEnergyDerivative PeriodicGalerkin
open scoped ENNReal InnerProductSpace BigOperators Topology BoundedContinuousFunction ContDiff

variable {n : ℕ} [MeasurableSpace (Point n)] [BorelSpace (Point n)]

/-- The actual Laplacian acts inside each concrete Fourier trial space. -/
def laplacianTrial (s : Finset ((Fin n → ℤ) × Bool)) (f : frequencySpace s) : frequencySpace s :=
  ⟨PeriodicIntegrationByParts.laplacian f.val, (frequencySpace_properties s f.property).2.2⟩

/-- The actual weighted `L²` energy of the constructed vector is its periodic gradient integral. -/
theorem integral_vector_square (q ρ : Point n →ᵇ ℝ)
    (ℓ : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)
    (s : Finset ((Fin n → ℤ) × Bool)) :
    (∫ y, q y * ‖(vector ρ ℓ s : Lp (Point n) 2 (cubePoint (n := n))) y‖ ^ 2 ∂(cubePoint (n := n))) =
      ∫ x, q ((coordinateEquiv n).symm x) * gradientSquare (potential ρ ℓ s).val x ∂cube n := by
  rw [← gradient_potential]
  have h := weightedOperator_trialGradient_inner q s (potential ρ ℓ s) (potential ρ ℓ s)
  rw [weightedOperator_inner] at h
  simpa only [real_inner_self_eq_norm_sq, gradientSquare, pow_two] using h

/-- The elliptic inverse and periodic Bochner identity give the exact diffusion term. -/
theorem diffusion_identity (ρ : Point n →ᵇ ℝ)
    (ℓ : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)
    {a : ℝ} (ha : 0 < a) (hp : ∀ᵐ y ∂(cubePoint (n := n)), a ≤ ρ y)
    (hρ : ContDiff ℝ 2 (fun x => ρ ((coordinateEquiv n).symm x)))
    (hpρ : Periodic (fun x => ρ ((coordinateEquiv n).symm x)))
    (s : Finset ((Fin n → ℤ) × Bool)) :
    2 * ℓ (trialGradient s (laplacianTrial s (potential ρ ℓ s))) -
      (∫ x, PeriodicIntegrationByParts.laplacian (fun x => ρ ((coordinateEquiv n).symm x)) x *
        gradientSquare (potential ρ ℓ s).val x ∂cube n) =
      -2 * (∫ x, ρ ((coordinateEquiv n).symm x) *
        hessianSquare (potential ρ ℓ s).val x ∂cube n) := by
  have hfp := frequencySpace_properties s (potential ρ ℓ s).property
  have hB := integral_weighted_bochner hρ hpρ hfp.1 hfp.2.1
  rw [potential_equation ρ ℓ ha hp s]
  change 2 * (∫ x, ρ ((coordinateEquiv n).symm x) *
      ∑ i : Fin n, coordinatePartial (potential ρ ℓ s).val i x *
        coordinatePartial (PeriodicIntegrationByParts.laplacian (potential ρ ℓ s).val) i x ∂cube n) - _ = _
  have hm : (∫ x, gradientSquare (potential ρ ℓ s).val x *
      PeriodicIntegrationByParts.laplacian (fun x => ρ ((coordinateEquiv n).symm x)) x ∂cube n) =
      ∫ x, PeriodicIntegrationByParts.laplacian (fun x => ρ ((coordinateEquiv n).symm x)) x *
        gradientSquare (potential ρ ℓ s).val x ∂cube n := by
    congr 1
    funext x
    exact mul_comm _ _
  rw [hm] at hB
  linarith

/-- Natural weak heat equations for the density and tangent source imply the
exact finite Fourier energy dissipation, including an arbitrary continuous
forcing functional. The desired energy identity is a conclusion. -/
theorem hasDerivAt_finiteEnergy_diffusion
    {ρ : ℝ → (Point n →ᵇ ℝ)} {ρ' : Point n →ᵇ ℝ}
    {ℓ : ℝ → (gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)}
    {ℓ' : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ}
    (J : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)
    {t a : ℝ} (hρt : HasDerivAt ρ ρ' t) (hℓt : HasDerivAt ℓ ℓ' t)
    (ha : 0 < a) (hp : ∀ᵐ y ∂(cubePoint (n := n)), a ≤ ρ t y)
    (hρ : ContDiff ℝ 2 (fun x => ρ t ((coordinateEquiv n).symm x)))
    (hpρ : Periodic (fun x => ρ t ((coordinateEquiv n).symm x)))
    (hρheat : ∀ᵐ x ∂cube n, ρ' ((coordinateEquiv n).symm x) =
      PeriodicIntegrationByParts.laplacian (fun x => ρ t ((coordinateEquiv n).symm x)) x)
    (s : Finset ((Fin n → ℤ) × Bool))
    (hℓheat : ∀ ψ : frequencySpace s,
      ℓ' (trialGradient s ψ) = ℓ t (trialGradient s (laplacianTrial s ψ)) + J (trialGradient s ψ)) :
    HasDerivAt (fun r => ℓ r (vector (ρ r) (ℓ r) s))
      (-2 * (∫ x, ρ t ((coordinateEquiv n).symm x) *
        hessianSquare (potential (ρ t) (ℓ t) s).val x ∂cube n) +
        2 * J (vector (ρ t) (ℓ t) s)) t := by
  have hd := PeriodicGradientClosure.hasDerivAt_finiteEnergy hρt hℓt ha hp s
  have hi : (∫ y, ρ' y * ‖(vector (ρ t) (ℓ t) s : Lp (Point n) 2 (cubePoint (n := n))) y‖ ^ 2 ∂(cubePoint (n := n))) =
      ∫ x, PeriodicIntegrationByParts.laplacian (fun x => ρ t ((coordinateEquiv n).symm x)) x *
        gradientSquare (potential (ρ t) (ℓ t) s).val x ∂cube n := by
    rw [integral_vector_square]
    exact integral_congr_ae (hρheat.mono fun x hx => congrArg (fun z => z * _) hx)
  have he := hℓheat (potential (ρ t) (ℓ t) s)
  rw [gradient_potential] at he
  have hD := diffusion_identity (ρ t) (ℓ t) ha hp hρ hpρ s
  convert hd using 1
  rw [hi, he]
  linarith

/-- Exact diffusion-plus-forcing derivative value at a finite Fourier optimizer. -/
theorem finiteDerivativePairing_eq_diffusion (ρ ρ' : Point n →ᵇ ℝ)
    (ℓ ℓ' J : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)
    {a : ℝ} (ha : 0 < a) (hp : ∀ᵐ y ∂(cubePoint (n := n)), a ≤ ρ y)
    (hρ : ContDiff ℝ 2 (fun x => ρ ((coordinateEquiv n).symm x)))
    (hpρ : Periodic (fun x => ρ ((coordinateEquiv n).symm x)))
    (hρheat : ∀ᵐ x ∂cube n, ρ' ((coordinateEquiv n).symm x) =
      PeriodicIntegrationByParts.laplacian (fun x => ρ ((coordinateEquiv n).symm x)) x)
    (s : Finset ((Fin n → ℤ) × Bool))
    (hℓheat : ∀ ψ : frequencySpace s,
      ℓ' (trialGradient s ψ) = ℓ (trialGradient s (laplacianTrial s ψ)) + J (trialGradient s ψ)) :
    2 * ℓ' (vector ρ ℓ s) -
      (∫ y, ρ' y * ‖(vector ρ ℓ s : Lp (Point n) 2 (cubePoint (n := n))) y‖ ^ 2 ∂(cubePoint (n := n))) =
      -2 * (∫ x, ρ ((coordinateEquiv n).symm x) *
        hessianSquare (potential ρ ℓ s).val x ∂cube n) + 2 * J (vector ρ ℓ s) := by
  rw [integral_vector_square]
  have he := hℓheat (potential ρ ℓ s)
  rw [gradient_potential] at he
  have hi : (∫ x, ρ' ((coordinateEquiv n).symm x) * gradientSquare (potential ρ ℓ s).val x ∂cube n) =
      ∫ x, PeriodicIntegrationByParts.laplacian (fun x => ρ ((coordinateEquiv n).symm x)) x *
        gradientSquare (potential ρ ℓ s).val x ∂cube n :=
    integral_congr_ae (hρheat.mono fun x hx => congrArg (fun z => z * _) hx)
  have hD := diffusion_identity ρ ℓ ha hp hρ hpρ s
  rw [hi, he]
  linarith

/-- Diffusion is nonpositive for the genuine closed-space energy. This limit
uses only strong convergence of gradients, not regularity of the optimizer. -/
theorem diffusionDerivativePairing_le (ρ ρ' : Point n →ᵇ ℝ)
    (ℓ ℓ' J : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)
    {a : ℝ} (ha : 0 < a) (hp : ∀ y, a ≤ ρ y)
    (hρ : ContDiff ℝ 2 (fun x => ρ ((coordinateEquiv n).symm x)))
    (hpρ : Periodic (fun x => ρ ((coordinateEquiv n).symm x)))
    (hρheat : ∀ᵐ x ∂cube n, ρ' ((coordinateEquiv n).symm x) =
      PeriodicIntegrationByParts.laplacian (fun x => ρ ((coordinateEquiv n).symm x)) x)
    (hℓheat : ∀ (s : Finset ((Fin n → ℤ) × Bool)) (ψ : frequencySpace s),
      ℓ' (trialGradient s ψ) = ℓ (trialGradient s (laplacianTrial s ψ)) + J (trialGradient s ψ)) :
    2 * ℓ' (PeriodicGradientClosure.optimizer ρ ℓ) -
      (∫ y, ρ' y * ‖((PeriodicGradientClosure.optimizer ρ ℓ : gradientClosure (cubePoint (n := n))) :
        Lp (Point n) 2 (cubePoint (n := n))) y‖ ^ 2 ∂(cubePoint (n := n))) ≤
      2 * J (PeriodicGradientClosure.optimizer ρ ℓ) := by
  have hpos : ∀ᵐ y ∂(cubePoint (n := n)), a ≤ ρ y := Filter.Eventually.of_forall hp
  have hleft := PeriodicGradientClosure.derivativePairing_tendsto ρ ρ' ℓ ℓ' ha hpos
  have hright := (J.continuous.continuousAt.tendsto.comp
    (PeriodicGradientClosure.vector_tendsto ρ ℓ ha hpos)).const_mul 2
  apply le_of_tendsto_of_tendsto hleft hright
  apply Filter.Eventually.of_forall
  intro s
  dsimp only [Function.comp_apply]
  rw [finiteDerivativePairing_eq_diffusion ρ ρ' ℓ ℓ' J ha hpos hρ hpρ hρheat s (hℓheat s)]
  have hH : 0 ≤ ∫ x, ρ ((coordinateEquiv n).symm x) *
      hessianSquare (potential ρ ℓ s).val x ∂cube n := by
    apply integral_nonneg
    intro x
    exact mul_nonneg (ha.le.trans (hp _)) (hessianSquare_nonneg _ x)
  linarith

/-- The actual differentiated periodic energy obeys the forced diffusion inequality. -/
theorem deriv_energy_le_forcing
    {ρ : ℝ → (Point n →ᵇ ℝ)} {ρ' : Point n →ᵇ ℝ}
    {ℓ : ℝ → (gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)}
    {ℓ' : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ}
    (J : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)
    {t a : ℝ} (hρt : HasDerivAt ρ ρ' t) (hℓt : HasDerivAt ℓ ℓ' t)
    (ha : 0 < a) (hp : ∀ y, a ≤ ρ t y)
    (hρ : ContDiff ℝ 2 (fun x => ρ t ((coordinateEquiv n).symm x)))
    (hpρ : Periodic (fun x => ρ t ((coordinateEquiv n).symm x)))
    (hρheat : ∀ᵐ x ∂cube n, ρ' ((coordinateEquiv n).symm x) =
      PeriodicIntegrationByParts.laplacian (fun x => ρ t ((coordinateEquiv n).symm x)) x)
    (hℓheat : ∀ (s : Finset ((Fin n → ℤ) × Bool)) (ψ : frequencySpace s),
      ℓ' (trialGradient s ψ) = ℓ t (trialGradient s (laplacianTrial s ψ)) + J (trialGradient s ψ)) :
    deriv (fun r => ℓ r (PeriodicGradientClosure.optimizer (ρ r) (ℓ r))) t ≤
      2 * J (PeriodicGradientClosure.optimizer (ρ t) (ℓ t)) := by
  rw [(PeriodicGradientClosure.hasDerivAt_energy hρt hℓt ha (Filter.Eventually.of_forall hp)).deriv]
  exact diffusionDerivativePairing_le (ρ t) ρ' (ℓ t) ℓ' J ha hp hρ hpρ hρheat hℓheat

end SharpWasserstein.PeriodicDiffusionEnergy
