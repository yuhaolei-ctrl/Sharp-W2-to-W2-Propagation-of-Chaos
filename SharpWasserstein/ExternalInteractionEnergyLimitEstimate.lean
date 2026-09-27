import SharpWasserstein.ExternalInteractionEnergyLimitPotentials

/-! The sharp external estimate along the actual marginal Galerkin sequence.
The positive Hessian term is subtracted before taking the limit, so the result
combines correctly with negative diffusion under weak Hessian convergence. -/
noncomputable section
namespace SharpWasserstein.ExternalInteractionEnergyLimit
open MeasureTheory Filter WeightedTangent WeightedMarginal WeightedDensity
open PeriodicIntegrationByParts PeriodicBochner PeriodicFourierTests PeriodicGalerkin
open PeriodicGradientClosure PeriodicSmoothGradient PeriodicOptimizerProducts
open PeriodicMarginalLift PeriodicMarginalEnergy PeriodicConvolution ExternalInteraction
open scoped Topology InnerProductSpace ContDiff BoundedContinuousFunction
variable {d m : ℕ}
  [MeasurableSpace (Point (m*d))] [BorelSpace (Point (m*d))]
  [MeasurableSpace (Point (m*d+d))] [BorelSpace (Point (m*d+d))]
  (κ : ℝ) (μ : Measure (Coordinates (m*d+d))) [IsProbabilityMeasure μ]
  (ℓ : gradientClosure (cubePoint (n := m*d+d)) →L[ℝ] ℝ)

local instance estimate_marginal_probability : IsProbabilityMeasure (μ.map (prefixCoords (m*d) d)) :=
  Measure.isProbabilityMeasure_map (prefix_continuous (m*d) d).measurable.aemeasurable

/-- Actual external contribution tested against the actual smooth marginal
Galerkin potential and the actual full weak optimizer. -/
def externalGalerkinTerm (b : Position d → Position d → Position d)
    (s : Finset ((Fin (m*d) → ℤ) × Bool)) : ℝ :=
  2*(∫ z,densityBCF κ μ z*
    ⟪((optimizer (densityBCF κ μ) ℓ : gradientClosure (cubePoint (n := m*d+d))) :
      Lp (Point (m*d+d)) 2 cubePoint) z,
      gradient (interaction b (marginalPotential κ μ ℓ s)) z⟫_ℝ ∂cubePoint)-
    ∫ z,densityBCF κ μ z*⟪liftedForce b z,
      gradient (fun q => ‖gradient (marginalPotential κ μ ℓ s) (prefixProjection (m*d) d q)‖^2) z⟫_ℝ ∂cubePoint

/-- Actual full Hessian action of the marginal potential, under the joint law. -/
def hessianGalerkinTerm (s : Finset ((Fin (m*d) → ℤ) × Bool)) : ℝ :=
  ∫ z,densityBCF κ μ z*HierarchyAlgebra.frobeniusSq
    (BochnerIdentity.hessian (marginalPotential κ μ ℓ s) (prefixProjection (m*d) d z)) ∂cubePoint

/-- The joint-law Hessian term is exactly the lower marginal term appearing
in the independently proved Galerkin diffusion identity. -/
theorem hessianGalerkinTerm_eq_marginal (s : Finset ((Fin (m*d) → ℤ) × Bool)) :
    hessianGalerkinTerm κ μ ℓ s =
      ∫ x,densityBCF κ (μ.map (prefixCoords (m*d) d)) ((coordinateEquiv (m*d)).symm x)*
        hessianSquare (potential (densityBCF κ (μ.map (prefixCoords (m*d) d)))
          (marginalFunctional ℓ) s).val x ∂cube (m*d) := by
  unfold hessianGalerkinTerm
  rw [integral_densityBCF_prefix κ μ _
    (continuous_frobenius_hessian (marginalPotential_smooth κ μ ℓ s)),integral_cubePoint]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [marginalPotential,hessianSquare_pullback,ContinuousLinearEquiv.apply_symm_apply]

/-- Finite-dimensional external absorption for the genuine convolved joint law. -/
theorem externalGalerkin_absorbed_le
    {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
    (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
    (hm : 1 ≤ m) (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    {ε : ℝ} (hε : 0 < ε) (s : Finset ((Fin (m*d) → ℤ) × Bool)) :
    externalGalerkinTerm κ μ ℓ b s-ε*hessianGalerkinTerm κ μ ℓ s ≤
      (2*(d:ℝ)*L₁+ε)*(∫ z,densityBCF κ μ z*
        ‖gradient (marginalPotential κ μ ℓ s) (prefixProjection (m*d) d z)‖^2 ∂cubePoint)+
      (gradientConstant d M L₁ L₂*(m:ℝ)/ε)*
        (∫ z,densityBCF κ μ z*
          ‖((optimizer (densityBCF κ μ) ℓ : gradientClosure (cubePoint (n := m*d+d))) :
            Lp (Point (m*d+d)) 2 cubePoint) z-
            prefixEmbedding (m*d) d (gradient (marginalPotential κ μ ℓ s) (prefixProjection (m*d) d z))‖^2 ∂cubePoint) := by
  have hρ : ∀ z,0 ≤ densityBCF κ μ z := fun z => (density_pos κ μ (coordinateEquiv (m*d+d) z)).le
  have hh := weighted_external_le (densityBCF κ μ) hρ hb hbound hm hM hL₁ hL₂
    (marginalPotential_smooth κ μ ℓ s)
    (((optimizer (densityBCF κ μ) ℓ : gradientClosure (cubePoint (n := m*d+d))) :
      Lp (Point (m*d+d)) 2 cubePoint)) hε
  change externalGalerkinTerm κ μ ℓ b s ≤ _ at hh
  unfold hessianGalerkinTerm
  linarith

/-- The actual Galerkin external contribution, after Hessian absorption,
is eventually bounded by the true optimizer energies and their exact increment.
No convergence of positive Hessian energies is assumed or inferred. -/
theorem externalGalerkin_absorbed_eventually_le
    {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
    (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
    (hm : 1 ≤ m) (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∀ᶠ s in atTop, externalGalerkinTerm κ μ ℓ b s-ε*hessianGalerkinTerm κ μ ℓ s ≤
      (2*(d:ℝ)*L₁+ε)*marginalFunctional ℓ
        (optimizer (densityBCF κ (μ.map (prefixCoords (m*d) d))) (marginalFunctional ℓ))+
      (gradientConstant d M L₁ L₂*(m:ℝ)/ε)*
        (ℓ (optimizer (densityBCF κ μ) ℓ)-marginalFunctional ℓ
          (optimizer (densityBCF κ (μ.map (prefixCoords (m*d) d))) (marginalFunctional ℓ)))+η := by
  have ht := ((potential_marginal_energy_tendsto (n := m*d) (k := d) κ μ ℓ).const_mul
    (2*(d:ℝ)*L₁+ε)).add
    ((potential_fluctuation_energy_tendsto (n := m*d) (k := d) κ μ ℓ).const_mul
      (gradientConstant d M L₁ L₂*(m:ℝ)/ε))
  have he := ht.eventually (gt_mem_nhds (lt_add_of_pos_right _ hη))
  filter_upwards [he] with s hs
  exact (externalGalerkin_absorbed_le κ μ ℓ hb hbound hm hM hL₁ hL₂ hε s).trans hs.le

end SharpWasserstein.ExternalInteractionEnergyLimit
