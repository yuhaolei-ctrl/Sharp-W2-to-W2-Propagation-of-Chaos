module

public import SharpWasserstein.Compat
public import SharpWasserstein.PhysicalFourierTrialMarginal
public import SharpWasserstein.PhysicalFourierTrialBounds
public import SharpWasserstein.FiniteTrialEnergyInequality
public import SharpWasserstein.ExternalInteractionEnergyCancellation

@[expose] public section

/-! Actual external interaction bound at a finite physical Fourier optimizer.
The favourable fluctuation is the next periodic source energy minus the
current regularized energy, with no assumed marginal pairing. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace BigOperators
namespace SharpWasserstein.PhysicalFourierTrialExternal
open WeightedTangent WeightedMarginal PeriodicFourierTests BochnerIdentity
open WeightedPeriodicFourierPhysical RegularizedTrialConvergencePhysical
open FiniteGradientTrial ExternalInteraction
variable {d m : ℕ} [MeasurableSpace (Point (m*d))] [BorelSpace (Point (m*d))]
  [MeasurableSpace (Point (m*d+d))] [BorelSpace (Point (m*d+d))]
  (P : ℝ) (μ : Measure (Point (m*d+d))) [IsFiniteMeasure μ]

theorem integral_external_trial_le (σ : Test (m*d+d) →ₗ[ℝ] ℝ)
    (s : Finset ((Fin (m*d) → ℤ) × Bool)) {δ : ℝ} (hδ : 0 < δ)
    {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
    (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
    (hm : 1 ≤ m) (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    {ε : ℝ} (hε : 0 < ε) :
    let T := trial P (marginalLaw μ) s
    let U := (WeightedPeriodicTangentPhysical.representative P (marginalLaw μ)
      (marginalDistribution μ σ)).val.val
    let V := (WeightedPeriodicTangentPhysical.representative P μ σ).val.val
    let c := RegularizedTrialEnergy.solution T δ U
    let f := potential (fun p : s => physicalPotential P (atom p.val)) c
    2*(∫ z,⟪V z,gradient (interaction b f) z⟫_ℝ ∂μ)-
      (∫ z,⟪liftedForce b z,
        gradient (fun q => ‖gradient f (prefixProjection (m*d) d q)‖^2) z⟫_ℝ ∂μ) ≤
      (2*(d:ℝ)*L₁+ε)*RegularizedTrialEnergy.energy T δ U+
      ε*(∫ x,HierarchyAlgebra.frobeniusSq (hessian f x) ∂marginalLaw μ)+
      (gradientConstant d M L₁ L₂*(m:ℝ)/ε)*
        (WeightedPeriodicTangentPhysical.energy P μ σ-RegularizedTrialEnergy.energy T δ U) := by
  dsimp only
  let a := fun p : s => physicalPotential P (atom p.val)
  have ha : ∀ p,ContDiff ℝ ∞ (a p) := fun p => physicalPotential_smooth P (smooth_atom p.val)
  have hBa : ∀ p,NoiseAverage.AllDerivativesBounded (a p) := fun p =>
    physicalPotential_allDerivativesBounded P (smooth_atom p.val) (periodic_atom p.val)
  have hGa : ∀ p,∃ B : ℝ,∀ x,‖gradient (a p) x‖ ≤ B := fun p =>
    physicalPotential_gradient_bound P _ (smooth_atom p.val) (periodic_atom p.val)
  let T := trial P (marginalLaw μ) s
  let U := (WeightedPeriodicTangentPhysical.representative P (marginalLaw μ)
    (marginalDistribution μ σ)).val.val
  let V := (WeightedPeriodicTangentPhysical.representative P μ σ).val.val
  let c := RegularizedTrialEnergy.solution T δ U
  let f := potential a c
  have hf := potential_smooth a ha c
  have hBf := potential_allDerivativesBounded a ha hBa c
  have hg : MemLp (gradient f) 2 (marginalLaw μ) := by
    obtain ⟨B,_,hBg⟩ := (WeightedPeriodicCoefficientEvolution.gradient_allDerivativesBounded hf hBf).bounded
    exact bounded_smooth_gradient_memLp _ _ hf ⟨B,hBg⟩
  have hgp := hg.comp_measurePreserving (measurePreserving_prefix μ)
  have hH := hessian_square_integrable (marginalLaw μ) hf hBf
  have hHp := (measurePreserving_prefix μ).integrable_comp hH.aestronglyMeasurable |>.mpr hH
  have hext := integral_external_le μ hb hbound hm hM hL₁ hL₂ hf hgp hHp (Lp.memLp V) hε
  have hmapG : (∫ z,‖gradient f (prefixProjection (m*d) d z)‖^2 ∂μ) =
      ∫ x,‖gradient f x‖^2 ∂marginalLaw μ :=
    (integral_map (prefixProjection (m*d) d).continuous.measurable.aemeasurable
      (((smooth_gradient hf).continuous.norm.pow 2).aestronglyMeasurable)).symm
  have hmapH : (∫ z,HierarchyAlgebra.frobeniusSq (hessian f (prefixProjection (m*d) d z)) ∂μ) =
      ∫ x,HierarchyAlgebra.frobeniusSq (hessian f x) ∂marginalLaw μ :=
    (integral_map (prefixProjection (m*d) d).continuous.measurable.aemeasurable
      hH.aestronglyMeasurable).symm
  have hgap := PhysicalFourierTrialMarginal.trial_fluctuation_integral P μ σ s hδ
  have hE := RegularizedTrialEnergy.energy_eq_penalized_norm T δ hδ U
  rw [show T = gradientMap (marginalLaw μ) a ha hGa from rfl,gradientMap_norm_sq] at hE
  have hEg : (∫ x,‖gradient f x‖^2 ∂marginalLaw μ) ≤ RegularizedTrialEnergy.energy T δ U := by
    change RegularizedTrialEnergy.energy T δ U = (∫ x,‖gradient f x‖^2 ∂marginalLaw μ)+δ*‖c‖^2 at hE
    have := mul_nonneg hδ.le (sq_nonneg ‖c‖)
    linarith
  have hCg : 0 ≤ 2*(d:ℝ)*L₁+ε := by positivity
  have hCf : 0 ≤ gradientConstant d M L₁ L₂*(m:ℝ)/ε := by
    exact div_nonneg (mul_nonneg (gradientConstant_nonneg _ _ _ _) (Nat.cast_nonneg _)) hε.le
  have hpen : 0 ≤ δ*‖c‖^2 := mul_nonneg hδ.le (sq_nonneg _)
  have hGle := mul_le_mul_of_nonneg_left hEg hCg
  dsimp only at hgap
  change (∫ z,‖V z-prefixEmbedding (m*d) d (gradient f (prefixProjection (m*d) d z))‖^2 ∂μ) =
    WeightedPeriodicTangentPhysical.energy P μ σ-RegularizedTrialEnergy.energy T δ U-δ*‖c‖^2 at hgap
  rw [hmapG,hmapH,hgap] at hext
  have hFle := mul_le_mul_of_nonneg_left (show
    WeightedPeriodicTangentPhysical.energy P μ σ-RegularizedTrialEnergy.energy T δ U-δ*‖c‖^2 ≤
    WeightedPeriodicTangentPhysical.energy P μ σ-RegularizedTrialEnergy.energy T δ U by linarith) hCf
  change 2*(∫ z,⟪V z,gradient (interaction b f) z⟫_ℝ ∂μ)-_ ≤ _
  linarith

end SharpWasserstein.PhysicalFourierTrialExternal
