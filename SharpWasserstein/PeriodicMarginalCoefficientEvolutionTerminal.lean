module

public import SharpWasserstein.Compat
public import SharpWasserstein.PeriodicMarginalCoefficientEvolutionEstimate

@[expose] public section

/-! The genuine terminal marginal has no external interaction contribution.
Its actual finite energy uses the same constructed prefix source as every
lower marginal, with a proved internal generator estimate. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace NNReal BigOperators
namespace SharpWasserstein.PeriodicMarginalCoefficientEvolution
open WeightedTangent NoiseAverage PropagatedSourceEquation WeightedMarginal
open PeriodicParticleTangentLimit WeightedPeriodicCoefficientEvolution
open ExternalInteractionPeriodic ExternalInteractionSymmetry PropagatedSourcePermutation ExternalInteraction
open FiniteGradientTrial WeightedPeriodicFourierPhysical RegularizedTrialConvergencePhysical PeriodicFourierTests
open WeightedPeriodicFourierScale (PeriodicOf)
variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]

/-- Exact full-level energy derivative decomposition, with the empty
external sum removed before any inequality is taken. -/
theorem terminal_splitEnergyDerivative_eq {P : ℝ} (hP : 0 < P)
    (μ : Measure (Point (N*d))) [IsFiniteMeasure μ] (σ : Test (N*d) →ₗ[ℝ] ℝ)
    {b : Position d → Position d → Position d} (hb : BoundedSmoothKernel b)
    (hx : ∀ a x y,b (x+Pi.single a P) y=b x y)
    (hy : ∀ a x y,b x (y+Pi.single a P)=b x y)
    {f : Point (N*d) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : PeriodicOf P (f ∘ (PeriodicBochner.coordinateEquiv (N*d)).symm)) :
    2*pairing μ (WeightedTangent.representative μ σ).val (splitGenerator (m := N) le_rfl b f)-
      (∫ x,splitGenerator (m := N) le_rfl b (fun y => ‖gradient f y‖^2) x ∂μ) =
    localEnergyTerm P (μ.map (marginalProjection (k := N) le_rfl))
      (prefixSource le_rfl μ (WeightedTangent.representative μ σ).val) (internalDrift N b) f := by
  rw [splitGenerator_terminal,splitGenerator_terminal,
    prefixSource_periodic_pairing le_rfl μ (WeightedTangent.representative μ σ).val hP
      (internalGenerator_smooth hb N hf) (internalGenerator_periodic hx hy N hp)]
  have hs := internalGenerator_smooth hb N (BochnerIdentity.smooth_gradient_norm_sq hf)
  rw [show (∫ x,cylinder (m := N) le_rfl (internalGenerator N b (fun y => ‖gradient f y‖^2)) x ∂μ) =
      ∫ y,internalGenerator N b (fun y => ‖gradient f y‖^2) y
        ∂μ.map (marginalProjection (k := N) le_rfl) from
    (integral_map (marginalProjection (k := N) le_rfl).continuous.measurable.aemeasurable
      hs.continuous.aestronglyMeasurable).symm]
  rfl

/-- Actual terminal finite generator bound, with the common hierarchy
coefficient D and the sole remaining own-energy regularization gap. -/
theorem finite_terminal_splitHierarchy_le {P : ℝ} (hP : 0 < P) (hN : 1 ≤ N)
    (μ : Measure (Point (N*d))) [IsFiniteMeasure μ] (σ : Test (N*d) →ₗ[ℝ] ℝ)
    {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
    (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
    (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hx : ∀ a x y,b (x+Pi.single a P) y=b x y)
    (hy : ∀ a x y,b x (y+Pi.single a P)=b x y)
    (s : Finset ((Fin (N*d) → ℤ) × Bool)) {δ : ℝ} (hδ : 0 < δ) :
    let L := Real.sqrt (2*(d:ℝ)*(L₁^2+L₂^2))
    let A := internalAmplitude N hb (lt_of_lt_of_le Nat.zero_lt_one hN)
    let T := trial P (μ.map (marginalProjection (k := N) le_rfl)) s
    let U := periodicPrefixField P le_rfl μ σ
    let c := RegularizedTrialEnergy.solution T δ U
    let f := potential (fun p : s => physicalPotential P (atom p.val)) c
    let e := RegularizedTrialEnergy.energy T δ U
    2*pairing μ (WeightedTangent.representative μ σ).val (splitGenerator (m := N) le_rfl b f)-
      (∫ x,splitGenerator (m := N) le_rfl b (fun y => ‖gradient f y‖^2) x ∂μ) ≤
    (2*L+2*(d:ℝ)*L₁+1)*e+
      4*(L^2+A^2)*(WeightedPeriodicTangentPhysical.energy P (μ.map (marginalProjection (k := N) le_rfl))
        (prefixSource le_rfl μ (WeightedTangent.representative μ σ).val)-e) := by
  let ρ := μ.map (marginalProjection (k := N) le_rfl)
  let τ := prefixSource le_rfl μ (WeightedTangent.representative μ σ).val
  let a := fun p : s => physicalPotential P (atom p.val)
  let T := trial P ρ s
  let U := periodicPrefixField P le_rfl μ σ
  let c := RegularizedTrialEnergy.solution T δ U
  have ha (p : s) := physicalPotential_smooth P (smooth_atom p.val)
  have hpa (p : s) := physicalPotential_periodic hP.ne' (periodic_atom p.val)
  have hi := PhysicalFourierTrialHierarchy.finite_terminal_le P ρ τ s hδ
    (internalDrift_smooth hb N) (internalDrift_allDerivativesBounded hb (lt_of_lt_of_le Nat.zero_lt_one hN))
    (Real.sqrt_nonneg _) (internalAmplitude_nonneg N hb (lt_of_lt_of_le Nat.zero_lt_one hN))
    (internalDrift_fderiv_bound hb hbound (lt_of_lt_of_le Nat.zero_lt_one hN) le_rfl hL₁ hL₂)
    (internalAmplitude_bound N hb (lt_of_lt_of_le Nat.zero_lt_one hN))
  have he := RegularizedTrialEnergy.energy_nonneg T δ hδ U
  have hext : 0 ≤ 2*(d:ℝ)*L₁*RegularizedTrialEnergy.energy T δ U := by positivity
  have hd := terminal_splitEnergyDerivative_eq hP μ σ hb hx hy (potential_smooth a ha c)
    (potential_periodic a hpa c)
  dsimp only at hi hd ⊢
  rw [hd]
  change localEnergyTerm P ρ τ (internalDrift N b) (potential a c) ≤ _ at hi
  dsimp only [ρ,τ,T,U,c,a,periodicPrefixField] at hext hi ⊢
  linarith

end SharpWasserstein.PeriodicMarginalCoefficientEvolution
