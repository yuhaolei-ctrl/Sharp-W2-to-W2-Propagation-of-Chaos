import SharpWasserstein.PeriodicMarginalCoefficientEvolutionSource

/-! The actual marginal source generator is represented by its physical
periodic tangent and one genuine next-particle source. The coefficient is
exactly (N-m)/N; terminal marginals have an empty external sum. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace BigOperators
namespace SharpWasserstein.PeriodicMarginalCoefficientEvolution
open WeightedTangent NoiseAverage PropagatedSourceEquation PeriodicSourceConvolution
open PeriodicParticleTangentLimit WeightedPeriodicCoefficientEvolution
open ExternalInteractionPeriodic ExternalInteractionSymmetry PDEPairings PropagatedSourcePermutation
open WeightedPeriodicFourierScale (PeriodicOf)
variable {d m N : ℕ}
  [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  [MeasurableSpace (Point (m*d))] [BorelSpace (Point (m*d))]
  [MeasurableSpace (Point (m*d+d))] [BorelSpace (Point (m*d+d))]

/-- Exact source marginal generator decomposition on physical periodic tests.
All three sources are constructed from the actual full law and flux, and the
external averaging follows from genuine law and field permutation covariance. -/
theorem splitGenerator_periodic_pairing {P : ℝ} (hP : 0 < P) (hm : m < N)
    (μ : Measure (Point (N*d))) [IsFiniteMeasure μ]
    (hμ : ∀ e : Equiv.Perm (Fin N),μ.map (euclideanPermutation e)=μ)
    (U : Lp (Point (N*d)) 2 μ)
    (hU : ∀ e : Equiv.Perm (Fin N),∀ᵐ x ∂μ,
      U (euclideanPermutation e x)=euclideanPermutation e (U x))
    {b : Position d → Position d → Position d} (hb : BoundedSmoothKernel b)
    (hx : ∀ a x y,b (x+Pi.single a P) y=b x y)
    (hy : ∀ a x y,b x (y+Pi.single a P)=b x y)
    {f : Point (m*d) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : PeriodicOf P (f ∘ (PeriodicBochner.coordinateEquiv (m*d)).symm)) :
    pairing μ U (splitGenerator hm.le b f) =
      (∫ y,⟪gradient (internalGenerator N b f) y,
        ((WeightedPeriodicTangentPhysical.representative P (μ.map (marginalProjection hm.le))
          (prefixSource hm.le μ U) : gradientClosure (μ.map (marginalProjection hm.le))) :
          Lp (Point (m*d)) 2 (μ.map (marginalProjection hm.le))) y⟫_ℝ
          ∂μ.map (marginalProjection hm.le)) +
      (((N:ℝ)-m)/N)*(∫ y,⟪gradient (ExternalInteraction.interaction b f) y,
        ((WeightedPeriodicTangentPhysical.representative P (μ.map (observation hm.le ⟨m,hm⟩))
          (observedSource hm.le ⟨m,hm⟩ μ U) : gradientClosure (μ.map (observation hm.le ⟨m,hm⟩))) :
          Lp (Point (m*d+d)) 2 (μ.map (observation hm.le ⟨m,hm⟩))) y⟫_ℝ
          ∂μ.map (observation hm.le ⟨m,hm⟩)) := by
  have hi := internalGenerator_smooth hb N hf
  have hpi := internalGenerator_periodic hx hy N hp
  have hbi := physical_allDerivativesBounded hP hi hpi
  have he := ExternalInteraction.interaction_smooth hb hf
  have hpe := interaction_periodic hx hy hp
  have hbe := physical_allDerivativesBounded hP he hpe
  have hsplit : pairing μ U (splitGenerator hm.le b f) =
      pairing μ U (cylinder hm.le (internalGenerator N b f))+
        (N:ℝ)⁻¹*∑ j : Fin N with m ≤ j.val,pairing μ U (particleInteraction hm.le j b f) := by
    exact pairing_add_sum μ U (Finset.univ.filter (fun j : Fin N => m ≤ j.val))
      (cylinder_smooth hm.le hi) (cylinder_allDerivativesBounded hm.le hi hbi)
      (fun j => particleInteraction hm.le j b f)
      (fun j => he.comp (observation hm.le j).contDiff)
      (fun j => hbe.comp_linear he (observation hm.le j)) _
  rw [hsplit,prefixSource_periodic_pairing hm.le μ U hP hi hpi,
    external_interaction_meanField_periodic hP hm μ hμ U hU hb hx hy hf hp]

/-- Source symmetry on compact tests suffices: covariance of its actual
canonical field is proved by the weighted Riesz symmetry theorem. -/
theorem canonical_splitGenerator_periodic_pairing {P : ℝ} (hP : 0 < P) (hm : m < N)
    (μ : Measure (Point (N*d))) [IsFiniteMeasure μ]
    (hμ : ∀ e : Equiv.Perm (Fin N),μ.map (euclideanPermutation e)=μ)
    (σ : Test (N*d) →ₗ[ℝ] ℝ) (hσE : FiniteEnergy μ σ)
    (hσ : ∀ e : Equiv.Perm (Fin N),∀ φ : Test (N*d),
      σ (pullTest (euclideanPermutation e) φ)=σ φ)
    {b : Position d → Position d → Position d} (hb : BoundedSmoothKernel b)
    (hx : ∀ a x y,b (x+Pi.single a P) y=b x y)
    (hy : ∀ a x y,b x (y+Pi.single a P)=b x y)
    {f : Point (m*d) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : PeriodicOf P (f ∘ (PeriodicBochner.coordinateEquiv (m*d)).symm)) :
    let U := (WeightedTangent.representative μ σ).val
    pairing μ U (splitGenerator hm.le b f) =
      (∫ y,⟪gradient (internalGenerator N b f) y,
        ((WeightedPeriodicTangentPhysical.representative P (μ.map (marginalProjection hm.le))
          (prefixSource hm.le μ U) : gradientClosure (μ.map (marginalProjection hm.le))) :
          Lp (Point (m*d)) 2 (μ.map (marginalProjection hm.le))) y⟫_ℝ
          ∂μ.map (marginalProjection hm.le)) +
      (((N:ℝ)-m)/N)*(∫ y,⟪gradient (ExternalInteraction.interaction b f) y,
        ((WeightedPeriodicTangentPhysical.representative P (μ.map (observation hm.le ⟨m,hm⟩))
          (observedSource hm.le ⟨m,hm⟩ μ U) : gradientClosure (μ.map (observation hm.le ⟨m,hm⟩))) :
          Lp (Point (m*d+d)) 2 (μ.map (observation hm.le ⟨m,hm⟩))) y⟫_ℝ
          ∂μ.map (observation hm.le ⟨m,hm⟩)) := by
  apply splitGenerator_periodic_pairing hP hm μ hμ _ _ hb hx hy hf hp
  intro e
  exact WeightedSourceSymmetry.representative_equivariant μ (euclideanPermutationIsometry e)
    (hμ e) σ hσE (hσ e)

omit [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  [MeasurableSpace (Point (m*d))] [BorelSpace (Point (m*d))]
  [MeasurableSpace (Point (m*d+d))] [BorelSpace (Point (m*d+d))] in
/-- The full-N endpoint has exactly zero external contribution, including
N=0 as a harmless empty-dimensional algebraic identity. -/
theorem splitGenerator_terminal (b : Position d → Position d → Position d)
    (f : Point (N*d) → ℝ) :
    splitGenerator (m := N) le_rfl b f =
      cylinder le_rfl (internalGenerator N b f) := by
  funext x
  change _+_ = _
  have hempty : Finset.univ.filter (fun j : Fin N => N ≤ j.val) = ∅ := by
    ext j
    simp [Nat.not_le.mpr j.isLt]
  rw [hempty,Finset.sum_empty,mul_zero,add_zero]
  rfl

end SharpWasserstein.PeriodicMarginalCoefficientEvolution
