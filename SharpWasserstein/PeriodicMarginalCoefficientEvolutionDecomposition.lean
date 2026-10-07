module

public import SharpWasserstein.Compat
public import SharpWasserstein.PeriodicMarginalCoefficientEvolutionGeneratorTime
public import SharpWasserstein.PhysicalFourierTrialHierarchy
public import SharpWasserstein.InternalDriftFiniteBounds

@[expose] public section

/-! Exact generator energy decomposition before applying the finite hierarchy
estimate. Prefix source consistency identifies every law and representative. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace NNReal BigOperators
namespace SharpWasserstein.PeriodicMarginalCoefficientEvolution
open WeightedTangent NoiseAverage PropagatedSourceEquation PeriodicSourceConvolution
open PeriodicParticleTangentLimit WeightedPeriodicCoefficientEvolution WeightedMarginal
open ExternalInteractionPeriodic ExternalInteractionSymmetry PropagatedSourcePermutation ExternalInteraction
open FiniteCoefficientMatrix FiniteCoefficientEnergy FiniteGradientTrial
open WeightedPeriodicFourierScale (PeriodicOf)
variable {d m N : ℕ} {n : ℕ}

/-- Actual finite linear combinations preserve the physical period. -/
theorem potential_periodic {ι : Type*} [Fintype ι] {P : ℝ} (a : ι → Point n → ℝ)
    (hp : ∀ i,PeriodicOf P (a i ∘ (PeriodicBochner.coordinateEquiv n).symm))
    (c : EuclideanSpace ℝ ι) :
    PeriodicOf P (potential a c ∘ (PeriodicBochner.coordinateEquiv n).symm) := by
  intro j x
  simp only [Function.comp_apply,potential,Finset.sum_apply,Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show a i ((PeriodicBochner.coordinateEquiv n).symm (x+Pi.single j P)) =
    a i ((PeriodicBochner.coordinateEquiv n).symm x) from hp i j x]

/-- The literal internal generator energy term at the actual periodic tangent. -/
def localEnergyTerm [MeasurableSpace (Point n)] [BorelSpace (Point n)]
    (P : ℝ) (μ : Measure (Point n)) [IsFiniteMeasure μ] (σ : Test n →ₗ[ℝ] ℝ)
    (B : Point n → Point n) (f : Point n → ℝ) : ℝ :=
  2*(∫ x,⟪gradient (FiniteGeneratorCalculus.generator B f) x,
    (WeightedPeriodicTangentPhysical.representative P μ σ).val.val x⟫_ℝ ∂μ)-
      (∫ x,FiniteGeneratorCalculus.generator B (fun y => ‖gradient f y‖^2) x ∂μ)

/-- The literal next-particle interaction energy term. -/
def externalEnergyTerm [MeasurableSpace (Point (m*d+d))] [BorelSpace (Point (m*d+d))]
    (P : ℝ) (μ : Measure (Point (m*d+d))) [IsFiniteMeasure μ] (σ : Test (m*d+d) →ₗ[ℝ] ℝ)
    (b : Position d → Position d → Position d) (f : Point (m*d) → ℝ) : ℝ :=
  2*(∫ z,⟪(WeightedPeriodicTangentPhysical.representative P μ σ).val.val z,
    gradient (interaction b f) z⟫_ℝ ∂μ)-
      (∫ z,⟪liftedForce b z,gradient (fun w => ‖gradient f (prefixProjection (m*d) d w)‖^2) z⟫_ℝ ∂μ)

variable [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  [MeasurableSpace (Point (m*d))] [BorelSpace (Point (m*d))]
  [MeasurableSpace (Point (m*d+d))] [BorelSpace (Point (m*d+d))]

/-- Exact decomposition of the genuine full-law energy derivative into the
marginal periodic internal term and the next-particle periodic external term. -/
theorem splitEnergyDerivative_eq {P : ℝ} (hP : 0 < P) (hm : m < N)
    (μ : Measure (Point (N*d))) [IsFiniteMeasure μ]
    (hμ : ∀ e : Equiv.Perm (Fin N),μ.map (euclideanPermutation e)=μ)
    (σ : Test (N*d) →ₗ[ℝ] ℝ) (hσE : FiniteEnergy μ σ)
    (hσ : ∀ e : Equiv.Perm (Fin N),∀ φ : Test (N*d),σ (pullTest (euclideanPermutation e) φ)=σ φ)
    {b : Position d → Position d → Position d} (hb : BoundedSmoothKernel b)
    (hx : ∀ a x y,b (x+Pi.single a P) y=b x y)
    (hy : ∀ a x y,b x (y+Pi.single a P)=b x y)
    {f : Point (m*d) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : PeriodicOf P (f ∘ (PeriodicBochner.coordinateEquiv (m*d)).symm)) :
    2*pairing μ (WeightedTangent.representative μ σ).val (splitGenerator hm.le b f)-
      (∫ x,splitGenerator hm.le b (fun y => ‖gradient f y‖^2) x ∂μ) =
    localEnergyTerm P (μ.map (marginalProjection hm.le))
      (prefixSource hm.le μ (WeightedTangent.representative μ σ).val) (internalDrift N b) f+
      (((N:ℝ)-m)/N)*externalEnergyTerm P (μ.map (observation hm.le ⟨m,hm⟩))
        (observedSource hm.le ⟨m,hm⟩ μ (WeightedTangent.representative μ σ).val) b f := by
  have hf2 := BochnerIdentity.smooth_gradient_norm_sq hf
  have hp2 : PeriodicOf P ((fun y => ‖gradient f y‖^2) ∘ (PeriodicBochner.coordinateEquiv (m*d)).symm) := by
    have he : (fun y => ‖gradient f y‖^2) = gramTest f f := by
      funext y
      exact (real_inner_self_eq_norm_sq _).symm
    rw [he]
    exact gramTest_periodic hp hp
  rw [canonical_splitGenerator_periodic_pairing hP hm μ hμ σ hσE hσ hb hx hy hf hp,
    splitGenerator_integral hP hm μ hμ hb hx hy hf2 hp2]
  have hext : interaction b (fun y => ‖gradient f y‖^2) =
      fun z => ⟪liftedForce b z,gradient (fun w => ‖gradient f (prefixProjection (m*d) d w)‖^2) z⟫_ℝ :=
    (lifted_interaction_eq hf2).symm
  rw [hext,show internalGenerator N b f = FiniteGeneratorCalculus.generator (internalDrift N b) f from rfl]
  dsimp only [localEnergyTerm,externalEnergyTerm,internalGenerator,FiniteGeneratorCalculus.generator]
  simp only [real_inner_comm]
  ring

/-- The local internal term agrees under actual prefix-of-observation
marginalization; equality includes its canonical periodic representative. -/
theorem localEnergyTerm_observation (P : ℝ) (hm : m ≤ N) (j : Fin N)
    (μ : Measure (Point (N*d))) [IsFiniteMeasure μ] (U : Lp (Point (N*d)) 2 μ)
    (B : Point (m*d) → Point (m*d)) (f : Point (m*d) → ℝ) :
    localEnergyTerm P (marginalLaw (μ.map (observation hm j)))
      (marginalDistribution (μ.map (observation hm j)) (observedSource hm j μ U)) B f =
    localEnergyTerm P (μ.map (marginalProjection hm)) (prefixSource hm μ U) B f := by
  simp only [marginalDistribution_observedSource,marginalLaw_observation]

end SharpWasserstein.PeriodicMarginalCoefficientEvolution
