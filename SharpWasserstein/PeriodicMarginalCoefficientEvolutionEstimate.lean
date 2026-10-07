module

public import SharpWasserstein.Compat
public import SharpWasserstein.PeriodicMarginalCoefficientEvolutionDecomposition

@[expose] public section

/-! The proved static finite hierarchy evaluated at the actual prefix optimizer.
Only the genuine own-energy gap carries the auxiliary internal drift bound. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace NNReal BigOperators
namespace SharpWasserstein.PeriodicMarginalCoefficientEvolution
open WeightedTangent NoiseAverage PropagatedSourceEquation WeightedMarginal
open PeriodicParticleTangentLimit WeightedPeriodicCoefficientEvolution
open ExternalInteractionPeriodic ExternalInteractionSymmetry PropagatedSourcePermutation ExternalInteraction
open FiniteGradientTrial WeightedPeriodicFourierPhysical RegularizedTrialConvergencePhysical PeriodicFourierTests
variable {d m N : ℕ}

/-- A single finite auxiliary amplitude for the actual internal drift. It is
chosen from proved global bounds, independently of time and the trial space. -/
def internalAmplitude (N : ℕ) {b : Position d → Position d → Position d}
    (hb : BoundedSmoothKernel b) (hm : 0 < m) : ℝ :=
  Classical.choose (internalDrift_allDerivativesBounded (N := N) hb hm).bounded

theorem internalAmplitude_nonneg (N : ℕ) {b : Position d → Position d → Position d}
    (hb : BoundedSmoothKernel b) (hm : 0 < m) : 0 ≤ internalAmplitude N hb hm :=
  (Classical.choose_spec (internalDrift_allDerivativesBounded (N := N) hb hm).bounded).1

theorem internalAmplitude_bound (N : ℕ) {b : Position d → Position d → Position d}
    (hb : BoundedSmoothKernel b) (hm : 0 < m) (x : Point (m*d)) :
    ‖internalDrift N b x‖ ≤ internalAmplitude N hb hm :=
  (Classical.choose_spec (internalDrift_allDerivativesBounded (N := N) hb hm).bounded).2 x

variable [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  [MeasurableSpace (Point (m*d))] [BorelSpace (Point (m*d))]
  [MeasurableSpace (Point (m*d+d))] [BorelSpace (Point (m*d+d))]

/-- Equality of the actual finite optimizer coefficients under true observed
source marginalization. The coefficient space and physical norm are unchanged. -/
theorem observed_solution_eq_prefix (P : ℝ) (hm : m ≤ N) (j : Fin N)
    (μ : Measure (Point (N*d))) [IsFiniteMeasure μ] (σ : Test (N*d) →ₗ[ℝ] ℝ)
    (s : Finset ((Fin (m*d) → ℤ) × Bool)) (δ : ℝ) :
    RegularizedTrialEnergy.solution (trial P (marginalLaw (μ.map (observation hm j))) s) δ
      (WeightedPeriodicTangentPhysical.representative P (marginalLaw (μ.map (observation hm j)))
        (marginalDistribution (μ.map (observation hm j))
          (observedSource hm j μ (WeightedTangent.representative μ σ).val))).val.val =
    RegularizedTrialEnergy.solution (trial P (μ.map (marginalProjection hm)) s) δ
      (periodicPrefixField P hm μ σ) := by
  simp only [marginalDistribution_observedSource,periodicPrefixField]
  have he (ρ τ : Measure (Point (m*d))) [IsFiniteMeasure ρ] [IsFiniteMeasure τ] (h : ρ=τ) :
      RegularizedTrialEnergy.solution (trial P ρ s) δ
        (WeightedPeriodicTangentPhysical.representative P ρ
          (prefixSource hm μ (WeightedTangent.representative μ σ).val)).val.val =
      RegularizedTrialEnergy.solution (trial P τ s) δ
        (WeightedPeriodicTangentPhysical.representative P τ
          (prefixSource hm μ (WeightedTangent.representative μ σ).val)).val.val := by
    subst τ
    rfl
  exact he _ _ (marginalLaw_observation hm j μ)

/-- Actual finite generator derivative bound, after exact source/law/optimizer
identification. The sharp coupling multiplies next energy minus trial energy. -/
theorem finite_splitHierarchy_le {P : ℝ} (hP : 0 < P) (hm : m < N) (hmpos : 1 ≤ m)
    (μ : Measure (Point (N*d))) [IsFiniteMeasure μ]
    (hμ : ∀ e : Equiv.Perm (Fin N),μ.map (euclideanPermutation e)=μ)
    (σ : Test (N*d) →ₗ[ℝ] ℝ) (hσE : FiniteEnergy μ σ)
    (hσ : ∀ e : Equiv.Perm (Fin N),∀ φ : Test (N*d),σ (pullTest (euclideanPermutation e) φ)=σ φ)
    {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
    (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
    (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hx : ∀ a x y,b (x+Pi.single a P) y=b x y)
    (hy : ∀ a x y,b x (y+Pi.single a P)=b x y)
    (s : Finset ((Fin (m*d) → ℤ) × Bool)) {δ : ℝ} (hδ : 0 < δ) :
    let L := Real.sqrt (2*(d:ℝ)*(L₁^2+L₂^2))
    let A := internalAmplitude N hb (lt_of_lt_of_le Nat.zero_lt_one hmpos)
    let T := trial P (μ.map (marginalProjection hm.le)) s
    let U := periodicPrefixField P hm.le μ σ
    let c := RegularizedTrialEnergy.solution T δ U
    let f := potential (fun p : s => physicalPotential P (atom p.val)) c
    let e := RegularizedTrialEnergy.energy T δ U
    let q := 2*(((N:ℝ)-m)/N)*gradientConstant d M L₁ L₂*(m:ℝ)
    2*pairing μ (WeightedTangent.representative μ σ).val (splitGenerator hm.le b f)-
      (∫ x,splitGenerator hm.le b (fun y => ‖gradient f y‖^2) x ∂μ) ≤
    (2*L+2*(d:ℝ)*L₁+1)*e+
      q*(WeightedPeriodicTangentPhysical.energy P (μ.map (observation hm.le ⟨m,hm⟩))
        (observedSource hm.le ⟨m,hm⟩ μ (WeightedTangent.representative μ σ).val)-e)+
      4*(L^2+A^2)*(WeightedPeriodicTangentPhysical.energy P (μ.map (marginalProjection hm.le))
        (prefixSource hm.le μ (WeightedTangent.representative μ σ).val)-e) := by
  let ν := μ.map (observation hm.le ⟨m,hm⟩)
  let σn := observedSource hm.le ⟨m,hm⟩ μ (WeightedTangent.representative μ σ).val
  let a := fun p : s => physicalPotential P (atom p.val)
  let T := trial P (μ.map (marginalProjection hm.le)) s
  let U := periodicPrefixField P hm.le μ σ
  let c := RegularizedTrialEnergy.solution T δ U
  let f := potential a c
  let L := Real.sqrt (2*(d:ℝ)*(L₁^2+L₂^2))
  let A := internalAmplitude N hb (lt_of_lt_of_le Nat.zero_lt_one hmpos)
  let θ := ((N:ℝ)-m)/N
  have hN : (0:ℝ)<N := Nat.cast_pos.mpr (lt_trans (lt_of_lt_of_le Nat.zero_lt_one hmpos) hm)
  have hθ : 0 ≤ θ := div_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr hm.le)) hN.le
  have hθ1 : θ ≤ 1 := (div_le_one hN).mpr (by linarith [Nat.cast_nonneg (α := ℝ) m])
  have ha (p : s) := physicalPotential_smooth P (smooth_atom p.val)
  have hpa (p : s) := physicalPotential_periodic hP.ne' (periodic_atom p.val)
  have hi := PhysicalFourierTrialHierarchy.finite_hierarchy_le P ν σn s hδ hb hbound hmpos hM hL₁ hL₂
    (internalDrift_smooth hb N) (internalDrift_allDerivativesBounded hb (lt_of_lt_of_le Nat.zero_lt_one hmpos))
    (Real.sqrt_nonneg _) (internalAmplitude_nonneg N hb (lt_of_lt_of_le Nat.zero_lt_one hmpos))
    (internalDrift_fderiv_bound hb hbound (lt_of_lt_of_le Nat.zero_lt_one hmpos) hm.le hL₁ hL₂)
    (internalAmplitude_bound N hb (lt_of_lt_of_le Nat.zero_lt_one hmpos)) hθ hθ1
  have hc := observed_solution_eq_prefix P hm.le ⟨m,hm⟩ μ σ s δ
  have he := observed_trialEnergy_eq_prefix P hm.le ⟨m,hm⟩ μ σ a ha
    (fun p => physicalPotential_gradient_bound P _ (smooth_atom p.val) (periodic_atom p.val)) δ
  change RegularizedTrialEnergy.energy (trial P (marginalLaw ν) s) δ
    (WeightedPeriodicTangentPhysical.representative P (marginalLaw ν)
      (marginalDistribution ν σn)).val.val = RegularizedTrialEnergy.energy T δ U at he
  have hE := periodic_marginalEnergy_observedSource P hm.le ⟨m,hm⟩ μ (WeightedTangent.representative μ σ).val
  dsimp only at hi
  change localEnergyTerm P (marginalLaw ν) (marginalDistribution ν σn) (internalDrift N b)
    (potential a (RegularizedTrialEnergy.solution (trial P (marginalLaw ν) s) δ
      (WeightedPeriodicTangentPhysical.representative P (marginalLaw ν) (marginalDistribution ν σn)).val.val))+
    θ*externalEnergyTerm P ν σn b
      (potential a (RegularizedTrialEnergy.solution (trial P (marginalLaw ν) s) δ
        (WeightedPeriodicTangentPhysical.representative P (marginalLaw ν) (marginalDistribution ν σn)).val.val)) ≤ _ at hi
  rw [hc,localEnergyTerm_observation,he,hE] at hi
  have hd := splitEnergyDerivative_eq hP hm μ hμ σ hσE hσ hb hx hy (potential_smooth a ha c)
    (potential_periodic a hpa c)
  dsimp only at hd ⊢
  rw [hd]
  convert hi using 1 <;> dsimp only [T,U,c,f,a,L,A,θ,ν,σn] <;> ring

end SharpWasserstein.PeriodicMarginalCoefficientEvolution
