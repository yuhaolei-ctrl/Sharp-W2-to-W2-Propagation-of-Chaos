module

public import SharpWasserstein.Compat
public import SharpWasserstein.PeriodicMarginalCoefficientEvolutionTerminal

@[expose] public section

/-! The sharp finite Fourier hierarchy along the actual Brownian law and
its actual propagated source. Both the optimized coefficient derivative and
the exact exchangeable marginal generator are derived before taking the
static estimate. No marginal evolution equation or energy derivative is
assumed. The remaining own-level regularization gap is displayed explicitly. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace NNReal BigOperators
namespace SharpWasserstein.PeriodicMarginalCoefficientEvolution
open WeightedTangent NoiseAverage PropagatedSourceEquation
open PeriodicParticleTangentLimit WeightedPeriodicCoefficientEvolution
open ExternalInteractionPeriodic ExternalInteractionSymmetry PropagatedSourcePermutation ExternalInteraction
open FiniteGradientTrial WeightedPeriodicFourierPhysical RegularizedTrialConvergencePhysical PeriodicFourierTests

variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  {b : Position d → Position d → Position d} {M K M' K' : ℝ≥0}
  (hv : Continuous (Function.uncurry (fun _ : ℝ => (particleDrift b : Configuration d N → _))))
  (hb : ∀ _ : ℝ,∀ x : Configuration d N,‖particleDrift b x‖ ≤ M)
  (hl : ∀ _ : ℝ,LipschitzWith K (particleDrift b : Configuration d N → _))
  (hv' : Continuous (Function.uncurry (fun _ : ℝ => equivDrift (configurationEuclidean d N) (particleDrift b))))
  (hb' : ∀ _ : ℝ,∀ y,‖equivDrift (configurationEuclidean d N) (particleDrift b) y‖ ≤ M')
  (hl' : ∀ _ : ℝ,LipschitzWith K' (equivDrift (configurationEuclidean d N) (particleDrift b)))
  {T : ℝ} (hT : 0 ≤ T) (hbs : BoundedSmoothKernel b)
  (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ] (hμ : HasSecondMoment μ)
  {u : Point (N*d) → Point (N*d)} (hu : MemLp u 2 (μ.map (configurationEuclidean d N)))
include hv hb hl hbs hμ hu

/-- The genuine finite marginal energy has the stated derivative on the
closed horizon and satisfies the sharp next-level inequality. Exchangeability
of the carrying law and covariance of the propagated source are consequences
of the corresponding initial data. -/
theorem brownian_periodic_trialEnergy_derivative_le
    {m : ℕ} [MeasurableSpace (Point (m*d))] [BorelSpace (Point (m*d))]
    [MeasurableSpace (Point (m*d+d))] [BorelSpace (Point (m*d+d))]
    {P : ℝ} (hP : 0 < P) (hm : m < N) (hmpos : 1 ≤ m) (hex : Exchangeable μ)
    (hue : ∀ e : Equiv.Perm (Fin N),∀ᵐ x ∂μ.map (configurationEuclidean d N),
      u (euclideanPermutation e x)=euclideanPermutation e (u x))
    {Mb L₁ L₂ : ℝ} (hbound : KernelBounds b Mb L₁ L₂)
    (hM : 0 ≤ Mb) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hx : ∀ a x y,b (x+Pi.single a P) y=b x y)
    (hy : ∀ a x y,b x (y+Pi.single a P)=b x y)
    (s : Finset ((Fin (m*d) → ℤ) × Bool)) {δ : ℝ} (hδ : 0 < δ)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    let ν := fun r => Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) r
    let σ := fun r => Brownian.sourceAt hv' hb' hl' hT (particleDrift_smooth hbs)
      (particleDrift_allDerivativesBounded hbs) (μ.map (configurationEuclidean d N)) u hu r
    let e := fun r => RegularizedTrialEnergy.energy
      (trial P ((ν r).map (marginalProjection hm.le)) s) δ (periodicPrefixField P hm.le (ν r) (σ r))
    let E := WeightedPeriodicTangentPhysical.energy P ((ν t).map (marginalProjection hm.le))
      (prefixSource hm.le (ν t) (WeightedTangent.representative (ν t) (σ t)).val)
    let E_next := WeightedPeriodicTangentPhysical.energy P ((ν t).map (observation hm.le ⟨m,hm⟩))
      (observedSource hm.le ⟨m,hm⟩ (ν t) (WeightedTangent.representative (ν t) (σ t)).val)
    let L := Real.sqrt (2*(d:ℝ)*(L₁^2+L₂^2))
    let A := internalAmplitude N hbs (lt_of_lt_of_le Nat.zero_lt_one hmpos)
    let q := 2*(((N:ℝ)-m)/N)*gradientConstant d Mb L₁ L₂*(m:ℝ)
    ∃ e', HasDerivWithinAt e e' (Icc 0 T) t ∧
      e' ≤ (2*L+2*(d:ℝ)*L₁+1)*e t + q*(E_next-e t)+4*(L^2+A^2)*(E-e t) := by
  let ν := Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) t
  let σ := Brownian.sourceAt hv' hb' hl' hT (particleDrift_smooth hbs)
    (particleDrift_allDerivativesBounded hbs) (μ.map (configurationEuclidean d N)) u hu t
  let a := fun p : s => physicalPotential P (atom p.val)
  have ha (p : s) := physicalPotential_smooth P (smooth_atom p.val)
  have hpa (p : s) := physicalPotential_periodic hP.ne' (periodic_atom p.val)
  have hν (e : Equiv.Perm (Fin N)) : ν.map (euclideanPermutation e)=ν :=
    brownian_lawAt_permutation hv' hb' hl' hT _ e (euclideanLaw_permutation μ hex e) t
  have hσ (e : Equiv.Perm (Fin N)) (φ : Test (N*d)) :
      σ (pullTest (euclideanPermutation e) φ)=σ φ :=
    particle_sourceAt_invariant hbs hv' hb' hl' hT _ e (euclideanLaw_permutation μ hex e)
      u hu (hue e) t φ
  have hσE : FiniteEnergy ν σ :=
    (Brownian.sourceAt_finiteEnergy_and_energy_le hv' hb' hl' hT
      (particleDrift_smooth hbs) (particleDrift_allDerivativesBounded hbs)
      (μ.map (configurationEuclidean d N)) u hu ht).1
  have hd := brownian_periodic_trialEnergy_splitGenerator hv hb hl hv' hb' hl' hT hbs μ hμ
    a ha hu hP hm.le hpa hδ ht
  have hi := finite_splitHierarchy_le hP hm hmpos ν hν σ hσE hσ hbs hbound hM hL₁ hL₂ hx hy s hδ
  dsimp only at hd hi ⊢
  exact ⟨_,hd,hi⟩

/-- The actual terminal Brownian trial energy has no next-level term. The
same baseline constant is retained, with only its own regularization gap. -/
theorem brownian_periodic_trialEnergy_terminal_derivative_le
    {P : ℝ} (hP : 0 < P) (hN : 1 ≤ N)
    {Mb L₁ L₂ : ℝ} (hbound : KernelBounds b Mb L₁ L₂)
    (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hx : ∀ a x y,b (x+Pi.single a P) y=b x y)
    (hy : ∀ a x y,b x (y+Pi.single a P)=b x y)
    (s : Finset ((Fin (N*d) → ℤ) × Bool)) {δ : ℝ} (hδ : 0 < δ)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    let ν := fun r => Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) r
    let σ := fun r => Brownian.sourceAt hv' hb' hl' hT (particleDrift_smooth hbs)
      (particleDrift_allDerivativesBounded hbs) (μ.map (configurationEuclidean d N)) u hu r
    let e := fun r => RegularizedTrialEnergy.energy
      (trial P ((ν r).map (marginalProjection (k := N) le_rfl)) s) δ
      (periodicPrefixField P le_rfl (ν r) (σ r))
    let E := WeightedPeriodicTangentPhysical.energy P ((ν t).map (marginalProjection (k := N) le_rfl))
      (prefixSource le_rfl (ν t) (WeightedTangent.representative (ν t) (σ t)).val)
    let L := Real.sqrt (2*(d:ℝ)*(L₁^2+L₂^2))
    let A := internalAmplitude N hbs (lt_of_lt_of_le Nat.zero_lt_one hN)
    ∃ e', HasDerivWithinAt e e' (Icc 0 T) t ∧
      e' ≤ (2*L+2*(d:ℝ)*L₁+1)*e t +4*(L^2+A^2)*(E-e t) := by
  let ν := Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) t
  let σ := Brownian.sourceAt hv' hb' hl' hT (particleDrift_smooth hbs)
    (particleDrift_allDerivativesBounded hbs) (μ.map (configurationEuclidean d N)) u hu t
  let a := fun p : s => physicalPotential P (atom p.val)
  have ha (p : s) := physicalPotential_smooth P (smooth_atom p.val)
  have hpa (p : s) := physicalPotential_periodic hP.ne' (periodic_atom p.val)
  have hd := brownian_periodic_trialEnergy_splitGenerator hv hb hl hv' hb' hl' hT hbs μ hμ
    a ha hu hP le_rfl hpa hδ ht
  have hi := finite_terminal_splitHierarchy_le hP hN ν σ hbs hbound hL₁ hL₂ hx hy s hδ
  dsimp only at hd hi ⊢
  exact ⟨_,hd,hi⟩

end SharpWasserstein.PeriodicMarginalCoefficientEvolution
