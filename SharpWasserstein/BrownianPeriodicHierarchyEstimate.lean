module

public import SharpWasserstein.Compat
public import SharpWasserstein.BrownianPeriodicHierarchyRecovery
public import SharpWasserstein.BrownianPeriodicHierarchyReindex
public import SharpWasserstein.BrownianPeriodicHierarchyConstants
public import SharpWasserstein.PeriodicMarginalCoefficientEvolutionHierarchy

@[expose] public section

/-! The proved Brownian finite coefficient inequality, expressed for the
canonical exhaustion energies and genuine consecutive particle levels. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace NNReal
namespace SharpWasserstein.BrownianPeriodicHierarchy
open WeightedTangent PropagatedSourceEquation NoiseAverage PeriodicParticleTangentLimit
open PeriodicMarginalCoefficientEvolution RegularizedTrialConvergence
open PropagatedSourcePermutation VolterraFourier

/-- Equality with the literal valid prefix energy. -/
theorem periodicEnergy_level_eq {d N m : ℕ} (P : ℝ) (hm : m ≤ N)
    (ν : Measure (Point (N*d))) [IsFiniteMeasure ν] (σ : Test (N*d) →ₗ[ℝ] ℝ) :
    WeightedPeriodicTangentPhysical.energy P (levelLaw d N ν m) (levelSource d N ν σ m) =
    WeightedPeriodicTangentPhysical.energy P (ν.map (marginalProjection hm))
      (prefixSource hm ν (representative ν σ).val) := by
  have hh := congrArg (fun A : Point (N*d) →L[ℝ] Point (m*d) =>
    WeightedPeriodicTangentPhysical.energy P (ν.map A)
      (InitialSourceMarginal.imageSource ν σ A)) (levelProjection_eq hm)
  simpa only [levelLaw,levelSource,prefixSource_eq_imageSource] using hh

/-- A finite auxiliary constant multiplying an actual vanishing Fourier gap. -/
def gapCoefficient {d : ℕ} (N : ℕ) {b : Position d → Position d → Position d}
    (hbs : BoundedSmoothKernel b) (L₁ L₂ : ℝ) (m : ℕ) : ℝ :=
  if hm : 0 < m then 4*((driftLipschitz d L₁ L₂)^2+(internalAmplitude N hbs hm)^2) else 0

variable {d N : ℕ} {b : Position d → Position d → Position d} {M K M' K' : ℝ≥0}
  (hv : Continuous (Function.uncurry (fun _ : ℝ => (particleDrift b : Configuration d N → _))))
  (hb : ∀ _ : ℝ,∀ x : Configuration d N,‖particleDrift b x‖ ≤ M)
  (hl : ∀ _ : ℝ,LipschitzWith K (particleDrift b : Configuration d N → _))
  (hv' : Continuous (Function.uncurry (fun _ : ℝ => equivDrift (configurationEuclidean d N) (particleDrift b))))
  (hb' : ∀ _ : ℝ,∀ y,‖equivDrift (configurationEuclidean d N) (particleDrift b) y‖ ≤ M')
  (hl' : ∀ _ : ℝ,LipschitzWith K' (equivDrift (configurationEuclidean d N) (particleDrift b)))
  {T : ℝ} (hT : 0 ≤ T) (hbs : BoundedSmoothKernel b)
  (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ] (hμ : HasSecondMoment μ)
  {u : Point (N*d) → Point (N*d)} (hu : MemLp u 2 (μ.map (configurationEuclidean d N)))


include hv hb hl hμ in
/-- Ordinary scalar derivatives satisfy the actual lower-level hierarchy. -/
theorem brownianFiniteEnergy_deriv_le {P : ℝ} (hP : 0 < P) {m : ℕ}
    (hm : m < N) (hmpos : 1 ≤ m) (hex : Exchangeable μ)
    (hue : ∀ e : Equiv.Perm (Fin N),∀ᵐ x ∂μ.map (configurationEuclidean d N),
      u (euclideanPermutation e x)=euclideanPermutation e (u x))
    {Mb L₁ L₂ : ℝ} (hbound : KernelBounds b Mb L₁ L₂)
    (hM : 0 ≤ Mb) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hx : ∀ a x y,b (x+Pi.single a P) y=b x y)
    (hy : ∀ a x y,b x (y+Pi.single a P)=b x y)
    (j : ℕ) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    deriv (brownianFiniteEnergy hv' hb' hl' hT hbs μ hu P m j) t ≤
      baseline d L₁ L₂*brownianFiniteEnergy hv' hb' hl' hT hbs μ hu P m j t+
      rate d Mb L₁ L₂ N m*(brownianPeriodicEnergy hv' hb' hl' hT hbs μ hu P (m+1) t-
        brownianFiniteEnergy hv' hb' hl' hT hbs μ hu P m j t)+
      gapCoefficient N hbs L₁ L₂ m*(brownianPeriodicEnergy hv' hb' hl' hT hbs μ hu P m t-
        brownianFiniteEnergy hv' hb' hl' hT hbs μ hu P m j t) := by
  obtain ⟨e',he,hi⟩ := brownian_periodic_trialEnergy_derivative_le hv hb hl hv' hb' hl' hT hbs μ hμ hu
    hP hm hmpos hex hue hbound hM hL₁ hL₂ hx hy
    (exhaustion ((Fin (m*d) → ℤ) × Bool) j) (penalty_pos j) ⟨ht.1.le,ht.2.le⟩
  have hd : HasDerivAt (brownianFiniteEnergy hv' hb' hl' hT hbs μ hu P m j) e' t := by
    apply (he.congr_of_mem (fun r _ => ?_) ⟨ht.1.le,ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    exact sourceFiniteEnergy_level_eq P hm.le _ _ j r
  rw [hd.deriv]
  dsimp only at hi
  rw [observed_nextEnergy hm] at hi
  simpa only [brownianFiniteEnergy,sourceFiniteEnergy_level_eq P hm.le,
    brownianPeriodicEnergy,periodicEnergy_level_eq P hm.le,
    periodicEnergy_level_eq P (Nat.succ_le_of_lt hm),
    baseline,driftLipschitz,rate,externalFraction,gapCoefficient,
    dif_pos (lt_of_lt_of_le Nat.zero_lt_one hmpos)] using hi

include hv hb hl hμ in
/-- The genuine terminal scalar energy derivative contains only its own gap. -/
theorem brownianFiniteEnergy_terminal_deriv_le {P : ℝ} (hP : 0 < P) (hN : 1 ≤ N)
    {Mb L₁ L₂ : ℝ} (hbound : KernelBounds b Mb L₁ L₂)
    (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hx : ∀ a x y,b (x+Pi.single a P) y=b x y)
    (hy : ∀ a x y,b x (y+Pi.single a P)=b x y)
    (j : ℕ) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    deriv (brownianFiniteEnergy hv' hb' hl' hT hbs μ hu P N j) t ≤
      baseline d L₁ L₂*brownianFiniteEnergy hv' hb' hl' hT hbs μ hu P N j t+
      gapCoefficient N hbs L₁ L₂ N*(brownianPeriodicEnergy hv' hb' hl' hT hbs μ hu P N t-
        brownianFiniteEnergy hv' hb' hl' hT hbs μ hu P N j t) := by
  obtain ⟨e',he,hi⟩ := brownian_periodic_trialEnergy_terminal_derivative_le hv hb hl hv' hb' hl' hT hbs μ hμ hu
    hP hN hbound hL₁ hL₂ hx hy
    (exhaustion ((Fin (N*d) → ℤ) × Bool) j) (penalty_pos j) ⟨ht.1.le,ht.2.le⟩
  have hd : HasDerivAt (brownianFiniteEnergy hv' hb' hl' hT hbs μ hu P N j) e' t := by
    apply (he.congr_of_mem (fun r _ => ?_) ⟨ht.1.le,ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    exact sourceFiniteEnergy_level_eq P le_rfl _ _ j r
  rw [hd.deriv]
  dsimp only at hi
  simpa only [brownianFiniteEnergy,sourceFiniteEnergy_level_eq P (le_rfl : N ≤ N),
    brownianPeriodicEnergy,periodicEnergy_level_eq P (le_rfl : N ≤ N),
    baseline,driftLipschitz,gapCoefficient,
    dif_pos (lt_of_lt_of_le Nat.zero_lt_one hN)] using hi

end SharpWasserstein.BrownianPeriodicHierarchy
