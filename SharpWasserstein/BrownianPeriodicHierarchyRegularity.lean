module

public import SharpWasserstein.Compat
public import SharpWasserstein.BrownianPeriodicHierarchyMarginals
public import SharpWasserstein.PeriodicMarginalCoefficientEvolutionEnergy
public import SharpWasserstein.VolterraFourierSource

@[expose] public section

/-! Actual scalar regularity of the physical Fourier trial energies along the
Brownian source flow. Only the initial current is supplied as an L² function;
no regularity or measurable selection of the varying Riesz tangents is assumed. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace NNReal
namespace SharpWasserstein.BrownianPeriodicHierarchy
open WeightedTangent PropagatedSourceEquation NoiseAverage PeriodicParticleTangentLimit
open PeriodicMarginalCoefficientEvolution WeightedPeriodicFourierPhysical
open PeriodicFourierTests RegularizedTrialConvergence VolterraFourier

theorem trialEnergy_measure_congr {n : ℕ} (P : ℝ)
    (ν τ : Measure (Point n)) [IsFiniteMeasure ν] [IsFiniteMeasure τ] (h : ν = τ)
    (σ : Test n →ₗ[ℝ] ℝ) (j : ℕ) :
    RegularizedTrialEnergy.energy
      (RegularizedTrialConvergencePhysical.trial P ν (exhaustion ((Fin n → ℤ) × Bool) j))
      (penalty j) (WeightedPeriodicTangentPhysical.representative P ν σ).val.val =
    RegularizedTrialEnergy.energy
      (RegularizedTrialConvergencePhysical.trial P τ (exhaustion ((Fin n → ℤ) × Bool) j))
      (penalty j) (WeightedPeriodicTangentPhysical.representative P τ σ).val.val := by
  subst τ
  rfl

/-- The total level family is literally the prefix trial problem at each valid level. -/
theorem sourceFiniteEnergy_level_eq {d N m : ℕ} (P : ℝ) (hm : m ≤ N)
    (ν : ℝ → Measure (Point (N*d))) [∀ r,IsFiniteMeasure (ν r)]
    (σ : ℝ → Test (N*d) →ₗ[ℝ] ℝ) (j : ℕ) (r : ℝ) :
    sourceFiniteEnergy P (fun r => levelLaw d N (ν r) m)
      (fun r => levelSource d N (ν r) (σ r) m) j r =
    RegularizedTrialEnergy.energy
      (RegularizedTrialConvergencePhysical.trial P ((ν r).map (marginalProjection hm))
        (exhaustion ((Fin (m*d) → ℤ) × Bool) j)) (penalty j)
      (periodicPrefixField P hm (ν r) (σ r)) := by
  have hh := congrArg (fun A : Point (N*d) →L[ℝ] Point (m*d) =>
    RegularizedTrialEnergy.energy
      (RegularizedTrialConvergencePhysical.trial P ((ν r).map A)
        (exhaustion ((Fin (m*d) → ℤ) × Bool) j)) (penalty j)
      (WeightedPeriodicTangentPhysical.representative P ((ν r).map A)
        (InitialSourceMarginal.imageSource (ν r) (σ r) A)).val.val) (levelProjection_eq hm)
  simp only [sourceFiniteEnergy,finiteEnergy,sourceRepresentative,levelLaw,levelSource,
    periodicPrefixField,prefixSource_eq_imageSource]
  convert hh using 1

variable {d N m : ℕ} {b : Position d → Position d → Position d} {M K M' K' : ℝ≥0}
  (hv : Continuous (Function.uncurry (fun _ : ℝ => (particleDrift b : Configuration d N → _))))
  (hb : ∀ _ : ℝ,∀ x : Configuration d N,‖particleDrift b x‖ ≤ M)
  (hl : ∀ _ : ℝ,LipschitzWith K (particleDrift b : Configuration d N → _))
  (hv' : Continuous (Function.uncurry (fun _ : ℝ => equivDrift (configurationEuclidean d N) (particleDrift b))))
  (hb' : ∀ _ : ℝ,∀ y,‖equivDrift (configurationEuclidean d N) (particleDrift b) y‖ ≤ M')
  (hl' : ∀ _ : ℝ,LipschitzWith K' (equivDrift (configurationEuclidean d N) (particleDrift b)))
  {T : ℝ} (hT : 0 ≤ T) (hbs : BoundedSmoothKernel b)
  (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ] (hμ : HasSecondMoment μ)
  {u : Point (N*d) → Point (N*d)} (hu : MemLp u 2 (μ.map (configurationEuclidean d N)))

/-- A convenient name for the exact energies used by Volterra recovery. -/
def brownianFiniteEnergy (P : ℝ) (m j : ℕ) (r : ℝ) : ℝ :=
  sourceFiniteEnergy P
    (fun t => levelLaw d N (Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) t) m)
    (fun t => levelSource d N (Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) t)
      (Brownian.sourceAt hv' hb' hl' hT (particleDrift_smooth hbs)
        (particleDrift_allDerivativesBounded hbs) (μ.map (configurationEuclidean d N)) u hu t) m) j r

include hv hb hl hμ in
/-- The finite energy possesses an actual derivative on the closed horizon. -/
theorem brownianFiniteEnergy_hasDerivWithinAt {P : ℝ} (hP : 0 < P) (hm : m ≤ N)
    (j : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∃ e',HasDerivWithinAt (brownianFiniteEnergy hv' hb' hl' hT hbs μ hu P m j) e' (Icc 0 T) t := by
  let s := exhaustion ((Fin (m*d) → ℤ) × Bool) j
  let a := fun p : s => physicalPotential P (atom p.val)
  have ha : ∀ p,ContDiff ℝ ∞ (a p) := fun p => physicalPotential_smooth P (smooth_atom p.val)
  have hp : ∀ p,WeightedPeriodicFourierScale.PeriodicOf P
      (a p ∘ (PeriodicBochner.coordinateEquiv (m*d)).symm) :=
    fun p => ExternalInteractionPeriodic.physicalPotential_periodic hP.ne' (periodic_atom p.val)
  have hd := brownian_periodic_trialEnergy_hasDerivWithinAt hv hb hl hv' hb' hl' hT hbs μ hμ
    a ha hu hP hm hp (penalty_pos j) ht
  dsimp only at hd
  refine ⟨_,hd.congr_of_mem (fun r _ => ?_) ht⟩
  rw [brownianFiniteEnergy,sourceFiniteEnergy_level_eq P hm]
  rfl

include hv hb hl hμ in
/-- Continuity is derived from the genuine coefficient evolution at every
point of the compact horizon, including its endpoints. -/
theorem brownianFiniteEnergy_continuousOn {P : ℝ} (hP : 0 < P) (hm : m ≤ N) (j : ℕ) :
    ContinuousOn (brownianFiniteEnergy hv' hb' hl' hT hbs μ hu P m j) (Icc 0 T) := by
  intro t ht
  obtain ⟨e',he⟩ := brownianFiniteEnergy_hasDerivWithinAt hv hb hl hv' hb' hl' hT hbs μ hμ hu hP hm j ht
  exact he.continuousWithinAt

include hv hb hl hμ in
/-- On the open horizon, the scalar derivative is its ordinary real derivative. -/
theorem brownianFiniteEnergy_hasDerivAt {P : ℝ} (hP : 0 < P) (hm : m ≤ N) (j : ℕ)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt (brownianFiniteEnergy hv' hb' hl' hT hbs μ hu P m j)
      (deriv (brownianFiniteEnergy hv' hb' hl' hT hbs μ hu P m j) t) t := by
  obtain ⟨e',he⟩ := brownianFiniteEnergy_hasDerivWithinAt hv hb hl hv' hb' hl' hT hbs μ hμ hu
    hP hm j ⟨ht.1.le,ht.2.le⟩
  have hd := he.hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  simpa only [hd.deriv] using hd

end SharpWasserstein.BrownianPeriodicHierarchy
