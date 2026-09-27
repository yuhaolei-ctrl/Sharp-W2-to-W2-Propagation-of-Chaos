import SharpWasserstein.BrownianPeriodicHierarchyRegularity

/-! Integrability and actual L¹ Fourier recovery for the propagated periodic
marginal source energies, derived from scalar trial continuity and the actual
initial-current L² bound. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace NNReal Topology
namespace SharpWasserstein.BrownianPeriodicHierarchy
open WeightedTangent PropagatedSourceEquation NoiseAverage
open VolterraFourier

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


/-- Actual physical periodic energy of the genuine m-particle source. -/
def brownianPeriodicEnergy (P : ℝ) (m : ℕ) (r : ℝ) : ℝ :=
  let ν := Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) r
  let σ := Brownian.sourceAt hv' hb' hl' hT (particleDrift_smooth hbs)
    (particleDrift_allDerivativesBounded hbs) (μ.map (configurationEuclidean d N)) u hu r
  WeightedPeriodicTangentPhysical.energy P (levelLaw d N ν m) (levelSource d N ν σ m)

include hv hb hl hμ in
/-- Genuine scalar energy integrability; the varying weighted representative
requires no measurable-vector assumption. -/
theorem brownianPeriodicEnergy_intervalIntegrable {P : ℝ} (hP : 0 < P) (hm : m ≤ N) :
    IntervalIntegrable (brownianPeriodicEnergy hv' hb' hl' hT hbs μ hu P m) volume 0 T := by
  let ν := fun r => levelLaw d N
    (Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) r) m
  let σ := fun r => levelSource d N
    (Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) r)
    (Brownian.sourceAt hv' hb' hl' hT (particleDrift_smooth hbs)
      (particleDrift_allDerivativesBounded hbs) (μ.map (configurationEuclidean d N)) u hu r) m
  let B := Real.exp ((K':ℝ)*T)^2*(∫ x,‖u x‖^2 ∂(μ.map (configurationEuclidean d N)))
  have he (j : ℕ) : AEStronglyMeasurable (sourceFiniteEnergy P ν σ j) (volume.restrict (Icc 0 T)) :=
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hT).mp
      ((brownianFiniteEnergy_continuousOn hv hb hl hv' hb' hl' hT hbs μ hμ hu hP hm j).intervalIntegrable_of_Icc hT)).aestronglyMeasurable
  have hh := sourceEnergy_integrable_of_full_bound P ν σ (volume.restrict (Icc 0 T))
    (show ∀ᵐ r ∂volume.restrict (Icc 0 T),FiniteEnergy (ν r) (σ r) from
      Eventually.of_forall (fun r => levelSource_finite _ _ _ _ _)) he
    (B := fun _ => B) (integrable_const B) (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      exact (brownian_level_energy_bound_flux hv' hb' hl' hT (particleDrift_smooth hbs)
        (particleDrift_allDerivativesBounded hbs) (μ.map (configurationEuclidean d N)) u hu m hr).2)
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mpr hh

include hv hb hl hμ in
/-- The actual finite Fourier energy errors vanish in L¹ in time. -/
theorem brownianPeriodicEnergy_gap_tendsto {P : ℝ} (hP : 0 < P) (hm : m ≤ N) :
    Tendsto (fun j => ∫ r,‖brownianPeriodicEnergy hv' hb' hl' hT hbs μ hu P m r-
      brownianFiniteEnergy hv' hb' hl' hT hbs μ hu P m j r‖ ∂volume.restrict (Icc 0 T))
      atTop (𝓝 0) := by
  let ν := fun r => levelLaw d N
    (Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) r) m
  let σ := fun r => levelSource d N
    (Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) r)
    (Brownian.sourceAt hv' hb' hl' hT (particleDrift_smooth hbs)
      (particleDrift_allDerivativesBounded hbs) (μ.map (configurationEuclidean d N)) u hu r) m
  let B := Real.exp ((K':ℝ)*T)^2*(∫ x,‖u x‖^2 ∂(μ.map (configurationEuclidean d N)))
  have he (j : ℕ) : AEStronglyMeasurable (sourceFiniteEnergy P ν σ j) (volume.restrict (Icc 0 T)) :=
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hT).mp
      ((brownianFiniteEnergy_continuousOn hv hb hl hv' hb' hl' hT hbs μ hμ hu hP hm j).intervalIntegrable_of_Icc hT)).aestronglyMeasurable
  exact source_gap_tendsto_of_full_bound P ν σ (volume.restrict (Icc 0 T))
    (Eventually.of_forall (fun r => levelSource_finite _ _ _ _ _)) he
    (B := fun _ => B) (integrable_const B) (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      exact (brownian_level_energy_bound_flux hv' hb' hl' hT (particleDrift_smooth hbs)
        (particleDrift_allDerivativesBounded hbs) (μ.map (configurationEuclidean d N)) u hu m hr).2)

end SharpWasserstein.BrownianPeriodicHierarchy
