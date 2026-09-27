import SharpWasserstein.BrownianEnergyPeriodizationIdentification

/-! The genuine sine-kernel/Jacobian limit for full Brownian marginal energy.
Every approximation propagates the same initial L² field, under the same
initial law and Brownian paths; the common bound is passed by the established
varying-measure lower semicontinuity theorem. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal Topology
namespace SharpWasserstein.BrownianEnergyPeriodization
open WeightedTangent PropagatedSourceEquation PeriodicParticleTangentLimit
open InitialSourceMarginal
variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
  (hN : 0 < N) (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
  (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) {T : ℝ} (hT : 0 ≤ T)
  (μ : Measure (Point (N*d))) [IsFiniteMeasure μ]

def carryingLaw (t : ℝ) : Measure (Point (N*d)) :=
  Brownian.lawAt ((drift_lipschitz hN hb hbound hL₁ hL₂).continuous.comp continuous_snd)
    (fun _ => drift_norm_le hN hbound hM) (fun _ => drift_lipschitz hN hb hbound hL₁ hL₂) hT μ t

instance carryingLaw_finite (t : ℝ) :
    IsFiniteMeasure (carryingLaw hN hb hbound hM hL₁ hL₂ hT μ t) := by
  unfold carryingLaw
  infer_instance

def propagatedSource (u : Point (N*d) → Point (N*d)) (hu : MemLp u 2 μ) (t : ℝ) :
    Test (N*d) →ₗ[ℝ] ℝ :=
  Brownian.sourceAt ((drift_lipschitz hN hb hbound hL₁ hL₂).continuous.comp continuous_snd)
    (fun _ => drift_norm_le hN hbound hM) (fun _ => drift_lipschitz hN hb hbound hL₁ hL₂)
    hT (particleDrift_smooth hb) (particleDrift_allDerivativesBounded hb) μ u hu t

def prefixEnergy {k : ℕ} [MeasurableSpace (Point (k*d))] [BorelSpace (Point (k*d))]
    (hk : k ≤ N) (u : Point (N*d) → Point (N*d)) (hu : MemLp u 2 μ) (t : ℝ) : ℝ :=
  energy ((carryingLaw hN hb hbound hM hL₁ hL₂ hT μ t).map (marginalProjection hk))
    (imageSource (carryingLaw hN hb hbound hM hL₁ hL₂ hT μ t)
      (propagatedSource hN hb hbound hM hL₁ hL₂ hT μ u hu t) (marginalProjection hk))

/-- Full Euclidean energy agrees exactly with the true projected-Jacobian
source and carrying law whose convergence has already been proved. -/
theorem prefixEnergy_eq_projectedEnergy {k : ℕ}
    [MeasurableSpace (Point (k*d))] [BorelSpace (Point (k*d))]
    (hk : k ≤ N) (u : Point (N*d) → Point (N*d)) (hu : MemLp u 2 μ)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    prefixEnergy hN hb hbound hM hL₁ hL₂ hT μ hk u hu t =
      energy (law hN hb hbound hM hL₁ hL₂ hT (euclideanBrownianPathLaw d N T) μ
        (marginalProjection hk) (t := t))
        (source hN hb hbound hM hL₁ hL₂ hT (euclideanBrownianPathLaw d N T) μ
          (marginalProjection hk) ht u hu) := by
  rw [projectedSource_eq_brownianImage hN hb hbound hM hL₁ hL₂ hT μ _ ht,
    projectedLaw_eq_brownianMap hN hb hbound hM hL₁ hL₂ hT μ _ ht]
  rfl

/-- A common actual full Brownian marginal bound for the sine kernels passes
to the original kernel. Initial fields are literally identical in every term. -/
theorem prefixEnergy_le_of_sine_bounds [IsProbabilityMeasure μ] {k : ℕ}
    [MeasurableSpace (Point (k*d))] [BorelSpace (Point (k*d))]
    (hk : k ≤ N) (u : Point (N*d) → Point (N*d)) (hu : MemLp u 2 μ)
    {t : ℝ} (ht : t ∈ Icc 0 T) {C : ℝ}
    (hC : ∀ᶠ n in atTop,prefixEnergy hN (PeriodicParticle.interaction_smooth hb n)
      (PeriodicParticle.interaction_bounds hb hbound hL₁ hL₂ n) hM hL₁ hL₂ hT μ hk u hu t ≤ C) :
    prefixEnergy hN hb hbound hM hL₁ hL₂ hT μ hk u hu t ≤ C := by
  rw [prefixEnergy_eq_projectedEnergy hN hb hbound hM hL₁ hL₂ hT μ hk u hu ht]
  apply (marginalEnergy_bound_of_periodic_bounds hN hb hbound hM hL₁ hL₂ hT hk μ
    (euclideanBrownianPathLaw d N T) u hu ht ?_).2
  filter_upwards [hC] with n hn
  rwa [prefixEnergy_eq_projectedEnergy hN (PeriodicParticle.interaction_smooth hb n)
    (PeriodicParticle.interaction_bounds hb hbound hL₁ hL₂ n) hM hL₁ hL₂ hT μ hk u hu ht] at hn

end SharpWasserstein.BrownianEnergyPeriodization
