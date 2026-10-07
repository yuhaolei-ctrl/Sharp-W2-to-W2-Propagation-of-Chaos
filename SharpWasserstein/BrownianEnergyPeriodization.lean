module

public import SharpWasserstein.Compat
public import SharpWasserstein.BrownianEnergyPeriodizationPeriodic

@[expose] public section

/-! Genuine full Euclidean propagation of the quadratic marginal source
profile for the original nonperiodic bounded smooth interaction kernel.
The same initial current and distribution are propagated in every sine
approximation. The comparison coefficient depends only on d,M,L₁,L₂. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace NNReal
namespace SharpWasserstein.BrownianEnergyPeriodization
open WeightedTangent PropagatedSourceEquation PeriodicParticleTangentLimit
open InitialSourceMarginal BrownianPeriodicHierarchy PropagatedSourcePermutation NoiseAverage

variable {d N : ℕ} {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
  (hN : 0 < N) (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
  (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) {T : ℝ} (hT : 0 ≤ T)
  (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ] (hμ : HasSecondMoment μ)
  {u : Point (N*d) → Point (N*d)} (hu : MemLp u 2 (μ.map (configurationEuclidean d N)))

include hμ in
/-- Sharp full Euclidean all-level propagation for the original interaction.
No periodicity, positive density, limiting hierarchy, or optimizer regularity
is assumed. Every initial and propagated source is a literal distribution
of the same actual L² current. -/
theorem prefixEnergy_quadratic_bound
    (hex : Exchangeable μ)
    (hue : ∀ e : Equiv.Perm (Fin N),∀ᵐ x ∂μ.map (configurationEuclidean d N),
      u (euclideanPermutation e x)=euclideanPermutation e (u x))
    {A : ℝ} (hA : 0 ≤ A) (σ₀ : Test (N*d) →ₗ[ℝ] ℝ)
    (hσ₀ : ∀ φ : Test (N*d),σ₀ φ = ∫ x,⟪gradient φ.val x,u x⟫_ℝ ∂μ.map (configurationEuclidean d N))
    (hinit : ∀ k,1 ≤ k → k ≤ N →
      energy (levelLaw d N (μ.map (configurationEuclidean d N)) k)
        (levelSource d N (μ.map (configurationEuclidean d N)) σ₀ k) ≤ A*(k:ℝ)^2/(N:ℝ)^2)
    {k : ℕ} (hkpos : 1 ≤ k) (hk : k ≤ N) {t : ℝ} (ht : t ∈ Icc 0 T) :
    prefixEnergy hN hb hbound hM hL₁ hL₂ hT (μ.map (configurationEuclidean d N)) hk u hu t ≤
      A*Real.exp (4*comparisonConstant d M L₁ L₂*t)*(k:ℝ)^2/(N:ℝ)^2 := by
  letI : IsProbabilityMeasure (μ.map (configurationEuclidean d N)) :=
    Measure.isProbabilityMeasure_map (configurationEuclidean d N).continuous.measurable.aemeasurable
  apply prefixEnergy_le_of_sine_bounds hN hb hbound hM hL₁ hL₂ hT
    (μ.map (configurationEuclidean d N)) hk u hu ht
  apply Eventually.of_forall
  intro n
  exact periodic_prefixEnergy_quadratic_bound hN (PeriodicParticle.interaction_smooth hb n)
    (PeriodicParticle.interaction_bounds hb hbound hL₁ hL₂ n) hM hL₁ hL₂ hT μ hμ hu
    (P := 2*Real.pi*((n:ℝ)+1)) (by positivity) hex hue hA
    (SinePeriodization.kernel_periodic_first (by positivity) b)
    (SinePeriodization.kernel_periodic_second (by positivity) b)
    σ₀ hσ₀ hinit hkpos hk ht

include hμ in
/-- The same bound directly for the source/law used in actual projected
Jacobian propagation and marginal Wasserstein approximation. -/
theorem projectedSource_quadratic_bound
    (hex : Exchangeable μ)
    (hue : ∀ e : Equiv.Perm (Fin N),∀ᵐ x ∂μ.map (configurationEuclidean d N),
      u (euclideanPermutation e x)=euclideanPermutation e (u x))
    {A : ℝ} (hA : 0 ≤ A) (σ₀ : Test (N*d) →ₗ[ℝ] ℝ)
    (hσ₀ : ∀ φ : Test (N*d),σ₀ φ = ∫ x,⟪gradient φ.val x,u x⟫_ℝ ∂μ.map (configurationEuclidean d N))
    (hinit : ∀ k,1 ≤ k → k ≤ N →
      energy (levelLaw d N (μ.map (configurationEuclidean d N)) k)
        (levelSource d N (μ.map (configurationEuclidean d N)) σ₀ k) ≤ A*(k:ℝ)^2/(N:ℝ)^2)
    {k : ℕ} (hkpos : 1 ≤ k) (hk : k ≤ N) {t : ℝ} (ht : t ∈ Icc 0 T) :
    energy (law hN hb hbound hM hL₁ hL₂ hT (euclideanBrownianPathLaw d N T)
      (μ.map (configurationEuclidean d N)) (marginalProjection hk) (t := t))
      (source hN hb hbound hM hL₁ hL₂ hT (euclideanBrownianPathLaw d N T)
        (μ.map (configurationEuclidean d N)) (marginalProjection hk) ht u hu) ≤
      A*Real.exp (4*comparisonConstant d M L₁ L₂*t)*(k:ℝ)^2/(N:ℝ)^2 := by
  rw [← prefixEnergy_eq_projectedEnergy hN hb hbound hM hL₁ hL₂ hT
    (μ.map (configurationEuclidean d N)) hk u hu ht]
  exact prefixEnergy_quadratic_bound hN hb hbound hM hL₁ hL₂ hT μ hμ hu
    hex hue hA σ₀ hσ₀ hinit hkpos hk ht

end SharpWasserstein.BrownianEnergyPeriodization
