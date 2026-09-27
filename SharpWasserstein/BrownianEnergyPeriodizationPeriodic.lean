import SharpWasserstein.BrownianEnergyPeriodizationLimit
import SharpWasserstein.BrownianEnergyPeriodizationExhaustion
import SharpWasserstein.BrownianPeriodicHierarchyInitial

/-! A fixed smooth periodic interaction kernel propagates the sharp profile
in the full Euclidean tangent space. The proved Brownian periodic hierarchy
is used at every positive integer multiple of the kernel period, then actual
compact tests are recovered. -/
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
/-- Genuine full Euclidean all-level propagation for a fixed periodic kernel.
The initial distribution is specified by its actual pairing with the same
initial L² field used in every Brownian source. -/
theorem periodic_prefixEnergy_quadratic_bound {P A : ℝ} (hP : 0 < P)
    (hex : Exchangeable μ)
    (hue : ∀ e : Equiv.Perm (Fin N),∀ᵐ x ∂μ.map (configurationEuclidean d N),
      u (euclideanPermutation e x)=euclideanPermutation e (u x))
    (hA : 0 ≤ A)
    (hx : ∀ i x y,b (x+Pi.single i P) y=b x y)
    (hy : ∀ i x y,b x (y+Pi.single i P)=b x y)
    (σ₀ : Test (N*d) →ₗ[ℝ] ℝ)
    (hσ₀ : ∀ φ : Test (N*d),σ₀ φ = ∫ x,⟪gradient φ.val x,u x⟫_ℝ ∂μ.map (configurationEuclidean d N))
    (hinit : ∀ k,1 ≤ k → k ≤ N →
      energy (levelLaw d N (μ.map (configurationEuclidean d N)) k)
        (levelSource d N (μ.map (configurationEuclidean d N)) σ₀ k) ≤ A*(k:ℝ)^2/(N:ℝ)^2)
    {k : ℕ} (hkpos : 1 ≤ k) (hk : k ≤ N) {t : ℝ} (ht : t ∈ Icc 0 T) :
    prefixEnergy hN hb hbound hM hL₁ hL₂ hT (μ.map (configurationEuclidean d N)) hk u hu t ≤
      A*Real.exp (4*comparisonConstant d M L₁ L₂*t)*(k:ℝ)^2/(N:ℝ)^2 := by
  let ν := carryingLaw hN hb hbound hM hL₁ hL₂ hT (μ.map (configurationEuclidean d N)) t
  let σ := propagatedSource hN hb hbound hM hL₁ hL₂ hT (μ.map (configurationEuclidean d N)) u hu t
  change energy (ν.map (marginalProjection hk)) (imageSource ν σ (marginalProjection hk)) ≤ _
  apply full_energy_le_of_kernel_periods hP hx hy (ν.map (marginalProjection hk))
    (imageSource ν σ (marginalProjection hk)) (imageSource_finite _ _ _)
  intro Q hQ hxQ hyQ
  have hh := brownian_periodic_quadratic_bound_initial_flux (M := ⟨M,hM⟩)
    ((particleDrift_lipschitz hN hb hbound hL₁ hL₂).continuous.comp continuous_snd)
    (fun _ => particleDrift_norm_bound hN hbound hM) (fun _ => particleDrift_lipschitz hN hb hbound hL₁ hL₂)
    ((drift_lipschitz hN hb hbound hL₁ hL₂).continuous.comp continuous_snd)
    (fun _ => drift_norm_le hN hbound hM) (fun _ => drift_lipschitz hN hb hbound hL₁ hL₂)
    hT hb μ hμ hu hQ hN hex hue hbound hM hL₁ hL₂ hA hxQ hyQ σ₀ hσ₀ hinit k hkpos hk t ht
  simpa only [brownianPeriodicEnergy,levelLaw,levelSource,levelProjection_eq hk,
    ν,σ,carryingLaw,propagatedSource] using hh

end SharpWasserstein.BrownianEnergyPeriodization
