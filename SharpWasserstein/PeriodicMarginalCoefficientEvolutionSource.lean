module

public import SharpWasserstein.Compat
public import SharpWasserstein.PeriodicMarginalCoefficientEvolutionBrownian
public import SharpWasserstein.WeightedPeriodicCoefficientEvolutionFourier
public import SharpWasserstein.FiniteTrialEnergyIdentity

@[expose] public section

/-! Genuine source marginalization and finite-N source-generator splitting.
Every noncompact periodic test is represented through the actual weighted
gradient closure, and the external sum is averaged by actual covariance. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace BigOperators
namespace SharpWasserstein.PeriodicMarginalCoefficientEvolution
open WeightedTangent NoiseAverage PropagatedSourceEquation PeriodicSourceConvolution
open PeriodicParticleTangentLimit WeightedPeriodicCoefficientEvolution
open ExternalInteractionPeriodic ExternalInteractionSymmetry PDEPairings
open WeightedPeriodicFourierScale (PeriodicOf)
variable {n d m N : ℕ}

/-- Smooth physical-period tests have actual bounds on every derivative. -/
theorem physical_allDerivativesBounded {P : ℝ} (hP : 0 < P)
    {f : Point n → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : PeriodicOf P (f ∘ (PeriodicBochner.coordinateEquiv n).symm)) :
    AllDerivativesBounded f := by
  obtain ⟨g,rfl⟩ := exists_physical_test hP f hf hp
  exact ((periodic_allDerivativesBounded g.property.1 g.property.2).comp_linear
    g.property.1 (WeightedPeriodicFourierScale.dilation P⁻¹)).comp_linear
    (WeightedPeriodicFourierScale.rescale_smooth P⁻¹ g.property.1)
    (PeriodicBochner.coordinateEquiv n).toContinuousLinearMap

theorem directionDeriv_periodic {P : ℝ} {f : Point n → ℝ}
    (hp : PeriodicOf P (f ∘ (PeriodicBochner.coordinateEquiv n).symm)) (v : Point n) :
    PeriodicOf P (directionDeriv v f ∘ (PeriodicBochner.coordinateEquiv n).symm) := by
  apply of_euclidean_lattice_periodic
  intro k x
  have he : (fun y => f (y+euclideanLattice P k)) = f := funext (euclidean_lattice_periodic hp k)
  have hd := fderiv_comp_add_right (𝕜 := ℝ) (f := f) (x := x) (euclideanLattice P k)
  rw [he] at hd
  exact congrArg (fun L : Point n →L[ℝ] ℝ => L v) hd.symm

/-- The true Euclidean Laplacian retains the physical period. -/
theorem euclidean_laplacian_periodic {P : ℝ} {f : Point n → ℝ}
    (hp : PeriodicOf P (f ∘ (PeriodicBochner.coordinateEquiv n).symm)) :
    PeriodicOf P (PDEPairings.laplacian f ∘ (PeriodicBochner.coordinateEquiv n).symm) := by
  intro k x
  simp only [Function.comp_apply,PDEPairings.laplacian]
  apply Finset.sum_congr rfl
  intro i hi
  exact directionDeriv_periodic (directionDeriv_periodic hp _) _ k x

/-- The diffusion plus the actual internal drift, retaining the full-N
normalization even though the test has only m particle arguments. -/
def internalGenerator (N : ℕ) (b : Position d → Position d → Position d)
    (f : Point (m*d) → ℝ) (x : Point (m*d)) : ℝ :=
  PDEPairings.laplacian f x+⟪internalDrift N b x,gradient f x⟫_ℝ

theorem internalGenerator_smooth {b : Position d → Position d → Position d}
    (hb : BoundedSmoothKernel b) (N : ℕ) {f : Point (m*d) → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (internalGenerator N b f) :=
  (BochnerIdentity.smooth_laplacian hf).add (internalDrift_pairing_smooth hb N hf)

theorem internalGenerator_periodic {P : ℝ} {b : Position d → Position d → Position d}
    (hx : ∀ a x y,b (x+Pi.single a P) y=b x y)
    (hy : ∀ a x y,b x (y+Pi.single a P)=b x y)
    (N : ℕ) {f : Point (m*d) → ℝ}
    (hp : PeriodicOf P (f ∘ (PeriodicBochner.coordinateEquiv (m*d)).symm)) :
    PeriodicOf P (internalGenerator N b f ∘ (PeriodicBochner.coordinateEquiv (m*d)).symm) :=
  fun i => (euclidean_laplacian_periodic hp i).add (internalDrift_pairing_periodic hx hy N hp i)

section Pairings
variable [MeasurableSpace (Point n)] [BorelSpace (Point n)]
  (μ : Measure (Point n)) [IsFiniteMeasure μ] (U : Lp (Point n) 2 μ)

theorem pairing_integrable {f : Point n → ℝ} (hf : ContDiff ℝ ∞ f)
    (hB : AllDerivativesBounded f) : Integrable (fun x => fderiv ℝ f x (U x)) μ := by
  simpa only [inner_gradient_left] using
    FiniteGradientTrial.integrable_smooth_gradient_pairing μ hf hB U

/-- Genuine linearity of the differential source pairing, with all integrals
justified from bounded smooth tests and the actual L² field. -/
theorem pairing_add_sum {ι : Type*} (s : Finset ι)
    {f : Point n → ℝ} (hf : ContDiff ℝ ∞ f) (hBf : AllDerivativesBounded f)
    (g : ι → Point n → ℝ) (hg : ∀ i,ContDiff ℝ ∞ (g i))
    (hBg : ∀ i,AllDerivativesBounded (g i)) (c : ℝ) :
    pairing μ U (fun x => f x+c*∑ i ∈ s,g i x) =
      pairing μ U f+c*∑ i ∈ s,pairing μ U (g i) := by
  have hd (x : Point n) :
      fderiv ℝ (fun y => f y+c*∑ i ∈ s,g i y) x (U x) =
        fderiv ℝ f x (U x)+c*∑ i ∈ s,fderiv ℝ (g i) x (U x) := by
    rw [fderiv_fun_add (hf.differentiable (by simp) x)
      ((contDiff_const.mul (ContDiff.sum fun i _ => hg i)).differentiable (by simp) x),
      fderiv_const_mul ((ContDiff.sum fun i _ => hg i).differentiable (by simp) x) c,
      fderiv_fun_sum (fun i _ => (hg i).differentiable (by simp) x)]
    simp only [add_apply,smul_apply,
      sum_apply,smul_eq_mul]
  simp only [pairing,hd]
  rw [integral_add (pairing_integrable μ U hf hBf)
    ((integrable_finsetSum _ fun i _ => pairing_integrable μ U (hg i) (hBg i)).const_mul c),
    integral_const_mul,integral_finsetSum _ (fun i _ => pairing_integrable μ U (hg i) (hBg i))]

end Pairings

section Marginal
variable [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  [MeasurableSpace (Point (m*d))] [BorelSpace (Point (m*d))]
  (hm : m ≤ N) (μ : Measure (Point (N*d))) [IsFiniteMeasure μ]
  (U : Lp (Point (N*d)) 2 μ)

/-- The actual marginal source is the distribution of the projected flux
under the actual coordinate observation. -/
def prefixSource : Test (m*d) →ₗ[ℝ] ℝ :=
  PropagatedFlux.source μ (marginalProjection hm) (marginalProjection hm).continuous.measurable
    ((marginalProjection hm).compLpₗ 2 μ U)

theorem prefixSource_finiteEnergy :
    FiniteEnergy (μ.map (marginalProjection hm)) (prefixSource hm μ U) :=
  PropagatedFlux.source_finiteEnergy _ _ _ _

/-- Actual bounded periodic cylinders pair exactly with the constructed
periodic representative of the genuine source marginal. -/
theorem prefixSource_periodic_pairing {P : ℝ} (hP : 0 < P)
    {f : Point (m*d) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : PeriodicOf P (f ∘ (PeriodicBochner.coordinateEquiv (m*d)).symm)) :
    pairing μ U (cylinder hm f) =
      ∫ y,⟪gradient f y,
        ((WeightedPeriodicTangentPhysical.representative P (μ.map (marginalProjection hm))
          (prefixSource hm μ U) : gradientClosure (μ.map (marginalProjection hm))) :
          Lp (Point (m*d)) 2 (μ.map (marginalProjection hm))) y⟫_ℝ ∂μ.map (marginalProjection hm) := by
  obtain ⟨hA,hB⟩ := physical_test_bounds hP f hf hp
  have hpref := randomSource_bounded_pairing μ (marginalProjection hm)
    (marginalProjection hm).continuous.measurable ((marginalProjection hm).compLpₗ 2 μ U) f hf hA hB
  rw [periodic_representative_pairing hP _ _ f hf hp] at hpref
  refine Eq.trans ?_ hpref
  apply integral_congr_ae
  filter_upwards [(marginalProjection hm).coeFn_compLp U] with x hx
  rw [ContinuousLinearMap.compLpₗ_apply,hx,inner_gradient_left]
  unfold cylinder
  rw [fderiv_comp x (hf.differentiable (by simp) _) (marginalProjection hm).differentiableAt,
    ContinuousLinearMap.fderiv]
  rfl

end Marginal
end SharpWasserstein.PeriodicMarginalCoefficientEvolution
