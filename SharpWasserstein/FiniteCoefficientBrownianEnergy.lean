import SharpWasserstein.FiniteCoefficientEnergyDerivative
import SharpWasserstein.WeightedPeriodicCoefficientEvolutionBrownian

/-! The regularized Galerkin energy differentiates along the actual Brownian
carrying probability and the actual propagated Jacobian source. Both its
Gram and source derivatives are discharged by the genuine evolution laws. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff InnerProductSpace NNReal
namespace SharpWasserstein.FiniteCoefficientEnergy
open WeightedTangent NoiseAverage PropagatedSourceEquation PeriodicSourceConvolution
open WeightedPeriodicCoefficientEvolution FiniteCoefficientMatrix
variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  {b : Configuration d N → Configuration d N} {M K M' K' : ℝ≥0}
  (hv : Continuous (Function.uncurry (fun _ : ℝ => b)))
  (hb : ∀ _ : ℝ,∀ x,‖b x‖ ≤ M) (hl : ∀ _ : ℝ,LipschitzWith K b)
  (hv' : Continuous (Function.uncurry (fun _ : ℝ => equivDrift (configurationEuclidean d N) b)))
  (hb' : ∀ _ : ℝ,∀ y,‖equivDrift (configurationEuclidean d N) b y‖ ≤ M')
  (hl' : ∀ _ : ℝ,LipschitzWith K' (equivDrift (configurationEuclidean d N) b))
  {T : ℝ} (hT : 0 ≤ T) (hbs : ContDiff ℝ ∞ b) (hB : AllDerivativesBounded b)
  (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ] (hμ : HasSecondMoment μ)
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (a : ι → Point (N*d) → ℝ) (ha : ∀ i,ContDiff ℝ ∞ (a i))
  (hBa : ∀ i,AllDerivativesBounded (a i))
  {u : Point (N*d) → Point (N*d)} (hu : MemLp u 2 (μ.map (configurationEuclidean d N)))

include hv hb hl hbs hB hμ ha hBa hu in
/-- Every quantity in this energy derivative is evaluated on the same
constructed Brownian law. No density or differentiated Gram hypothesis is
added, and the formula includes both time endpoints. -/
theorem brownian_optimizedEnergy_hasDerivWithinAt {δ : ℝ} (hδ : 0 < δ)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    let ν := fun r => Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) r
    let s := fun r => coefficientVector (fun i =>
      action hv' hb' hl' hT (euclideanBrownianPathLaw d N T) (μ.map (configurationEuclidean d N)) u (a i) r)
    let s' := coefficientVector (fun i =>
      action hv' hb' hl' hT (euclideanBrownianPathLaw d N T) (μ.map (configurationEuclidean d N)) u
        (euclideanGenerator b (a i)) t)
    let G' := matrixOperator (fun i j => ∫ x,euclideanGenerator b (gramTest (a i) (a j)) x ∂ν t)
    let c := Ring.inverse (gramMatrix (ν t) a δ) (s t)
    HasDerivWithinAt (fun r => optimizedEnergy (ν r) a δ (s r))
      (2*⟪s',c⟫_ℝ-⟪G' c,c⟫_ℝ) (Icc 0 T) t := by
  have hc := brownian_coefficients_hasDerivWithinAt hv hb hl hv' hb' hl' hT hbs μ hμ hB a ha hBa hu ht
  have hg (i : ι) : ∃ B : ℝ,∀ x,‖gradient (a i) x‖ ≤ B := by
    obtain ⟨B,_,h⟩ := (gradient_allDerivativesBounded (ha i) (hBa i)).bounded
    exact ⟨B,h⟩
  letI : IsFiniteMeasure (Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) t) := by
    dsimp only [Brownian.lawAt]
    infer_instance
  exact optimizedEnergy_hasDerivWithinAt _ a ha hg hδ hc.1 hc.2

end SharpWasserstein.FiniteCoefficientEnergy
