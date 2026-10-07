module

public import SharpWasserstein.Compat
public import SharpWasserstein.PeriodicMarginalCoefficientEvolutionGenerator

@[expose] public section

/-! The exact time derivative of the actual finite periodic marginal energy
as a literal full-law generator/source pairing. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace NNReal BigOperators
namespace SharpWasserstein.PeriodicMarginalCoefficientEvolution
open WeightedTangent NoiseAverage PropagatedSourceEquation PeriodicSourceConvolution
open PeriodicParticleTangentLimit WeightedPeriodicCoefficientEvolution
open ExternalInteractionPeriodic ExternalInteractionSymmetry
open FiniteCoefficientMatrix FiniteCoefficientEnergy FiniteGradientTrial
open WeightedPeriodicFourierScale (PeriodicOf)
variable {d m N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  [MeasurableSpace (Point (m*d))] [BorelSpace (Point (m*d))]
  {b : Position d → Position d → Position d} {M K M' K' : ℝ≥0}
  (hv : Continuous (Function.uncurry (fun _ : ℝ => (particleDrift b : Configuration d N → _))))
  (hb : ∀ _ : ℝ,∀ x : Configuration d N,‖particleDrift b x‖ ≤ M)
  (hl : ∀ _ : ℝ,LipschitzWith K (particleDrift b : Configuration d N → _))
  (hv' : Continuous (Function.uncurry (fun _ : ℝ => equivDrift (configurationEuclidean d N) (particleDrift b))))
  (hb' : ∀ _ : ℝ,∀ y,‖equivDrift (configurationEuclidean d N) (particleDrift b) y‖ ≤ M')
  (hl' : ∀ _ : ℝ,LipschitzWith K' (equivDrift (configurationEuclidean d N) (particleDrift b)))
  {T : ℝ} (hT : 0 ≤ T) (hbs : BoundedSmoothKernel b)
  (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ] (hμ : HasSecondMoment μ)
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (a : ι → Point (m*d) → ℝ) (ha : ∀ i,ContDiff ℝ ∞ (a i))
  {u : Point (N*d) → Point (N*d)} (hu : MemLp u 2 (μ.map (configurationEuclidean d N)))
include hv hb hl hbs hμ ha hu

theorem brownian_periodic_trialEnergy_splitGenerator {P : ℝ} (hP : 0 < P) (hm : m ≤ N)
    (hp : ∀ i,PeriodicOf P (a i ∘ (PeriodicBochner.coordinateEquiv (m*d)).symm))
    {δ : ℝ} (hδ : 0 < δ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    let ν := fun r => Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) r
    let σ := fun r => Brownian.sourceAt hv' hb' hl' hT (particleDrift_smooth hbs)
      (particleDrift_allDerivativesBounded hbs) (μ.map (configurationEuclidean d N)) u hu r
    let U := fun r => periodicPrefixField P hm (ν r) (σ r)
    let hg := fun i => (physical_test_bounds hP (a i) (ha i) (hp i)).2
    let A := fun r => gradientMap ((ν r).map (marginalProjection hm)) a ha hg
    let c := RegularizedTrialEnergy.solution (A t) δ (U t)
    let f := potential a c
    HasDerivWithinAt (fun r => RegularizedTrialEnergy.energy (A r) δ (U r))
      (2*pairing (ν t) (WeightedTangent.representative (ν t) (σ t)).val (splitGenerator hm b f)-
        (∫ x,splitGenerator hm b (fun y => ‖gradient f y‖^2) x ∂ν t)) (Icc 0 T) t := by
  let ν := Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) t
  let σ := Brownian.sourceAt hv' hb' hl' hT (particleDrift_smooth hbs)
    (particleDrift_allDerivativesBounded hbs) (μ.map (configurationEuclidean d N)) u hu t
  let U := periodicPrefixField P hm ν σ
  let hg := fun i => (physical_test_bounds hP (a i) (ha i) (hp i)).2
  let A := gradientMap (ν.map (marginalProjection hm)) a ha hg
  let c := RegularizedTrialEnergy.solution A δ U
  have hBa i := physical_allDerivativesBounded hP (ha i) (hp i)
  have hd := brownian_periodic_trialEnergy_hasDerivWithinAt hv hb hl hv' hb' hl' hT hbs μ hμ
    a ha hu hP hm hp hδ ht
  have hs (i : ι) : action hv' hb' hl' hT (euclideanBrownianPathLaw d N T)
      (μ.map (configurationEuclidean d N)) u (splitGenerator hm b (a i)) t =
      pairing ν (WeightedTangent.representative ν σ).val (splitGenerator hm b (a i)) := by
    obtain ⟨hs,hB⟩ := splitGenerator_smooth_bounded hm hbs (ha i) (hBa i)
    simpa only [pairing,inner_gradient_left] using Brownian.action_eq_representative_pairing
      hv' hb' hl' hT (particleDrift_smooth hbs) (particleDrift_allDerivativesBounded hbs)
      (μ.map (configurationEuclidean d N)) hu hs hB ht
  dsimp only at hd ⊢
  simp only [hs] at hd
  have hS := source_splitGenerator_pairing hm ν hbs a ha hBa
    (WeightedTangent.representative ν σ).val c
  have hG := matrix_splitGenerator_quadratic hm ν hbs a ha hBa c
  convert hd using 1
  rw [hS,hG]

end SharpWasserstein.PeriodicMarginalCoefficientEvolution
