module

public import SharpWasserstein.Compat
public import SharpWasserstein.PeriodicMarginalCoefficientEvolutionConsistency
public import SharpWasserstein.FiniteCoefficientEnergyDerivative

@[expose] public section

/-! The finite regularized energy of the exact periodic marginal tangent.
The matrix and source coefficients are derived from the same actual Brownian
law and source; differentiability of the optimizer is a proved inverse-Gram
consequence, not an additional premise. -/
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

/-- The actual physical-period tangent of the true prefix source. -/
def periodicPrefixField (P : ℝ) (hm : m ≤ N) (ν : Measure (Point (N*d))) [IsFiniteMeasure ν]
    (σ : Test (N*d) →ₗ[ℝ] ℝ) : Lp (Point (m*d)) 2 (ν.map (marginalProjection hm)) :=
  (WeightedPeriodicTangentPhysical.representative P (ν.map (marginalProjection hm))
    (prefixSource hm ν (WeightedTangent.representative ν σ).val)).val.val

/-- The finite trial energy built from the actual next-particle source is
literally the same energy used in the marginal coefficient evolution. -/
theorem observed_trialEnergy_eq_prefix
    [MeasurableSpace (Point (m*d+d))] [BorelSpace (Point (m*d+d))]
    {ι : Type*} [Fintype ι] (P : ℝ) (hm : m ≤ N) (j : Fin N)
    (ν : Measure (Point (N*d))) [IsFiniteMeasure ν] (σ : Test (N*d) →ₗ[ℝ] ℝ)
    (a : ι → Point (m*d) → ℝ) (ha : ∀ i,ContDiff ℝ ∞ (a i))
    (hGa : ∀ i,∃ B : ℝ,∀ x,‖gradient (a i) x‖ ≤ B) (δ : ℝ) :
    RegularizedTrialEnergy.energy
      (gradientMap (WeightedMarginal.marginalLaw (ν.map (observation hm j))) a ha hGa) δ
      (WeightedPeriodicTangentPhysical.representative P
        (WeightedMarginal.marginalLaw (ν.map (observation hm j)))
        (WeightedMarginal.marginalDistribution (ν.map (observation hm j))
          (observedSource hm j ν (WeightedTangent.representative ν σ).val))).val.val =
    RegularizedTrialEnergy.energy (gradientMap (ν.map (marginalProjection hm)) a ha hGa) δ
      (periodicPrefixField P hm ν σ) := by
  simp only [marginalDistribution_observedSource,periodicPrefixField]
  have he (ρ τ : Measure (Point (m*d))) [IsFiniteMeasure ρ] [IsFiniteMeasure τ] (h : ρ=τ) :
      RegularizedTrialEnergy.energy (gradientMap ρ a ha hGa) δ
        (WeightedPeriodicTangentPhysical.representative P ρ
          (prefixSource hm ν (WeightedTangent.representative ν σ).val)).val.val =
      RegularizedTrialEnergy.energy (gradientMap τ a ha hGa) δ
        (WeightedPeriodicTangentPhysical.representative P τ
          (prefixSource hm ν (WeightedTangent.representative ν σ).val)).val.val := by
    subst τ
    rfl
  exact he _ _ (marginalLaw_observation hm j ν)

variable {b : Position d → Position d → Position d} {M K M' K' : ℝ≥0}
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

include hv hb hl hbs hμ ha hu in
/-- The literal optimized marginal Gram energy has a genuine time derivative
at every time of the finite horizon, including both endpoints. -/
theorem brownian_marginal_optimizedEnergy_hasDerivWithinAt (hm : m ≤ N)
    (hBa : ∀ i,AllDerivativesBounded (a i)) {δ : ℝ} (hδ : 0 < δ)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    let ν := fun r => Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) r
    let s := fun r => coefficientVector (fun i =>
      action hv' hb' hl' hT (euclideanBrownianPathLaw d N T) (μ.map (configurationEuclidean d N)) u
        (cylinder hm (a i)) r)
    let s' := coefficientVector (fun i =>
      action hv' hb' hl' hT (euclideanBrownianPathLaw d N T) (μ.map (configurationEuclidean d N)) u
        (splitGenerator hm b (a i)) t)
    let G' := matrixOperator (fun i j => ∫ x,splitGenerator hm b (gramTest (a i) (a j)) x ∂ν t)
    let c := Ring.inverse (gramMatrix ((ν t).map (marginalProjection hm)) a δ) (s t)
    HasDerivWithinAt (fun r => optimizedEnergy ((ν r).map (marginalProjection hm)) a δ (s r))
      (2*⟪s',c⟫_ℝ-⟪G' c,c⟫_ℝ) (Icc 0 T) t := by
  have hc := brownian_marginal_coefficients_hasDerivWithinAt hv hb hl hv' hb' hl' hT hbs μ hμ hm
    a ha hBa hu ht
  have hg (i : ι) : ∃ B : ℝ,∀ x,‖gradient (a i) x‖ ≤ B := by
    obtain ⟨B,_,h⟩ := (gradient_allDerivativesBounded (ha i) (hBa i)).bounded
    exact ⟨B,h⟩
  exact optimizedEnergy_hasDerivWithinAt _ a ha hg hδ hc.1 hc.2

include ha in
/-- Source entries of that exact matrix problem are the actual pairings with
the same periodic prefix tangent used by the next-particle energy identity. -/
theorem brownian_periodic_sourceVector_eq {P : ℝ} (hP : 0 < P) (hm : m ≤ N)
    (hp : ∀ i,PeriodicOf P (a i ∘ (PeriodicBochner.coordinateEquiv (m*d)).symm))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    let ν := Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) t
    let σ := Brownian.sourceAt hv' hb' hl' hT (particleDrift_smooth hbs)
      (particleDrift_allDerivativesBounded hbs) (μ.map (configurationEuclidean d N)) u hu t
    coefficientVector (fun i =>
      action hv' hb' hl' hT (euclideanBrownianPathLaw d N T) (μ.map (configurationEuclidean d N)) u
        (cylinder hm (a i)) t) =
      sourceVector (ν.map (marginalProjection hm)) a (periodicPrefixField P hm ν σ) := by
  ext i
  simp only [coefficientVector_apply,sourceVector]
  exact brownian_marginal_periodic_source_pairing hv' hb' hl' hT hbs μ hP hm hu (ha i) (hp i) ht

include hv hb hl hbs hμ ha hu in
/-- The derivative is for the genuine finite trial energy at the actual
periodic marginal representative U, not for an unrelated matrix solution.
The measure and representative may vary; no density or measurable U curve
is assumed. -/
theorem brownian_periodic_trialEnergy_hasDerivWithinAt {P : ℝ} (hP : 0 < P) (hm : m ≤ N)
    (hp : ∀ i,PeriodicOf P (a i ∘ (PeriodicBochner.coordinateEquiv (m*d)).symm))
    {δ : ℝ} (hδ : 0 < δ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    let ν := fun r => Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) r
    let σ := fun r => Brownian.sourceAt hv' hb' hl' hT (particleDrift_smooth hbs)
      (particleDrift_allDerivativesBounded hbs) (μ.map (configurationEuclidean d N)) u hu r
    let U := fun r => periodicPrefixField P hm (ν r) (σ r)
    let hg := fun i => (physical_test_bounds hP (a i) (ha i) (hp i)).2
    let A := fun r => gradientMap ((ν r).map (marginalProjection hm)) a ha hg
    let c := RegularizedTrialEnergy.solution (A t) δ (U t)
    let s' := coefficientVector (fun i =>
      action hv' hb' hl' hT (euclideanBrownianPathLaw d N T) (μ.map (configurationEuclidean d N)) u
        (splitGenerator hm b (a i)) t)
    let G' := matrixOperator (fun i j => ∫ x,splitGenerator hm b (gramTest (a i) (a j)) x ∂ν t)
    HasDerivWithinAt (fun r => RegularizedTrialEnergy.energy (A r) δ (U r))
      (2*⟪s',c⟫_ℝ-⟪G' c,c⟫_ℝ) (Icc 0 T) t := by
  let ν := fun r => Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) r
  let σ := fun r => Brownian.sourceAt hv' hb' hl' hT (particleDrift_smooth hbs)
    (particleDrift_allDerivativesBounded hbs) (μ.map (configurationEuclidean d N)) u hu r
  let U := fun r => periodicPrefixField P hm (ν r) (σ r)
  let hg := fun i => (physical_test_bounds hP (a i) (ha i) (hp i)).2
  let A := fun r => gradientMap ((ν r).map (marginalProjection hm)) a ha hg
  let s := fun r => coefficientVector (fun i =>
    action hv' hb' hl' hT (euclideanBrownianPathLaw d N T) (μ.map (configurationEuclidean d N)) u
      (cylinder hm (a i)) r)
  have hs (r : ℝ) (hr : r ∈ Icc 0 T) :
      s r = sourceVector ((ν r).map (marginalProjection hm)) a (U r) :=
    brownian_periodic_sourceVector_eq hv' hb' hl' hT hbs μ a ha hu hP hm hp hr
  have he (r : ℝ) (hr : r ∈ Icc 0 T) :
      RegularizedTrialEnergy.energy (A r) δ (U r) =
        optimizedEnergy ((ν r).map (marginalProjection hm)) a δ (s r) := by
    rw [hs r hr]
    exact (optimizedEnergy_eq _ a ha hg δ (U r)).symm
  have hd := brownian_marginal_optimizedEnergy_hasDerivWithinAt hv hb hl hv' hb' hl' hT hbs μ hμ
    a ha hu hm (fun i => physical_allDerivativesBounded hP (ha i) (hp i)) hδ ht
  have hc : Ring.inverse (gramMatrix ((ν t).map (marginalProjection hm)) a δ) (s t) =
      RegularizedTrialEnergy.solution (A t) δ (U t) := by
    rw [hs t ht,gramMatrix_eq _ a ha hg,sourceVector_eq _ a ha hg]
    rfl
  dsimp only at hd
  rw [hc] at hd
  exact hd.congr_of_mem he ht

end SharpWasserstein.PeriodicMarginalCoefficientEvolution
