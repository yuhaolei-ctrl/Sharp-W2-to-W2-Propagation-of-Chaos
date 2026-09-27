import SharpWasserstein.FiniteCoefficientBrownianEnergy
import SharpWasserstein.BrownianSourceSmoothPairing
import SharpWasserstein.FiniteGeneratorPairing
import SharpWasserstein.FiniteGeneratorBounds

/-! The actual Brownian coefficient-energy derivative is the literal
Euclidean generator integral, paired with the canonical source tangent of
the very same carrying law. This discharges both coefficient identifications. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff InnerProductSpace NNReal
namespace SharpWasserstein.FiniteCoefficientEnergy
open WeightedTangent NoiseAverage PropagatedSourceEquation PeriodicSourceConvolution
open WeightedPeriodicCoefficientEvolution FiniteCoefficientMatrix FiniteGradientTrial
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
theorem brownian_optimizedEnergy_generator {δ : ℝ} (hδ : 0 < δ)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    let ν := fun r => Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) r
    let σ := fun r => Brownian.sourceAt hv' hb' hl' hT hbs hB
      (μ.map (configurationEuclidean d N)) u hu r
    let U := (WeightedTangent.representative (ν t) (σ t)).val
    let s := fun r => coefficientVector (fun i =>
      action hv' hb' hl' hT (euclideanBrownianPathLaw d N T) (μ.map (configurationEuclidean d N)) u (a i) r)
    let c := Ring.inverse (gramMatrix (ν t) a δ) (s t)
    let f := potential a c
    HasDerivWithinAt (fun r => optimizedEnergy (ν r) a δ (s r))
      (2*(∫ x,⟪gradient (euclideanGenerator b f) x,U x⟫_ℝ ∂ν t)-
        (∫ x,euclideanGenerator b (fun y => ‖gradient f y‖^2) x ∂ν t)) (Icc 0 T) t := by
  dsimp only
  let ν := Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) t
  let σ := Brownian.sourceAt hv' hb' hl' hT hbs hB (μ.map (configurationEuclidean d N)) u hu t
  let U := (WeightedTangent.representative ν σ).val
  let s := coefficientVector (fun i => action hv' hb' hl' hT
    (euclideanBrownianPathLaw d N T) (μ.map (configurationEuclidean d N)) u (a i) t)
  let c := Ring.inverse (gramMatrix ν a δ) s
  let B := equivDrift (configurationEuclidean d N) b
  have hBs : ContDiff ℝ ∞ B := equivDrift_smooth _ hbs
  have hBB : AllDerivativesBounded B := equivDrift_allDerivativesBounded _ hbs hB
  have hd := brownian_optimizedEnergy_hasDerivWithinAt hv hb hl hv' hb' hl' hT hbs hB μ hμ a ha hBa hu hδ ht
  have hs (i : ι) : action hv' hb' hl' hT (euclideanBrownianPathLaw d N T)
      (μ.map (configurationEuclidean d N)) u (euclideanGenerator b (a i)) t =
      ∫ x,⟪gradient (euclideanGenerator b (a i)) x,U x⟫_ℝ ∂ν :=
    Brownian.action_eq_representative_pairing hv' hb' hl' hT hbs hB
      (μ.map (configurationEuclidean d N)) hu (euclideanGenerator_smooth hbs (ha i))
      (euclideanGenerator_bounded hbs hB (ha i) (hBa i)) ht
  have hG (i : ι) : ∃ C : ℝ,∀ x,‖gradient (FiniteGeneratorCalculus.generator B (a i)) x‖ ≤ C := by
    obtain ⟨C,_,hC⟩ := (gradient_allDerivativesBounded
      (FiniteGeneratorCalculus.generator_smooth hBs (ha i))
      (FiniteGeneratorCalculus.generator_allDerivativesBounded hBs hBB (ha i) (hBa i))).bounded
    exact ⟨C,hC⟩
  have hsource := FiniteGeneratorCalculus.sourceGenerator_pairing ν B a ha U
    (fun i => FiniteGeneratorCalculus.generator_smooth hBs (ha i)) hG c
  have hmatrix := FiniteGeneratorCalculus.matrixGenerator_quadratic ν B a ha
    (fun i j => FiniteGeneratorCalculus.generator_integrable ν hBs hBB
      (gramTest_smooth (ha i) (ha j)) (gramTest_allDerivativesBounded (ha i) (ha j) (hBa i) (hBa j))) c
  simp only [FiniteGeneratorCalculus.euclideanGenerator_eq] at hs ⊢
  simp only [FiniteGeneratorCalculus.euclideanGenerator_eq,hs] at hd
  convert hd using 1
  rw [hsource]
  congr 1
  exact hmatrix.symm

end SharpWasserstein.FiniteCoefficientEnergy
