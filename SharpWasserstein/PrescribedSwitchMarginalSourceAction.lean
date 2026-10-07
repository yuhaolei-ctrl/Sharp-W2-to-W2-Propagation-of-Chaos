module

public import SharpWasserstein.Compat
public import SharpWasserstein.PrescribedSwitchBrownianLaw
public import SharpWasserstein.BrownianSourceSmoothPairing

@[expose] public section

/-! The actual Brownian source action on bounded, noncompact observables
has the same coordinate-conjugacy formula as compact tests. This supplies
the missing cylinder bridge for genuine marginal switch derivatives. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal ContDiff InnerProductSpace
namespace SharpWasserstein.PropagatedSourceEquation.Brownian
open WeightedTangent NoiseAverage FlowSemigroupDerivative PeriodicSourceConvolution
variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  {b : Configuration d N → Configuration d N} {M K M' K' : ℝ≥0}
  (hv : Continuous (Function.uncurry (fun _ : ℝ => b)))
  (hb : ∀ _ : ℝ,∀ x,‖b x‖ ≤ M) (hl : ∀ _ : ℝ,LipschitzWith K b)
  (hv' : Continuous (Function.uncurry (fun _ : ℝ => equivDrift (configurationEuclidean d N) b)))
  (hb' : ∀ _ : ℝ,∀ y,‖equivDrift (configurationEuclidean d N) b y‖ ≤ M')
  (hl' : ∀ _ : ℝ,LipschitzWith K' (equivDrift (configurationEuclidean d N) b))
  {T : ℝ} (hT : 0 ≤ T) (μ : Measure (Configuration d N)) [IsFiniteMeasure μ]

/-- Literal coordinate conjugacy of the differentiated expectation, including
noncompact bounded cylinder observables. -/
theorem action_configuration_pairing (v : Configuration d N → Configuration d N)
    {F : Point (N*d) → ℝ} (hF : Continuous F) {t : ℝ} (ht : t ∈ Icc 0 T) :
    action hv' hb' hl' hT (euclideanBrownianPathLaw d N T) (euclideanLaw μ) (euclideanFlux v) F t =
      ∫ x,fderiv ℝ (expectation hv hb hl hT (BrownianNoise.configurationLaw d N T)
        (t := t) (F ∘ configurationEuclidean d N)) x (v x) ∂μ := by
  rw [action_of_mem hv' hb' hl' hT _ _ _ _ ht,integral_euclideanLaw]
  have he : (expectation hv' hb' hl' hT (euclideanBrownianPathLaw d N T) (t := t) F) ∘
      configurationEuclidean d N =
      expectation hv hb hl hT (BrownianNoise.configurationLaw d N T) (t := t)
        (F ∘ configurationEuclidean d N) := by
    funext x
    exact expectation_equiv (configurationEuclidean d N) hv hb hl hv' hb' hl' hT
      (BrownianNoise.configurationLaw d N T) x ht hF
  rw [← he]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [(configurationEuclidean d N).comp_right_fderiv]
  simp only [euclideanFlux,ContinuousLinearEquiv.symm_apply_apply,ContinuousLinearMap.comp_apply]
  rfl

end SharpWasserstein.PropagatedSourceEquation.Brownian

namespace SharpWasserstein.SwitchSourceDerivative
open WeightedTangent PropagatedSourceEquation PeriodicParticleTangentLimit InitialSourcePermutation
open PeriodicSourceConvolution
variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
  (hN : 0 < N) (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
  (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
  {μ : ℝ → Measure (Position d)} (hμ : IsLimitEvolution b μ)
  {T : ℝ} (hT : 0 ≤ T) (P : Measure (Configuration d N)) [IsProbabilityMeasure P]

/-- The prescribed scalar switch source is the actual Brownian differentiated
expectation for every continuous Euclidean observable, including cylinders. -/
theorem prescribedSourcePairing_eq_action {F : Point (N*d) → ℝ} (hF : Continuous F)
    {s : ℝ} (hs : s ∈ Icc 0 T) :
    letI : IsProbabilityMeasure (PrescribedReference.law hb hbound hM hL₁ hμ N P s) :=
      BrownianFlow.globalLaw_probability _ _ _ P hs.1
    prescribedSourcePairing hN hb hbound hM hL₁ hL₂ hμ hT P (F ∘ configurationEuclidean d N) s =
      action ((drift_lipschitz hN hb hbound hL₁ hL₂).continuous.comp continuous_snd)
        (fun _ => drift_norm_le hN hbound hM) (fun _ => drift_lipschitz hN hb hbound hL₁ hL₂)
        hT (euclideanBrownianPathLaw d N T)
        (euclideanLaw (PrescribedReference.law hb hbound hM hL₁ hμ N P s))
        (euclideanFlux (initialCurrent b (μ s))) F (T-s) := by
  letI : IsProbabilityMeasure (PrescribedReference.law hb hbound hM hL₁ hμ N P s) :=
    BrownianFlow.globalLaw_probability _ _ _ P hs.1
  have ht : T-s ∈ Icc 0 T := ⟨sub_nonneg.mpr hs.2,sub_le_self _ hs.1⟩
  have hh := Brownian.action_configuration_pairing (M := NNReal.mk M hM)
    ((particleDrift_lipschitz hN hb hbound hL₁ hL₂).continuous.comp continuous_snd)
    (fun _ => particleDrift_norm_bound hN hbound hM) (fun _ => particleDrift_lipschitz hN hb hbound hL₁ hL₂)
    ((drift_lipschitz hN hb hbound hL₁ hL₂).continuous.comp continuous_snd)
    (fun _ => drift_norm_le hN hbound hM) (fun _ => drift_lipschitz hN hb hbound hL₁ hL₂)
    hT (PrescribedReference.law hb hbound hM hL₁ hμ N P s) (initialCurrent b (μ s)) hF ht
  refine Eq.trans ?_ hh.symm
  rw [prescribedSourcePairing_eq_current hN hb hbound hM hL₁ hL₂ hμ hT P _ hs.1]
  have he := clampedExpectation_of_mem (M := NNReal.mk M hM)
    ((particleDrift_lipschitz hN hb hbound hL₁ hL₂).continuous.comp continuous_snd)
    (fun _ => particleDrift_norm_bound hN hbound hM) (fun _ => particleDrift_lipschitz hN hb hbound hL₁ hL₂)
    hT (BrownianNoise.configurationLaw d N T) (F ∘ configurationEuclidean d N) ht
  change particleRemainingTest hN hb hbound hM hL₁ hL₂ hT (F ∘ configurationEuclidean d N) s = _ at he
  rw [he]

end SharpWasserstein.SwitchSourceDerivative
