module

public import SharpWasserstein.Compat
public import SharpWasserstein.SwitchSourceBrownianPairing
public import SharpWasserstein.SwitchSourceDerivativePrescribed
public import SharpWasserstein.PeriodicParticleTangentLimitFlow

@[expose] public section

/-! The prescribed switch curve's scalar derivative is its actual Euclidean
Brownian propagated reference-minus-particle current. All L² hypotheses for
the initial current are derived from the bounded interaction. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal ContDiff InnerProductSpace
namespace SharpWasserstein.SwitchSourceDerivative
open WeightedTangent PropagatedSourceEquation PeriodicParticleTangentLimit InitialSourcePermutation
variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
  (hN : 0 < N) (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
  (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
  {μ : ℝ → Measure (Position d)} (hμ : IsLimitEvolution b μ)
  {T : ℝ} (hT : 0 ≤ T) (P : Measure (Configuration d N)) [IsProbabilityMeasure P]

include hN in
theorem prescribedCurrent_memLp {s : ℝ} (hs : 0 ≤ s) :
    MemLp (euclideanFlux (initialCurrent b (μ s))) 2
      (euclideanLaw (PrescribedReference.law hb hbound hM hL₁ hμ N P s)) := by
  letI := hμ.1 s hs
  letI : IsProbabilityMeasure (PrescribedReference.law hb hbound hM hL₁ hμ N P s) := BrownianFlow.globalLaw_probability
    (DecoupledFlow.liftDrift_continuous N (PrescribedReference.singleDrift_continuous hb hbound hL₁ hμ))
    (DecoupledFlow.liftDrift_bound N (PrescribedReference.singleDrift_bound hbound hM hμ))
    (DecoupledFlow.liftDrift_lipschitz N (PrescribedReference.singleDrift_lipschitz hb hbound hL₁ hμ)) P hs
  exact InitialSourceMarginal.initialCurrent_memLp hN _ _ hb.smooth.continuous.measurable
    (fun x y a => by
      calc |b x y a| = ‖b x y a‖ := (Real.norm_eq_abs _).symm
           _ ≤ ‖b x y‖ := norm_le_pi_norm (b x y) a
           _ ≤ M := hbound.value x y)

/-- The source is a genuine linear distribution; switch-time dependence is
clamped only to extend it beyond the physical interval. -/
def prescribedBrownianSource (s : ℝ) : Test (N*d) →ₗ[ℝ] ℝ :=
  let r := projIcc 0 T hT s
  letI : IsProbabilityMeasure (PrescribedReference.law hb hbound hM hL₁ hμ N P r) := BrownianFlow.globalLaw_probability
    (DecoupledFlow.liftDrift_continuous N (PrescribedReference.singleDrift_continuous hb hbound hL₁ hμ))
    (DecoupledFlow.liftDrift_bound N (PrescribedReference.singleDrift_bound hbound hM hμ))
    (DecoupledFlow.liftDrift_lipschitz N (PrescribedReference.singleDrift_lipschitz hb hbound hL₁ hμ)) P r.property.1
  Brownian.sourceAt ((drift_lipschitz hN hb hbound hL₁ hL₂).continuous.comp continuous_snd)
    (fun _ => drift_norm_le hN hbound hM) (fun _ => drift_lipschitz hN hb hbound hL₁ hL₂)
    hT (particleDrift_smooth hb) (particleDrift_allDerivativesBounded hb)
    (euclideanLaw (PrescribedReference.law hb hbound hM hL₁ hμ N P r))
    (euclideanFlux (initialCurrent b (μ r))) (prescribedCurrent_memLp hN hb hbound hM hL₁ hμ P r.property.1) (T-r)

/-- Exact identification with the already proved prescribed switch derivative. -/
theorem prescribedBrownianSource_pairing {s : ℝ} (hs : s ∈ Icc 0 T) (φ : Test (N*d)) :
    prescribedBrownianSource hN hb hbound hM hL₁ hL₂ hμ hT P s φ =
      prescribedSourcePairing hN hb hbound hM hL₁ hL₂ hμ hT P
        ((φ : Point (N*d) → ℝ) ∘ configurationEuclidean d N) s := by
  letI : IsProbabilityMeasure (PrescribedReference.law hb hbound hM hL₁ hμ N P s) := BrownianFlow.globalLaw_probability
    (DecoupledFlow.liftDrift_continuous N (PrescribedReference.singleDrift_continuous hb hbound hL₁ hμ))
    (DecoupledFlow.liftDrift_bound N (PrescribedReference.singleDrift_bound hbound hM hμ))
    (DecoupledFlow.liftDrift_lipschitz N (PrescribedReference.singleDrift_lipschitz hb hbound hL₁ hμ)) P hs.1
  unfold prescribedBrownianSource
  simp only [projIcc_of_mem _ hs]
  rw [Brownian.sourceAt_configuration_pairing (M := NNReal.mk M hM)
    ((particleDrift_lipschitz hN hb hbound hL₁ hL₂).continuous.comp continuous_snd)
    (fun _ => particleDrift_norm_bound hN hbound hM) (fun _ => particleDrift_lipschitz hN hb hbound hL₁ hL₂)
    ((drift_lipschitz hN hb hbound hL₁ hL₂).continuous.comp continuous_snd)
    (fun _ => drift_norm_le hN hbound hM) (fun _ => drift_lipschitz hN hb hbound hL₁ hL₂)
    hT (particleDrift_smooth hb) (particleDrift_allDerivativesBounded hb) _ _
    (show T-s ∈ Icc 0 T from ⟨sub_nonneg.mpr hs.2,sub_le_self _ hs.1⟩)]
  rw [prescribedSourcePairing_eq_current hN hb hbound hM hL₁ hL₂ hμ hT P _ hs.1]
  have he := clampedExpectation_of_mem (M := NNReal.mk M hM)
    ((particleDrift_lipschitz hN hb hbound hL₁ hL₂).continuous.comp continuous_snd)
    (fun _ => particleDrift_norm_bound hN hbound hM) (fun _ => particleDrift_lipschitz hN hb hbound hL₁ hL₂)
    hT (BrownianNoise.configurationLaw d N T)
    ((φ : Point (N*d) → ℝ) ∘ configurationEuclidean d N)
    (show T-s ∈ Icc 0 T from ⟨sub_nonneg.mpr hs.2,sub_le_self _ hs.1⟩)
  change particleRemainingTest hN hb hbound hM hL₁ hL₂ hT
    ((φ : Point (N*d) → ℝ) ∘ configurationEuclidean d N) s = _ at he
  rw [he]

end SharpWasserstein.SwitchSourceDerivative
