module

public import SharpWasserstein.Compat
public import SharpWasserstein.PrescribedSwitchBrownianSource
public import SharpWasserstein.PropagatedSourceEquationLaw

@[expose] public section

/-! Exact identification of the measure carrying the switch source. The source
energy is evaluated at the actual interpolation law, in unnormalized Euclidean
coordinates. -/
noncomputable section
open Set MeasureTheory
open scoped NNReal ContDiff
namespace SharpWasserstein.SwitchSourceDerivative
open WeightedTangent PropagatedSourceEquation PeriodicParticleTangentLimit InitialSourcePermutation
variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
  (hN : 0 < N) (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
  (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
  {μ : ℝ → Measure (Position d)} (hμ : IsLimitEvolution b μ)
  {T : ℝ} (hT : 0 ≤ T) (P : Measure (Configuration d N)) [IsProbabilityMeasure P]

theorem prescribedBrownianSource_lawAt {s : ℝ} (hs : s ∈ Icc 0 T) :
    Brownian.lawAt ((drift_lipschitz hN hb hbound hL₁ hL₂).continuous.comp continuous_snd)
      (fun _ => drift_norm_le hN hbound hM) (fun _ => drift_lipschitz hN hb hbound hL₁ hL₂)
      hT (euclideanLaw (PrescribedReference.law hb hbound hM hL₁ hμ N P s)) (T-s) =
    euclideanLaw (PrescribedSwitchCurve.law hN hb hbound hM hL₁ hL₂ hμ hT P s) := by
  letI : IsProbabilityMeasure (PrescribedReference.law hb hbound hM hL₁ hμ N P s) :=
    BrownianFlow.globalLaw_probability _ _ _ P hs.1
  rw [PrescribedSwitchCurve.law_eq_composition hN hb hbound hM hL₁ hL₂ hμ hT P hs]
  exact Brownian.lawAt_eq_map_globalLaw (M := NNReal.mk M hM)
    ((particleDrift_lipschitz hN hb hbound hL₁ hL₂).continuous.comp continuous_snd)
    (fun _ => particleDrift_norm_bound hN hbound hM) (fun _ => particleDrift_lipschitz hN hb hbound hL₁ hL₂)
    _ _ _ hT _ ⟨sub_nonneg.mpr hs.2,sub_le_self _ hs.1⟩

theorem prescribedBrownianSource_finite {s : ℝ} (hs : s ∈ Icc 0 T) :
    letI : IsProbabilityMeasure (PrescribedSwitchCurve.law hN hb hbound hM hL₁ hL₂ hμ hT P s) :=
      SwitchCurve.law_probability hN hb hbound hM hL₁ hL₂ _ _ _ hT P hs
    FiniteEnergy (euclideanLaw (PrescribedSwitchCurve.law hN hb hbound hM hL₁ hL₂ hμ hT P s))
      (prescribedBrownianSource hN hb hbound hM hL₁ hL₂ hμ hT P s) := by
  letI : IsProbabilityMeasure (PrescribedSwitchCurve.law hN hb hbound hM hL₁ hL₂ hμ hT P s) :=
    SwitchCurve.law_probability hN hb hbound hM hL₁ hL₂ _ _ _ hT P hs
  letI : IsProbabilityMeasure (PrescribedReference.law hb hbound hM hL₁ hμ N P s) :=
    BrownianFlow.globalLaw_probability _ _ _ P hs.1
  unfold prescribedBrownianSource
  simp only [projIcc_of_mem _ hs]
  have he := prescribedBrownianSource_lawAt hN hb hbound hM hL₁ hL₂ hμ hT P hs
  rw [← he]
  exact (Brownian.sourceAt_finiteEnergy_and_energy_le _ _ _ hT (particleDrift_smooth hb)
    (particleDrift_allDerivativesBounded hb) _ _ _
      ⟨sub_nonneg.mpr hs.2,sub_le_self _ hs.1⟩).1

end SharpWasserstein.SwitchSourceDerivative
