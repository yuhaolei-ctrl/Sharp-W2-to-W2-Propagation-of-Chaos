import SharpWasserstein.PrescribedSwitchMarginalSourceAction
import SharpWasserstein.InitialSourceMarginalPairing
import SharpWasserstein.PeriodicParticleTangentLimitMarginal
import SharpWasserstein.RoughEulerianSmoothingFloor

/-! The true marginal switch source is the canonical linear image of the
actual Brownian propagated current. Compact marginal tests are admitted via
bounded smooth cylinders, not by claiming their full-space lifts are compact. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal ContDiff InnerProductSpace
namespace SharpWasserstein.SwitchSourceDerivative
open WeightedTangent PropagatedSourceEquation PeriodicParticleTangentLimit InitialSourcePermutation
open NoiseAverage InitialSourceMarginal
/-- Exact transport of the canonical source pairing under equality of carrying measures. -/
theorem canonical_pairing_measure_congr {n : ℕ}
    [MeasurableSpace (Point n)] [BorelSpace (Point n)]
    (ν τ : Measure (Point n)) [IsFiniteMeasure ν] [IsFiniteMeasure τ] (h : ν=τ)
    (σ : Test n →ₗ[ℝ] ℝ) (F : Point n → ℝ) :
    (∫ x,⟪gradient F x,(WeightedTangent.representative ν σ).val x⟫_ℝ ∂ν) =
      ∫ x,⟪gradient F x,(WeightedTangent.representative τ σ).val x⟫_ℝ ∂τ := by
  subst τ
  rfl

variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
  (hN : 0 < N) (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
  (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
  {μ : ℝ → Measure (Position d)} (hμ : IsLimitEvolution b μ)
  {T : ℝ} (hT : 0 ≤ T) (P : Measure (Configuration d N)) [IsProbabilityMeasure P]

/-- Genuine canonical source pairing for bounded smooth Euclidean tests,
including noncompact cylinders. -/
theorem prescribedSourcePairing_eq_canonical_pairing {F : Point (N*d) → ℝ}
    (hF : ContDiff ℝ ∞ F) (hBF : AllDerivativesBounded F) {s : ℝ} (hs : s ∈ Icc 0 T) :
    letI : IsProbabilityMeasure (PrescribedSwitchCurve.law hN hb hbound hM hL₁ hL₂ hμ hT P s) :=
      SwitchCurve.law_probability hN hb hbound hM hL₁ hL₂ _ _ _ hT P hs
    prescribedSourcePairing hN hb hbound hM hL₁ hL₂ hμ hT P (F ∘ configurationEuclidean d N) s =
      ∫ x,⟪gradient F x,
        (WeightedTangent.representative
          (euclideanLaw (PrescribedSwitchCurve.law hN hb hbound hM hL₁ hL₂ hμ hT P s))
          (prescribedBrownianSource hN hb hbound hM hL₁ hL₂ hμ hT P s)).val x⟫_ℝ
        ∂euclideanLaw (PrescribedSwitchCurve.law hN hb hbound hM hL₁ hL₂ hμ hT P s) := by
  letI : IsProbabilityMeasure (PrescribedSwitchCurve.law hN hb hbound hM hL₁ hL₂ hμ hT P s) :=
    SwitchCurve.law_probability hN hb hbound hM hL₁ hL₂ _ _ _ hT P hs
  letI : IsProbabilityMeasure (PrescribedReference.law hb hbound hM hL₁ hμ N P s) :=
    BrownianFlow.globalLaw_probability _ _ _ P hs.1
  rw [prescribedSourcePairing_eq_action hN hb hbound hM hL₁ hL₂ hμ hT P hF.continuous hs]
  have hh := Brownian.action_eq_representative_pairing
    ((drift_lipschitz hN hb hbound hL₁ hL₂).continuous.comp continuous_snd)
    (fun _ => drift_norm_le hN hbound hM) (fun _ => drift_lipschitz hN hb hbound hL₁ hL₂)
    hT (particleDrift_smooth hb) (particleDrift_allDerivativesBounded hb)
    (euclideanLaw (PrescribedReference.law hb hbound hM hL₁ hμ N P s))
    (prescribedCurrent_memLp hN hb hbound hM hL₁ hμ P hs.1) hF hBF
    (show T-s ∈ Icc 0 T from ⟨sub_nonneg.mpr hs.2,sub_le_self _ hs.1⟩)
  unfold prescribedBrownianSource
  simp only [projIcc_of_mem _ hs]
  exact hh.trans (canonical_pairing_measure_congr _ _
    (prescribedBrownianSource_lawAt hN hb hbound hM hL₁ hL₂ hμ hT P hs) _ F)

variable {k : ℕ} [MeasurableSpace (Point (k*d))] [BorelSpace (Point (k*d))]

/-- The actual marginal source, extended outside the physical interval only
by clamping the switch parameter. -/
def prescribedMarginalSource (hk : k ≤ N) (s : ℝ) : Test (k*d) →ₗ[ℝ] ℝ :=
  let r := projIcc 0 T hT s
  letI : IsProbabilityMeasure (PrescribedSwitchCurve.law hN hb hbound hM hL₁ hL₂ hμ hT P r) :=
    SwitchCurve.law_probability hN hb hbound hM hL₁ hL₂ _ _ _ hT P r.property
  imageSource (euclideanLaw (PrescribedSwitchCurve.law hN hb hbound hM hL₁ hL₂ hμ hT P r))
    (prescribedBrownianSource hN hb hbound hM hL₁ hL₂ hμ hT P r) (marginalProjection hk)

/-- On the physical interval the source is literally the image source whose
full Euclidean energy is bounded by propagation. -/
theorem prescribedMarginalSource_eq (hk : k ≤ N) {s : ℝ} (hs : s ∈ Icc 0 T) :
    letI : IsProbabilityMeasure (PrescribedSwitchCurve.law hN hb hbound hM hL₁ hL₂ hμ hT P s) :=
      SwitchCurve.law_probability hN hb hbound hM hL₁ hL₂ _ _ _ hT P hs
    prescribedMarginalSource hN hb hbound hM hL₁ hL₂ hμ hT P hk s =
      imageSource (euclideanLaw (PrescribedSwitchCurve.law hN hb hbound hM hL₁ hL₂ hμ hT P s))
        (prescribedBrownianSource hN hb hbound hM hL₁ hL₂ hμ hT P s) (marginalProjection hk) := by
  simp only [prescribedMarginalSource,projIcc_of_mem _ hs]

/-- Every compact marginal test gives exactly the already proved scalar
switch derivative. Its full-space lift is treated as a bounded smooth test. -/
theorem prescribedMarginalSource_pairing (hk : k ≤ N) {s : ℝ} (hs : s ∈ Icc 0 T)
    (φ : Test (k*d)) :
    prescribedMarginalSource hN hb hbound hM hL₁ hL₂ hμ hT P hk s φ =
      prescribedSourcePairing hN hb hbound hM hL₁ hL₂ hμ hT P
        ((φ.val ∘ marginalProjection hk) ∘ configurationEuclidean d N) s := by
  letI : IsProbabilityMeasure (PrescribedSwitchCurve.law hN hb hbound hM hL₁ hL₂ hμ hT P s) :=
    SwitchCurve.law_probability hN hb hbound hM hL₁ hL₂ _ _ _ hT P hs
  rw [prescribedMarginalSource_eq hN hb hbound hM hL₁ hL₂ hμ hT P hk hs,imageSource_apply]
  exact (prescribedSourcePairing_eq_canonical_pairing hN hb hbound hM hL₁ hL₂ hμ hT P
    (φ.property.1.comp (marginalProjection hk).contDiff)
    ((RoughEulerianSmoothing.allDerivativesBounded_of_compact φ.property.1 φ.property.2).comp_linear
      φ.property.1 (marginalProjection hk)) hs).symm

end SharpWasserstein.SwitchSourceDerivative
