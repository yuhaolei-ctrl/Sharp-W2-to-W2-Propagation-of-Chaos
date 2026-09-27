import SharpWasserstein.SwitchSourceDerivativeParticle
import SharpWasserstein.InitialSourcePermutation

/-! The manuscript's prescribed nonlinear reference is used literally.
The resulting derivative has reference-minus-particle direction and is the
actual generator-difference current propagated by the particle transition. -/
noncomputable section
open Set MeasureTheory
open scoped Topology NNReal ContDiff Interval
namespace SharpWasserstein.SwitchSourceDerivative
variable {d N : ℕ} {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
  (hN : 0 < N) (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
  (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
  {μ : ℝ → Measure (Position d)} (hμ : IsLimitEvolution b μ) {T : ℝ} (hT : 0 ≤ T)

/-- Genuine remaining-time interacting transition test on the fixed Brownian horizon. -/
def particleRemainingTest (F : Configuration d N → ℝ) (s : ℝ) : Configuration d N → ℝ :=
  remainingTest (M := NNReal.mk M hM) (fun x => particleDrift_norm_bound hN hbound hM x)
    (particleDrift_lipschitz hN hb hbound hL₁ hL₂) hT
    (BrownianNoise.configurationLaw d N T) F T s

/-- The actual prescribed-reference source, propagated for the remaining time. -/
def prescribedSourcePairing (P : Measure (Configuration d N)) (F : Configuration d N → ℝ) (s : ℝ) : ℝ :=
  particleSourcePairing hN hb hbound hM hL₁ hL₂
    (DecoupledFlow.liftDrift_continuous N (PrescribedReference.singleDrift_continuous hb hbound hL₁ hμ))
    (DecoupledFlow.liftDrift_bound N (PrescribedReference.singleDrift_bound hbound hM hμ))
    (DecoupledFlow.liftDrift_lipschitz N (PrescribedReference.singleDrift_lipschitz hb hbound hL₁ hμ)) hT P F s

/-- At every admissible time the current is exactly the empirical drift defect
from the supplied nonlinear one-particle law; there is no substituted flow law. -/
theorem prescribedSourcePairing_eq_current (P : Measure (Configuration d N))
    (F : Configuration d N → ℝ) {s : ℝ} (hs : 0 ≤ s) :
    prescribedSourcePairing hN hb hbound hM hL₁ hL₂ hμ hT P F s =
      ∫ x,fderiv ℝ (particleRemainingTest hN hb hbound hM hL₁ hL₂ hT F s) x
        (InitialSourcePermutation.initialCurrent b (μ s) x)
        ∂PrescribedReference.law hb hbound hM hL₁ hμ N P s := by
  unfold prescribedSourcePairing particleSourcePairing sourcePairing particleRemainingTest
    InitialSourcePermutation.initialCurrent PrescribedReference.law
    DecoupledFlow.liftDrift PrescribedReference.singleDrift
  simp only [max_eq_right hs]

/-- Both diffusion terms cancel, giving the literal difference of the two
configuration generators applied to the remaining transition test. -/
theorem prescribedSourcePairing_eq_generator_difference
    (P : Measure (Configuration d N)) (F : Configuration d N → ℝ) {s : ℝ} (hs : 0 ≤ s) :
    prescribedSourcePairing hN hb hbound hM hL₁ hL₂ hμ hT P F s =
      ∫ x,(generator (fun z i => nonlinearDrift b (μ s) (z i))
          (particleRemainingTest hN hb hbound hM hL₁ hL₂ hT F s) x-
        generator (particleDrift b)
          (particleRemainingTest hN hb hbound hM hL₁ hL₂ hT F s) x)
        ∂PrescribedReference.law hb hbound hM hL₁ hμ N P s := by
  rw [prescribedSourcePairing_eq_current hN hb hbound hM hL₁ hL₂ hμ hT P F hs]
  apply integral_congr_ae
  filter_upwards [] with x
  exact (InitialSourcePermutation.generator_difference b (μ s) _ x).symm

/-- Actual switch derivative for the nonlinear prescribed reference law. -/
theorem prescribed_switch_hasDerivAt
    (P : Measure (Configuration d N)) [IsProbabilityMeasure P]
    {F : Configuration d N → ℝ} (hF : ContDiff ℝ 1 F) {C : ℝ} (hC : ∀ x, ‖F x‖ ≤ C)
    {L : ℝ≥0} (hL : ∀ x, ‖fderiv ℝ F x‖ ≤ L) {s : ℝ} (hs : s ∈ Ioo 0 T) :
    HasDerivAt (fun r => ∫ x,F x ∂PrescribedSwitchCurve.law hN hb hbound hM hL₁ hL₂ hμ hT P r)
      (prescribedSourcePairing hN hb hbound hM hL₁ hL₂ hμ hT P F s) s :=
  particle_switch_hasDerivAt hN hb hbound hM hL₁ hL₂ _ _ _ hT P hF hC hL hs

/-- Integrated form includes the two genuine endpoints of the switch curve. -/
theorem prescribed_switch_sub_eq_integral
    (P : Measure (Configuration d N)) [IsProbabilityMeasure P]
    {F : Configuration d N → ℝ} (hF : ContDiff ℝ 1 F) {C : ℝ} (hC : ∀ x, ‖F x‖ ≤ C)
    {L : ℝ≥0} (hL : ∀ x, ‖fderiv ℝ F x‖ ≤ L)
    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (hst : s ≤ t) :
    (∫ x,F x ∂PrescribedSwitchCurve.law hN hb hbound hM hL₁ hL₂ hμ hT P t)-
      (∫ x,F x ∂PrescribedSwitchCurve.law hN hb hbound hM hL₁ hL₂ hμ hT P s) =
      ∫ r in s..t,prescribedSourcePairing hN hb hbound hM hL₁ hL₂ hμ hT P F r :=
  particle_switch_sub_eq_integral hN hb hbound hM hL₁ hL₂ _ _ _ hT P hF hC hL hs ht hst

/-- Compact smooth tests automatically supply every first-order test bound. -/
theorem configuration_compact_test_bounds {F : Configuration d N → ℝ} (hF : SmoothCompactTest F) :
    ∃ (C : ℝ) (L : ℝ≥0), (∀ x, ‖F x‖ ≤ C) ∧ (∀ x, ‖fderiv ℝ F x‖ ≤ L) := by
  obtain ⟨C,hC⟩ := hF.2.exists_bound_of_continuous hF.1.continuous
  obtain ⟨L,hL⟩ := (hF.2.fderiv ℝ).exists_bound_of_continuous (hF.1.continuous_fderiv (by simp))
  exact ⟨C,NNReal.mk L ((norm_nonneg (fderiv ℝ F 0)).trans (hL 0)),hC,hL⟩

/-- The requested compact C∞ switch identity has no extra bounded-test premises. -/
theorem prescribed_switch_compact_hasDerivAt
    (P : Measure (Configuration d N)) [IsProbabilityMeasure P]
    {F : Configuration d N → ℝ} (hF : SmoothCompactTest F) {s : ℝ} (hs : s ∈ Ioo 0 T) :
    HasDerivAt (fun r => ∫ x,F x ∂PrescribedSwitchCurve.law hN hb hbound hM hL₁ hL₂ hμ hT P r)
      (prescribedSourcePairing hN hb hbound hM hL₁ hL₂ hμ hT P F s) s := by
  obtain ⟨C,L,hC,hL⟩ := configuration_compact_test_bounds hF
  exact prescribed_switch_hasDerivAt hN hb hbound hM hL₁ hL₂ hμ hT P
    (hF.1.of_le (by simp)) hC hL hs

/-- Compact smooth tests also give the integrated source identity with both
endpoints included and without separately supplied norm bounds. -/
theorem prescribed_switch_compact_sub_eq_integral
    (P : Measure (Configuration d N)) [IsProbabilityMeasure P]
    {F : Configuration d N → ℝ} (hF : SmoothCompactTest F)
    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (hst : s ≤ t) :
    (∫ x,F x ∂PrescribedSwitchCurve.law hN hb hbound hM hL₁ hL₂ hμ hT P t)-
      (∫ x,F x ∂PrescribedSwitchCurve.law hN hb hbound hM hL₁ hL₂ hμ hT P s) =
      ∫ r in s..t,prescribedSourcePairing hN hb hbound hM hL₁ hL₂ hμ hT P F r := by
  obtain ⟨C,L,hC,hL⟩ := configuration_compact_test_bounds hF
  exact prescribed_switch_sub_eq_integral hN hb hbound hM hL₁ hL₂ hμ hT P
    (hF.1.of_le (by simp)) hC hL hs ht hst

end SharpWasserstein.SwitchSourceDerivative
