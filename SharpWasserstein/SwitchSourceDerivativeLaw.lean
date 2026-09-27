import SharpWasserstein.SwitchSourceDerivativeRemainingTest
import SharpWasserstein.SwitchSourceDerivativeShortTime
import SharpWasserstein.SwitchSourceDerivativeRestart
import SharpWasserstein.PropagatedSourceEquationBrownian

/-! Exact law algebra for the actual switch curve. Restart of the reference
law and the particle semigroup convert its increment into a synchronous
short-time drift comparison against the genuine remaining-time test. -/
noncomputable section
open Set MeasureTheory
open scoped Topology NNReal ContDiff
namespace SharpWasserstein.SwitchSourceDerivative
open PropagatedSourceEquation
variable {d N : ℕ} {b : Configuration d N → Configuration d N} {A H : ℝ≥0}
  (hb : ∀ x, ‖b x‖ ≤ A) (hLip : LipschitzWith H b)
  {T : ℝ} (hT : 0 ≤ T)

/-- On admissible remaining times the clamped test is exactly the actual
Brownian transition expectation. -/
theorem remainingTest_eq_transition {F : Configuration d N → ℝ} (hF : Continuous F)
    {τ r : ℝ} (hr : τ-r ∈ Icc 0 T) (x : Configuration d N) :
    remainingTest hb hLip hT (BrownianNoise.configurationLaw d N T) F τ r x =
      ∫ z,F z ∂BrownianFlow.globalLaw (v := fun _ : ℝ => b) (hLip.continuous.comp continuous_snd)
        (fun _ => hb) (fun _ => hLip) (Measure.dirac x) (τ-r) := by
  rw [remainingTest,clampedExpectation_of_mem _ _ _ _ _ _ hr]
  exact brownianExpectation_eq_globalLaw _ _ _ hT x hF hr

/-- Integrating the remaining test against any actual initial probability
law gives its true future transition expectation. -/
theorem integral_remainingTest_eq {F : Configuration d N → ℝ} (hF : Continuous F)
    {C : ℝ} (hC : ∀ x, ‖F x‖ ≤ C) (ν : Measure (Configuration d N)) [IsProbabilityMeasure ν]
    {τ r : ℝ} (hr : τ-r ∈ Icc 0 T) :
    (∫ x,remainingTest hb hLip hT (BrownianNoise.configurationLaw d N T) F τ r x ∂ν) =
      ∫ z,F z ∂BrownianFlow.globalLaw (v := fun _ : ℝ => b) (hLip.continuous.comp continuous_snd)
        (fun _ => hb) (fun _ => hLip) ν (τ-r) := by
  have he := BrownianFlow.globalLaw_add_integral (hLip.continuous.comp continuous_snd)
    (fun _ => hb) (fun _ => hLip) (show (0:ℝ) ≤ 0 from le_rfl) hr.1 ν hF hC
  simp only [zero_add,BrownianFlow.globalLaw_initial] at he
  rw [he]
  apply integral_congr_ae
  filter_upwards [] with x
  exact remainingTest_eq_transition hb hLip hT hF hr x

variable {v : ℝ → Configuration d N → Configuration d N} {M K : ℝ≥0}
  (hv : Continuous (Function.uncurry v)) (hbv : ∀ r x, ‖v r x‖ ≤ M)
  (hlv : ∀ r, LipschitzWith K (v r))

/-- The actual reference evolution followed by the actual particle evolution. -/
def switchLaw (μ : Measure (Configuration d N)) (s : ℝ) : Measure (Configuration d N) :=
  BrownianFlow.globalLaw (v := fun _ : ℝ => b) (hLip.continuous.comp continuous_snd)
    (fun _ => hb) (fun _ => hLip) (BrownianFlow.globalLaw hv hbv hlv μ s) (T-s)

/-- Exact finite switch increment as a synchronous short-time comparison.
This identity uses the genuine time-dependent drift v(s+r), not v(s). -/
theorem switch_integral_increment_eq
    (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    {F : Configuration d N → ℝ} (hF : ContDiff ℝ 1 F) {C : ℝ} (hC : ∀ x, ‖F x‖ ≤ C)
    {s r : ℝ} (hs : s ∈ Icc 0 T) (hr : r ∈ Icc 0 (T-s)) :
    (∫ z,F z ∂switchLaw hb hLip hv hbv hlv (T := T) μ (s+r))-
        (∫ z,F z ∂switchLaw hb hLip hv hbv hlv (T := T) μ s) =
      ∫ p,flowTestDifference (q := fun _ : ℝ => b) (shiftedDrift_continuous hv s)
        (fun u => hbv (s+u)) (fun u => hlv (s+u))
        (hLip.continuous.comp continuous_snd) (fun _ => hb) (fun _ => hLip) hT
        (remainingTest hb hLip hT (BrownianNoise.configurationLaw d N T) F (T-s) r) r p
        ∂(BrownianFlow.globalLaw hv hbv hlv μ s).prod (BrownianNoise.configurationLaw d N T) := by
  let ν := BrownianFlow.globalLaw hv hbv hlv μ s
  letI : IsProbabilityMeasure ν := BrownianFlow.globalLaw_probability hv hbv hlv μ hs.1
  let f := remainingTest hb hLip hT (BrownianNoise.configurationLaw d N T) F (T-s) r
  have hf : Continuous f := (remainingTest_continuous hb hLip hT
    (BrownianNoise.configurationLaw d N T) hF hC (T-s)).comp
      (continuous_const.prodMk continuous_id)
  have hfB (x : Configuration d N) : ‖f x‖ ≤ C :=
    remainingTest_norm_le hb hLip hT (BrownianNoise.configurationLaw d N T) hC (T-s) r x
  have hrT : r ∈ Icc 0 T := ⟨hr.1,by linarith [hr.2,hs.1]⟩
  have hremain : T-s-r ∈ Icc 0 T := ⟨by linarith [hr.2],by linarith [hs.1,hr.1]⟩
  let νv := BrownianFlow.globalLaw (shiftedDrift_continuous hv s)
    (fun u => hbv (s+u)) (fun u => hlv (s+u)) ν r
  let νb := BrownianFlow.globalLaw (v := fun _ : ℝ => b) (hLip.continuous.comp continuous_snd)
    (fun _ => hb) (fun _ => hLip) ν r
  letI : IsProbabilityMeasure νv := BrownianFlow.globalLaw_probability _ _ _ ν hr.1
  letI : IsProbabilityMeasure νb := BrownianFlow.globalLaw_probability _ _ _ ν hr.1
  have he₁ : (∫ z,F z ∂switchLaw hb hLip hv hbv hlv (T := T) μ (s+r)) = ∫ x,f x ∂νv := by
    rw [integral_remainingTest_eq hb hLip hT hF.continuous hC νv hremain]
    unfold switchLaw νv ν
    rw [brownianGlobalLaw_add_shift hv hbv hlv hs.1 hr.1 μ]
    congr 1
    congr 1
    ring
  have he₂ : (∫ z,F z ∂switchLaw hb hLip hv hbv hlv (T := T) μ s) = ∫ x,f x ∂νb := by
    rw [integral_remainingTest_eq hb hLip hT hF.continuous hC νb hremain]
    unfold switchLaw νb ν
    rw [← BrownianFlow.globalLaw_add (hLip.continuous.comp continuous_snd)
      (fun _ => hb) (fun _ => hLip) hr.1 hremain.1]
    congr 1
    congr 1
    ring
  rw [he₁,he₂]
  have hvEq := BrownianFlow.globalLaw_eq (shiftedDrift_continuous hv s)
    (fun u => hbv (s+u)) (fun u => hlv (s+u)) hT ν hrT
  have hbEq := BrownianFlow.globalLaw_eq (v := fun _ : ℝ => b) (hLip.continuous.comp continuous_snd)
    (fun _ => hb) (fun _ => hLip) hT ν hrT
  change (∫ x,f x ∂BrownianFlow.globalLaw _ _ _ ν r)-
    (∫ x,f x ∂BrownianFlow.globalLaw _ _ _ ν r) = _
  rw [hvEq,hbEq,BrownianFlow.law_integral_eq _ _ _ hT ν hf hrT,
    BrownianFlow.law_integral_eq _ _ _ hT ν hf hrT]
  have hi₁ : Integrable (fun p : Configuration d N × C(Icc 0 T,Configuration d N) =>
      f (BoundedFlow.flow (shiftedDrift_continuous hv s)
        (fun u => hbv (s+u)) (fun u => hlv (s+u)) hT p.1 p.2 r))
        (ν.prod (BrownianNoise.configurationLaw d N T)) :=
    Integrable.of_bound (hf.comp (BoundedFlow.flow_continuous _ _ _ hT hrT)).aestronglyMeasurable C
      (Filter.Eventually.of_forall (fun _ => hfB _))
  have hi₂ : Integrable (fun p : Configuration d N × C(Icc 0 T,Configuration d N) =>
      f (BoundedFlow.flow (v := fun _ : ℝ => b) (hLip.continuous.comp continuous_snd)
        (fun _ => hb) (fun _ => hLip) hT p.1 p.2 r))
        (ν.prod (BrownianNoise.configurationLaw d N T)) :=
    Integrable.of_bound (hf.comp (BoundedFlow.flow_continuous _ _ _ hT hrT)).aestronglyMeasurable C
      (Filter.Eventually.of_forall (fun _ => hfB _))
  exact (integral_sub hi₁ hi₂).symm

end SharpWasserstein.SwitchSourceDerivative
