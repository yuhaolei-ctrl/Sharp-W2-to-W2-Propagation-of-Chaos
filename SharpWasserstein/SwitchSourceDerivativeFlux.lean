module

public import SharpWasserstein.Compat
public import SharpWasserstein.SwitchSourceDerivativeEquation
public import SharpWasserstein.FlowSemigroupDerivativePairing

@[expose] public section

/-! The derived switch derivative is identified with the actual propagated
Jacobian-current integral. Its initial field is genuinely L², and the joint
pairing is genuinely integrable before applying Fubini. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology NNReal ContDiff
namespace SharpWasserstein.SwitchSourceDerivative
open NoiseAverage FlowSemigroupDerivative PropagatedSourceEquation
variable {d N : ℕ} {b : Configuration d N → Configuration d N} {A H : ℝ≥0}
  (hb : ∀ x, ‖b x‖ ≤ A) (hLip : LipschitzWith H b)
  {v : ℝ → Configuration d N → Configuration d N} {M K : ℝ≥0}
  (hv : Continuous (Function.uncurry v)) (hbv : ∀ r x, ‖v r x‖ ≤ M)
  (hlv : ∀ r, LipschitzWith K (v r))
  {T : ℝ} (hT : 0 ≤ T)

include hb hLip hv hbv in
/-- The true drift defect is L² under every finite initial law; neither an
entropy estimate nor a source-energy estimate is being assumed. -/
theorem driftDifference_memLp (ν : Measure (Configuration d N)) [IsFiniteMeasure ν] (s : ℝ) :
    MemLp (fun x => v s x-b x) 2 ν := by
  apply MemLp.of_bound
    (((hv.comp (continuous_const.prodMk continuous_id)).sub hLip.continuous).aestronglyMeasurable)
    ((M:ℝ)+A)
  exact Eventually.of_forall (fun x => (norm_sub_le _ _).trans (add_le_add (hbv s x) (hb x)))

variable (hbs : ContDiff ℝ ∞ b) (hB : AllDerivativesBounded b)
  (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
  {F : Configuration d N → ℝ} (hF : ContDiff ℝ 1 F)
  {C : ℝ} (hC : ∀ x, ‖F x‖ ≤ C) {L : ℝ≥0} (hL : ∀ x, ‖fderiv ℝ F x‖ ≤ L)

include hbs hB hF hL in
/-- Absolute integrability of the actual propagated switch-current pairing. -/
theorem switch_flux_pairing_integrable {s : ℝ} (hs : s ∈ Icc 0 T) :
    Integrable (fun p : Configuration d N × C(Icc 0 T,Configuration d N) =>
      fderiv ℝ F (BoundedFlow.flow (v := fun _ : ℝ => b)
        (hLip.continuous.comp continuous_snd) (fun _ => hb) (fun _ => hLip) hT p.1 p.2 (T-s))
        (fderiv ℝ (fun y => BoundedFlow.flow (v := fun _ : ℝ => b)
          (hLip.continuous.comp continuous_snd) (fun _ => hb) (fun _ => hLip) hT y p.2 (T-s)) p.1
          (v s p.1-b p.1)))
      ((BrownianFlow.globalLaw hv hbv hlv μ s).prod (BrownianNoise.configurationLaw d N T)) := by
  letI := BrownianFlow.globalLaw_probability hv hbv hlv μ hs.1
  exact integrable_differential_pairing
    (hLip.continuous.comp continuous_snd) (fun _ => hb) (fun _ => hLip) hT
    (BrownianNoise.configurationLaw d N T) ⟨sub_nonneg.mpr hs.2,sub_le_self _ hs.1⟩ hbs hB
    (BrownianFlow.globalLaw hv hbv hlv μ s) hF hL
    (driftDifference_memLp hb hLip hv hbv (BrownianFlow.globalLaw hv hbv hlv μ s) s)

include hbs hB hF hC hL in
/-- Exact literal JV formula for the source in the proved switch equation. -/
theorem sourcePairing_eq_integral_JV {s : ℝ} (hs : s ∈ Icc 0 T) :
    sourcePairing hb hLip hv hbv hlv hT μ F s =
      ∫ p : Configuration d N × C(Icc 0 T,Configuration d N),
        fderiv ℝ F (BoundedFlow.flow (v := fun _ : ℝ => b)
          (hLip.continuous.comp continuous_snd) (fun _ => hb) (fun _ => hLip) hT p.1 p.2 (T-s))
          (fderiv ℝ (fun y => BoundedFlow.flow (v := fun _ : ℝ => b)
            (hLip.continuous.comp continuous_snd) (fun _ => hb) (fun _ => hLip) hT y p.2 (T-s)) p.1
            (v s p.1-b p.1))
        ∂(BrownianFlow.globalLaw hv hbv hlv μ s).prod (BrownianNoise.configurationLaw d N T) := by
  letI := BrownianFlow.globalLaw_probability hv hbv hlv μ hs.1
  have ht : T-s ∈ Icc 0 T := ⟨sub_nonneg.mpr hs.2,sub_le_self _ hs.1⟩
  have he : remainingTest hb hLip hT (BrownianNoise.configurationLaw d N T) F T s =
      expectation (hLip.continuous.comp continuous_snd) (fun _ => hb) (fun _ => hLip)
        hT (BrownianNoise.configurationLaw d N T) (t := T-s) F :=
    clampedExpectation_of_mem _ _ _ _ _ _ ht
  unfold sourcePairing
  rw [he]
  exact integral_fderiv_expectation_eq
    (hLip.continuous.comp continuous_snd) (fun _ => hb) (fun _ => hLip) hT
    (BrownianNoise.configurationLaw d N T) ht hbs hB (BrownianFlow.globalLaw hv hbv hlv μ s)
    hF hC hL (driftDifference_memLp hb hLip hv hbv (BrownianFlow.globalLaw hv hbv hlv μ s) s)

end SharpWasserstein.SwitchSourceDerivative
