import SharpWasserstein.SwitchSourceDerivativeLaw
import SharpWasserstein.SwitchSourceDerivativeMovingExpectation

/-! The actual switch law has the derived right derivative
 ∫ D(P_{T-s}F)(x)(v(s,x)-b(x)) dR_s(x).
Both diffusion stages use the constructed sqrt(2)-Brownian noise. -/
noncomputable section
open Set MeasureTheory
open scoped Topology NNReal ContDiff
namespace SharpWasserstein.SwitchSourceDerivative
open NoiseAverage
variable {d N : ℕ} {b : Configuration d N → Configuration d N} {A H : ℝ≥0}
  (hb : ∀ x, ‖b x‖ ≤ A) (hLip : LipschitzWith H b)
  {v : ℝ → Configuration d N → Configuration d N} {M K : ℝ≥0}
  (hv : Continuous (Function.uncurry v)) (hbv : ∀ r x, ‖v r x‖ ≤ M)
  (hlv : ∀ r, LipschitzWith K (v r))
  {T : ℝ} (hT : 0 ≤ T)

/-- Literal propagated drift-difference pairing on the actual reference law. -/
def sourcePairing (μ : Measure (Configuration d N)) (F : Configuration d N → ℝ) (s : ℝ) : ℝ :=
  ∫ x,fderiv ℝ (remainingTest hb hLip hT (BrownianNoise.configurationLaw d N T) F T s) x
    (v s x-b x) ∂BrownianFlow.globalLaw hv hbv hlv μ s

variable (hbs : ContDiff ℝ ∞ b) (hB : AllDerivativesBounded b)
  (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
  {F : Configuration d N → ℝ} (hF : ContDiff ℝ 1 F)
  {C : ℝ} (hC : ∀ x, ‖F x‖ ≤ C) {L : ℝ≥0} (hL : ∀ x, ‖fderiv ℝ F x‖ ≤ L)

include hbs hB hF hC hL

/-- The actual switch increment is differentiable in its nonnegative increment
parameter. No assumed source equation or backward generator identity occurs. -/
theorem switch_increment_hasDerivWithinAt_zero {s : ℝ} (hs : s ∈ Icc 0 T) :
    HasDerivWithinAt
      (fun r => ∫ z,F z ∂switchLaw hb hLip hv hbv hlv (T := T) μ (s+r))
      (sourcePairing hb hLip hv hbv hlv hT μ F s) (Icc 0 (T-s)) 0 := by
  let ν := BrownianFlow.globalLaw hv hbv hlv μ s
  letI : IsProbabilityMeasure ν := BrownianFlow.globalLaw_probability hv hbv hlv μ hs.1
  let ξ := BrownianNoise.configurationLaw d N T
  let Ψ := remainingTest hb hLip hT ξ F (T-s)
  let L' : ℝ≥0 := ⟨(L:ℝ)*Real.exp ((H:ℝ)*T),by positivity⟩
  have hΨ (r : ℝ) : ContDiff ℝ 1 (Ψ r) :=
    remainingTest_contDiff_one hb hLip hT ξ hbs hB hF hC hL (T-s) r
  have hDΨ : Continuous (fun p : ℝ × Configuration d N => fderiv ℝ (Ψ p.1) p.2) :=
    remainingTest_fderiv_joint_continuous hb hLip hT ξ hbs hB hF hC hL (T-s)
  have hLΨ (r : ℝ) (x : Configuration d N) : ‖fderiv ℝ (Ψ r) x‖ ≤ L' :=
    remainingTest_fderiv_norm_le hb hLip hT ξ hbs hB hF hC hL (T-s) r x
  have hd := integral_moving_flowTestDifference_hasDerivWithinAt_zero (q := fun _ : ℝ => b)
    (shiftedDrift_continuous hv s) (fun u => hbv (s+u)) (fun u => hlv (s+u))
    (hLip.continuous.comp continuous_snd) (fun _ => hb) (fun _ => hLip) hT
    ν ξ (BrownianNoise.configurationLaw_zero_ae hT) hΨ hDΨ hLΨ
  have hd' := hd.mono (show Icc 0 (T-s) ⊆ Icc 0 T from Icc_subset_Icc_right (by linarith [hs.1]))
  have he : ∀ r ∈ Icc 0 (T-s),
      (∫ z,F z ∂switchLaw hb hLip hv hbv hlv (T := T) μ (s+r))-
        (∫ z,F z ∂switchLaw hb hLip hv hbv hlv (T := T) μ s) =
      ∫ p,flowTestDifference (q := fun _ : ℝ => b) (shiftedDrift_continuous hv s)
        (fun u => hbv (s+u)) (fun u => hlv (s+u))
        (hLip.continuous.comp continuous_snd) (fun _ => hb) (fun _ => hLip) hT (Ψ r) r p
        ∂ν.prod ξ := fun r hr => switch_integral_increment_eq hb hLip hT hv hbv hlv μ hF hC hs hr
  have hg := hd'.congr_of_mem he (show (0:ℝ) ∈ Icc 0 (T-s) from ⟨le_rfl,sub_nonneg.mpr hs.2⟩)
  have heΨ : Ψ 0 = remainingTest hb hLip hT ξ F T s := by
    funext x
    simp only [Ψ,remainingTest,sub_zero]
  have hg' := hg.add_const (∫ z,F z ∂switchLaw hb hLip hv hbv hlv (T := T) μ s)
  rw [heΨ] at hg'
  simpa only [sub_add_cancel,sourcePairing,ν,ξ,shiftedDrift,add_zero] using hg'

/-- The parameter s itself has the same derivative on its right interval. -/
theorem switch_integral_hasDerivWithinAt {s : ℝ} (hs : s ∈ Icc 0 T) :
    HasDerivWithinAt
      (fun r => ∫ z,F z ∂switchLaw hb hLip hv hbv hlv (T := T) μ r)
      (sourcePairing hb hLip hv hbv hlv hT μ F s) (Icc s T) s := by
  have hd := switch_increment_hasDerivWithinAt_zero hb hLip hv hbv hlv hT hbs hB μ hF hC hL hs
  have hm : MapsTo (fun r : ℝ => r-s) (Icc s T) (Icc 0 (T-s)) := by
    intro r hr
    exact ⟨sub_nonneg.mpr hr.1,sub_le_sub_right hr.2 s⟩
  have hd' := hd.scomp_of_eq (h := fun r : ℝ => r-s) s
    ((hasDerivAt_id s).sub_const s).hasDerivWithinAt hm (by simp)
  simpa only [sub_self,one_smul,Function.comp_def,add_sub_cancel] using hd'

/-- The true right derivative at every interior switch time, including zero. -/
theorem switch_integral_hasDerivWithinAt_right {s : ℝ} (hs : s ∈ Ico 0 T) :
    HasDerivWithinAt
      (fun r => ∫ z,F z ∂switchLaw hb hLip hv hbv hlv (T := T) μ r)
      (sourcePairing hb hLip hv hbv hlv hT μ F s) (Ici s) s := by
  apply (switch_integral_hasDerivWithinAt hb hLip hv hbv hlv hT hbs hB μ hF hC hL
    ⟨hs.1,hs.2.le⟩).mono_of_mem_nhdsWithin
  rw [← Ici_inter_Iic]
  exact Filter.inter_mem self_mem_nhdsWithin
    (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds hs.2))

end SharpWasserstein.SwitchSourceDerivative
