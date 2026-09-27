import SharpWasserstein.SwitchSourceDerivativeEquation
import SharpWasserstein.SwitchCurveProperties
import SharpWasserstein.ParticleWeakIdentification

/-! Direct specialization to the manuscript's actual interacting switch
curve. Smoothness of the full particle drift is derived from the interaction,
and the reference drift remains genuinely time dependent. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology NNReal ContDiff Interval
namespace SharpWasserstein.SwitchSourceDerivative

variable {d N : ℕ} {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
  (hN : 0 < N) (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
  (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
  {v : ℝ → Configuration d N → Configuration d N} {A K : ℝ≥0}
  (hv : Continuous (Function.uncurry v)) (hvb : ∀ t x, ‖v t x‖ ≤ A)
  (hvl : ∀ t, LipschitzWith K (v t)) {T : ℝ} (hT : 0 ≤ T)

/-- The literal source pairing for the existing interacting switch law. -/
def particleSourcePairing (μ : Measure (Configuration d N)) (F : Configuration d N → ℝ) (s : ℝ) : ℝ :=
  sourcePairing (A := NNReal.mk M hM) (fun x => particleDrift_norm_bound hN hbound hM x)
    (particleDrift_lipschitz hN hb hbound hL₁ hL₂) hv hvb hvl hT μ F s

/-- The generic actual composition is exactly the pre-existing switch law. -/
theorem particle_switchLaw_eq (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : s ∈ Icc 0 T) :
    switchLaw (A := NNReal.mk M hM) (fun x => particleDrift_norm_bound hN hbound hM x)
      (particleDrift_lipschitz hN hb hbound hL₁ hL₂) hv hvb hvl (T := T) μ s =
      SwitchCurve.law hN hb hbound hM hL₁ hL₂ hv hvb hvl hT μ s := by
  exact (SwitchCurve.law_eq_global hN hb hbound hM hL₁ hL₂ hv hvb hvl hT μ hs).symm

/-- Ordinary switch derivative for the actual interacting diffusion and any
actual bounded jointly continuous spatially Lipschitz reference drift. -/
theorem particle_switch_hasDerivAt
    (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    {F : Configuration d N → ℝ} (hF : ContDiff ℝ 1 F) {C : ℝ} (hC : ∀ x, ‖F x‖ ≤ C)
    {L : ℝ≥0} (hL : ∀ x, ‖fderiv ℝ F x‖ ≤ L) {s : ℝ} (hs : s ∈ Ioo 0 T) :
    HasDerivAt (fun r => ∫ x,F x ∂SwitchCurve.law hN hb hbound hM hL₁ hL₂ hv hvb hvl hT μ r)
      (particleSourcePairing hN hb hbound hM hL₁ hL₂ hv hvb hvl hT μ F s) s := by
  have hd := switch_integral_hasDerivAt (A := NNReal.mk M hM)
    (fun x => particleDrift_norm_bound hN hbound hM x)
    (particleDrift_lipschitz hN hb hbound hL₁ hL₂) hv hvb hvl hT
    (particleDrift_smooth hb) (particleDrift_allDerivativesBounded hb) μ hF hC hL hs
  apply hd.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds hs.1 hs.2] with r hr
  rw [particle_switchLaw_eq hN hb hbound hM hL₁ hL₂ hv hvb hvl hT μ hr]

/-- Integrated identity on the full closed switch interval, including both
endpoints. No source-PDE or tangent-propagation conclusion is a hypothesis. -/
theorem particle_switch_sub_eq_integral
    (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    {F : Configuration d N → ℝ} (hF : ContDiff ℝ 1 F) {C : ℝ} (hC : ∀ x, ‖F x‖ ≤ C)
    {L : ℝ≥0} (hL : ∀ x, ‖fderiv ℝ F x‖ ≤ L)
    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (hst : s ≤ t) :
    (∫ x,F x ∂SwitchCurve.law hN hb hbound hM hL₁ hL₂ hv hvb hvl hT μ t)-
      (∫ x,F x ∂SwitchCurve.law hN hb hbound hM hL₁ hL₂ hv hvb hvl hT μ s) =
      ∫ r in s..t,particleSourcePairing hN hb hbound hM hL₁ hL₂ hv hvb hvl hT μ F r := by
  have he := switch_integral_sub_eq_integral (A := NNReal.mk M hM)
    (fun x => particleDrift_norm_bound hN hbound hM x)
    (particleDrift_lipschitz hN hb hbound hL₁ hL₂) hv hvb hvl hT
    (particleDrift_smooth hb) (particleDrift_allDerivativesBounded hb) μ hF hC hL hs ht hst
  rw [particle_switchLaw_eq hN hb hbound hM hL₁ hL₂ hv hvb hvl hT μ hs,
    particle_switchLaw_eq hN hb hbound hM hL₁ hL₂ hv hvb hvl hT μ ht] at he
  exact he

end SharpWasserstein.SwitchSourceDerivative
