import SharpWasserstein.RoughCommonLabelLift
import SharpWasserstein.SwitchCurveTimeEnergy
import SharpWasserstein.PrescribedSwitchMetricIdentification

/-! Actual common probability labels for every clamped switch marginal.
The mean-square continuity is proved from Brownian increments on the same
two paths; no transport-speed estimate is used to construct this data. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace SharpWasserstein.SwitchSourceDerivative
open RoughEulerianTransport
variable {d N k : ℕ} {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
  (hN : 0 < N) (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
  (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
  {μ : ℝ → Measure (Position d)} (hμ : IsLimitEvolution b μ)
  {T : ℝ} (hT : 0 ≤ T) (P : Measure (Configuration d N)) [IsProbabilityMeasure P]
  (hP : HasSecondMoment P) (hk : k ≤ N)

set_option maxHeartbeats 1200000 in
def prescribedMarginalCommonLabel :
    CommonLabelLift d k (prescribedMarginalCurve hN hb hbound hM hL₁ hL₂ hμ hT P hk) := by
  let hv := DecoupledFlow.liftDrift_continuous N
    (PrescribedReference.singleDrift_continuous hb hbound hL₁ hμ)
  let hvb := DecoupledFlow.liftDrift_bound N
    (PrescribedReference.singleDrift_bound hbound hM hμ)
  let hvl := DecoupledFlow.liftDrift_lipschitz N
    (PrescribedReference.singleDrift_lipschitz hb hbound hL₁ hμ)
  let ξ := BrownianNoise.configurationLaw d N T
  let Ω := (Configuration d N × C(Icc 0 T,Configuration d N)) × C(Icc 0 T,Configuration d N)
  let F := fun p : ℝ × Ω => restrictCoordinates hk
    (SwitchCurve.jointEndpoint hN hb hbound hM hL₁ hL₂ hv hvb hvl hT (projIcc 0 T hT p.1) p.2)
  have hc := SwitchCurve.jointEndpoint_continuous hN hb hbound hM hL₁ hL₂ hv hvb hvl hT
  have hF : Measurable F := (measurable_restrictCoordinates hk).comp
    (hc.measurable.comp (((continuous_projIcc (h := hT)).measurable.comp measurable_fst).prodMk measurable_snd))
  refine {
    Ω := Ω
    P := (P.prod ξ).prod ξ
    F := F
    measurable := hF
    law := ?_
    modulus := ?_ }
  · intro t
    rw [prescribedMarginalCurve_map_configuration hN hb hbound hM hL₁ hL₂ hμ hT P hP hk t]
    change marginal hk (SwitchCurve.law hN hb hbound hM hL₁ hL₂ hv hvb hvl hT P
      (projIcc 0 T hT t)) = _
    rw [SwitchCurve.law_eq_jointEndpoint hN hb hbound hM hL₁ hL₂ hv hvb hvl hT P
      (projIcc 0 T hT t)]
    unfold marginal
    exact Measure.map_map (measurable_restrictCoordinates hk)
      (show Measurable (SwitchCurve.jointEndpoint hN hb hbound hM hL₁ hL₂ hv hvb hvl hT
        (projIcc 0 T hT t)) from (hc.comp (continuous_const.prodMk continuous_id)).measurable)
  · intro s
    exact (SwitchCurve.jointEndpoint_marginal_cost_tendsto
      hN hb hbound hM hL₁ hL₂ hv hvb hvl hT P hk (projIcc 0 T hT s)).comp
        ((continuous_projIcc (h := hT)).tendsto s)

end SharpWasserstein.SwitchSourceDerivative
