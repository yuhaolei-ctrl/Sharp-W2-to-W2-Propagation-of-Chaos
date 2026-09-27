import SharpWasserstein.EulerLaw
import SharpWasserstein.TransportConvergence

/-! The Euler approximation converges in the actual unnormalized quadratic
transport cost. The proof constructs the common-input coupling. -/

noncomputable section
open Set MeasureTheory Filter
open scoped NNReal

namespace SharpWasserstein.Euler

set_option maxHeartbeats 800000 in
theorem endpoint_wassersteinSq_tendsto {d N : ℕ} {T : ℝ}
    [MeasurableSpace C(Icc 0 T, Configuration d N)]
    [BorelSpace C(Icc 0 T, Configuration d N)]
    {v : ℝ → Configuration d N → Configuration d N} {M K : ℝ≥0}
    (hv : Continuous (Function.uncurry v)) (hb : ∀ t x, ‖v t x‖ ≤ M)
    (hl : ∀ t, LipschitzWith K (v t)) (hT : 0 < T)
    (P : ProbabilityMeasure (Configuration d N × C(Icc 0 T, Configuration d N))) :
    Tendsto (fun n => wassersteinSq (Measure.map (endpointMap hT.le v n) P)
      (Measure.map (fun p : Configuration d N × C(Icc 0 T, Configuration d N) =>
        BoundedFlow.flow hv hb hl hT.le p.1 p.2 T) P)) atTop (nhds 0) := by
  apply wassersteinSq_tendsto_zero_of_meanSquare
    (d := d) (N := N) (P : Measure (Configuration d N × C(Icc 0 T, Configuration d N)))
    (F := fun n => endpointMap hT.le v n)
    (G := fun p => BoundedFlow.flow hv hb hl hT.le p.1 p.2 T)
  · exact fun n => endpointMap_measurable hT.le (fun t => (hl t).continuous.measurable) n
  · exact (BoundedFlow.flow_continuous hv hb hl hT.le ⟨hT.le,le_rfl⟩).measurable
  · exact endpoint_meanSquare_integrable hv hb hl hT.le P
  · exact endpoint_meanSquare_tendsto hv hb hl hT P

end SharpWasserstein.Euler
