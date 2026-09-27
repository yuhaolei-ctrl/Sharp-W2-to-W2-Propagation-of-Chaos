import SharpWasserstein.DriftApproximation
import SharpWasserstein.TransportConvergence

/-! Local uniform drift approximation implies genuine narrow and quadratic
transport convergence of the constructed continuous-noise flows. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace SharpWasserstein.BoundedFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {T : ℝ} [MeasurableSpace C(Icc 0 T,E)] [BorelSpace C(Icc 0 T,E)]
  {u : ℕ → ℝ → E → E} {v : ℝ → E → E} {M K : ℝ≥0}
  (huc : ∀ n, Continuous (Function.uncurry (u n))) (hub : ∀ n t x, ‖u n t x‖ ≤ M)
  (hul : ∀ n t, LipschitzWith K (u n t))
  (hvc : Continuous (Function.uncurry v)) (hvb : ∀ t x, ‖v t x‖ ≤ M)
  (hvl : ∀ t, LipschitzWith K (v t)) (hT : 0 ≤ T)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace C(Icc 0 T,E)] [BorelSpace C(Icc 0 T,E)] in
theorem flow_drift_tendsto
    (hd : TendstoLocallyUniformly (fun n => Function.uncurry (u n)) (Function.uncurry v) atTop)
    (x : E) (w : C(Icc 0 T,E)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Tendsto (fun n => flow (huc n) (hub n) (hul n) hT x w t) atTop
      (𝓝 (flow hvc hvb hvl hT x w t)) :=
  finiteTrajectory_tendsto_of_locallyUniform_drift hul
    (noiseExtension_continuous hT w).continuousOn
    (fun n => flow_trajectory (huc n) (hub n) (hul n) hT x w)
    (flow_trajectory hvc hvb hvl hT x w) hd ht

theorem flow_driftLaw_tendsto
    (hd : TendstoLocallyUniformly (fun n => Function.uncurry (u n)) (Function.uncurry v) atTop)
    (P : ProbabilityMeasure (E × C(Icc 0 T,E))) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Tendsto (fun n => P.map (flow_continuous (huc n) (hub n) (hul n) hT ht).measurable.aemeasurable)
      atTop (𝓝 (P.map (flow_continuous hvc hvb hvl hT ht).measurable.aemeasurable)) := by
  apply probabilityMeasure_map_tendsto P
    (fun n => (flow_continuous (huc n) (hub n) (hul n) hT ht).measurable)
    (flow_continuous hvc hvb hvl hT ht).measurable
  exact Eventually.of_forall (fun p => flow_drift_tendsto huc hub hul hvc hvb hvl hT hd p.1 p.2 ht)

theorem flow_drift_error_integrable (P : ProbabilityMeasure (E × C(Icc 0 T,E)))
    {t : ℝ} (ht : t ∈ Icc 0 T) (n : ℕ) :
    Integrable (fun p => ‖flow (huc n) (hub n) (hul n) hT p.1 p.2 t -
      flow hvc hvb hvl hT p.1 p.2 t‖^2) (P : Measure (E × C(Icc 0 T,E))) := by
  have ht0 := ht.1
  apply Integrable.mono' (integrable_const ((2*(M : ℝ)*t)^2))
  · exact (((flow_continuous (huc n) (hub n) (hul n) hT ht).measurable.sub
      (flow_continuous hvc hvb hvl hT ht).measurable).norm.pow_const 2).aestronglyMeasurable
  · apply Eventually.of_forall
    intro p
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
      ((flow_trajectory (huc n) (hub n) (hul n) hT p.1 p.2).sameInput_difference_bound
        (fun s _ x => hub n s x) (fun s _ x => hvb s x)
        (flow_trajectory hvc hvb hvl hT p.1 p.2) ht)

theorem flow_drift_meanSquare_tendsto
    (hd : TendstoLocallyUniformly (fun n => Function.uncurry (u n)) (Function.uncurry v) atTop)
    (P : ProbabilityMeasure (E × C(Icc 0 T,E))) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Tendsto (fun n => ∫ p : E × C(Icc 0 T,E), ‖flow (huc n) (hub n) (hul n) hT p.1 p.2 t -
      flow hvc hvb hvl hT p.1 p.2 t‖^2 ∂(P : Measure (E × C(Icc 0 T,E)))) atTop (𝓝 0) := by
  have ht0 := ht.1
  have h := tendsto_integral_of_dominated_convergence
    (μ := (P : Measure (E × C(Icc 0 T,E))))
    (F := fun n p => ‖flow (huc n) (hub n) (hul n) hT p.1 p.2 t -
      flow hvc hvb hvl hT p.1 p.2 t‖^2) (f := fun _ => (0 : ℝ))
    (fun _ => (2*(M : ℝ)*t)^2)
    (fun n => (flow_drift_error_integrable huc hub hul hvc hvb hvl hT P ht n).aestronglyMeasurable)
    (integrable_const _) ?_ ?_
  · simpa only [integral_zero] using h
  · intro n
    apply Eventually.of_forall
    intro p
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
      ((flow_trajectory (huc n) (hub n) (hul n) hT p.1 p.2).sameInput_difference_bound
        (fun s _ x => hub n s x) (fun s _ x => hvb s x)
        (flow_trajectory hvc hvb hvl hT p.1 p.2) ht)
  · apply Eventually.of_forall
    intro p
    have he := flow_drift_tendsto huc hub hul hvc hvb hvl hT hd p.1 p.2 ht
    simpa only [sub_self,norm_zero,zero_pow (by decide : 2 ≠ 0)] using
      ((he.sub_const (flow hvc hvb hvl hT p.1 p.2 t)).norm.pow 2)

end SharpWasserstein.BoundedFlow

namespace SharpWasserstein.BoundedFlow

set_option maxHeartbeats 800000 in
theorem flow_drift_wassersteinSq_tendsto {d N : ℕ} {T : ℝ}
    [MeasurableSpace C(Icc 0 T,Configuration d N)] [BorelSpace C(Icc 0 T,Configuration d N)]
    {u : ℕ → ℝ → Configuration d N → Configuration d N}
    {v : ℝ → Configuration d N → Configuration d N} {M K : ℝ≥0}
    (huc : ∀ n, Continuous (Function.uncurry (u n))) (hub : ∀ n t x, ‖u n t x‖ ≤ M)
    (hul : ∀ n t, LipschitzWith K (u n t))
    (hvc : Continuous (Function.uncurry v)) (hvb : ∀ t x, ‖v t x‖ ≤ M)
    (hvl : ∀ t, LipschitzWith K (v t)) (hT : 0 ≤ T)
    (hd : TendstoLocallyUniformly (fun n => Function.uncurry (u n)) (Function.uncurry v) atTop)
    (P : ProbabilityMeasure (Configuration d N × C(Icc 0 T,Configuration d N)))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    Tendsto (fun n => wassersteinSq
      (Measure.map (fun p : Configuration d N × C(Icc 0 T,Configuration d N) =>
        flow (huc n) (hub n) (hul n) hT p.1 p.2 t) (P : Measure _))
      (Measure.map (fun p : Configuration d N × C(Icc 0 T,Configuration d N) =>
        flow hvc hvb hvl hT p.1 p.2 t) (P : Measure _))) atTop (𝓝 0) := by
  apply wassersteinSq_tendsto_zero_of_meanSquare
    (Ω := Configuration d N × C(Icc 0 T,Configuration d N))
    (d := d) (N := N) (P : Measure (Configuration d N × C(Icc 0 T,Configuration d N)))
    (F := fun (n : ℕ) (p : Configuration d N × C(Icc 0 T,Configuration d N)) =>
      flow (v := u n) (M := M) (K := K) (huc n) (hub n) (hul n) hT p.1 p.2 t)
    (G := fun p : Configuration d N × C(Icc 0 T,Configuration d N) =>
      flow (v := v) (M := M) (K := K) hvc hvb hvl hT p.1 p.2 t)
  · exact fun n => (flow_continuous (huc n) (hub n) (hul n) hT ht).measurable
  · exact (flow_continuous hvc hvb hvl hT ht).measurable
  · exact flow_drift_error_integrable huc hub hul hvc hvb hvl hT P ht
  · exact flow_drift_meanSquare_tendsto huc hub hul hvc hvb hvl hT hd P ht

end SharpWasserstein.BoundedFlow
