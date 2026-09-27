import SharpWasserstein.EulerConvergence
import SharpWasserstein.NarrowFlow

/-! Measurable Euler laws and their genuine narrow convergence to the
constructed continuous-forcing solution law. -/

noncomputable section
open Set MeasureTheory Filter
open scoped NNReal

namespace SharpWasserstein

theorem probabilityMeasure_map_tendsto {Ω E : Type*} [MeasurableSpace Ω]
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    (P : ProbabilityMeasure Ω) {F : ℕ → Ω → E} {f : Ω → E}
    (hF : ∀ n, Measurable (F n)) (hf : Measurable f)
    (hlim : ∀ᵐ ω ∂(P : Measure Ω), Tendsto (fun n => F n ω) atTop (nhds (f ω))) :
    Tendsto (fun n => P.map (hF n).aemeasurable) atTop (nhds (P.map hf.aemeasurable)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro φ
  have hleft : (fun n => ∫ x, φ x ∂(P.map (hF n).aemeasurable)) =
      (fun n => ∫ ω, φ (F n ω) ∂P) := by
    funext n
    exact integral_map (hF n).aemeasurable φ.continuous.measurable.aestronglyMeasurable
  have hright : (∫ x, φ x ∂(P.map hf.aemeasurable)) = ∫ ω, φ (f ω) ∂P :=
    integral_map hf.aemeasurable φ.continuous.measurable.aestronglyMeasurable
  rw [hleft, hright]
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖φ‖)
  · intro n
    exact (φ.continuous.measurable.comp (hF n)).aestronglyMeasurable
  · exact integrable_const ‖φ‖
  · intro n
    exact Eventually.of_forall fun ω => φ.norm_coe_le_norm (F n ω)
  · filter_upwards [hlim] with ω hω
    exact φ.continuous.continuousAt.tendsto.comp hω

namespace Euler

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem nodes_measurable {Ω : Type*} [MeasurableSpace Ω]
    {v : ℝ → E → E} (hv : ∀ t, Measurable (v t))
    {x : Ω → E} (hx : Measurable x) {w : ℝ → Ω → E} (hw : ∀ t, Measurable (w t))
    (δ : ℝ) (n : ℕ) : Measurable (fun ω => nodes v (x ω) (fun t => w t ω) δ n) := by
  induction n with
  | zero => exact hx.add (hw 0)
  | succ n ih =>
    exact (ih.add (((hv _).comp ih).const_smul δ)).add ((hw _).sub (hw _))

def endpointMap {T : ℝ} (hT : 0 ≤ T) (v : ℝ → E → E) (n : ℕ)
    (p : E × C(Icc 0 T, E)) : E :=
  nodes v p.1 (BoundedFlow.noiseExtension hT p.2) (T / (n+1)) (n+1)

variable {T : ℝ} [MeasurableSpace C(Icc 0 T, E)] [BorelSpace C(Icc 0 T, E)]

theorem endpointMap_measurable (hT : 0 ≤ T) {v : ℝ → E → E}
    (hv : ∀ t, Measurable (v t)) (n : ℕ) : Measurable (endpointMap hT v n) := by
  apply nodes_measurable hv measurable_fst
  intro t
  exact (continuous_eval_const (projIcc 0 T hT t)).measurable.comp measurable_snd

/-- Narrow convergence holds for every probability distribution of initial
points and continuous forcing paths, hence for the actual Brownian input. -/
theorem endpointLaw_tendsto [CompleteSpace E]
    {v : ℝ → E → E} {M K : ℝ≥0}
    (hv : Continuous (Function.uncurry v)) (hb : ∀ t x, ‖v t x‖ ≤ M)
    (hl : ∀ t, LipschitzWith K (v t)) (hT : 0 < T)
    (P : ProbabilityMeasure (E × C(Icc 0 T, E))) :
    Tendsto (fun n => P.map (endpointMap_measurable hT.le
      (fun t => (hl t).continuous.measurable) n).aemeasurable) atTop
      (nhds (P.map (BoundedFlow.flow_continuous hv hb hl hT.le ⟨hT.le,le_rfl⟩).measurable.aemeasurable)) := by
  apply probabilityMeasure_map_tendsto P
    (fun n => endpointMap_measurable hT.le (fun t => (hl t).continuous.measurable) n)
    (BoundedFlow.flow_continuous hv hb hl hT.le ⟨hT.le,le_rfl⟩).measurable
  exact Eventually.of_forall fun p : E × C(Icc 0 T, E) => trajectory_endpoint_tendsto
    (BoundedFlow.flow_trajectory hv hb hl hT.le p.1 p.2) hl hT

/-- Mean-square endpoint convergence uses deterministic bounded-drift
domination; no supremum moment assumption on the noise is imposed. -/
theorem endpoint_meanSquare_tendsto [CompleteSpace E]
    {v : ℝ → E → E} {M K : ℝ≥0}
    (hv : Continuous (Function.uncurry v)) (hb : ∀ t x, ‖v t x‖ ≤ M)
    (hl : ∀ t, LipschitzWith K (v t)) (hT : 0 < T)
    (P : ProbabilityMeasure (E × C(Icc 0 T, E))) :
    Tendsto (fun n => ∫ p, ‖endpointMap hT.le v n p -
      BoundedFlow.flow hv hb hl hT.le p.1 p.2 T‖ ^ 2 ∂P) atTop (nhds 0) := by
  have hmeas (n : ℕ) : Measurable (fun p : E × C(Icc 0 T,E) =>
      ‖endpointMap hT.le v n p - BoundedFlow.flow hv hb hl hT.le p.1 p.2 T‖ ^ 2) :=
    ((endpointMap_measurable hT.le (fun t => (hl t).continuous.measurable) n).sub
      (BoundedFlow.flow_continuous hv hb hl hT.le ⟨hT.le,le_rfl⟩).measurable).norm.pow_const 2
  have hd := tendsto_integral_of_dominated_convergence
    (μ := (P : Measure (E × C(Icc 0 T,E))))
    (F := fun n p => ‖endpointMap hT.le v n p - BoundedFlow.flow hv hb hl hT.le p.1 p.2 T‖ ^ 2)
    (f := fun _ => (0 : ℝ)) (fun _ => (2 * (M : ℝ) * T)^2)
    (fun n => (hmeas n).aestronglyMeasurable) (integrable_const _) ?_ ?_
  · simpa using hd
  · intro n
    apply Eventually.of_forall
    intro p
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
      (trajectory_endpoint_error_bound (BoundedFlow.flow_trajectory hv hb hl hT.le p.1 p.2)
        hb hT.le n)
  · apply Eventually.of_forall
    intro p
    have h := trajectory_endpoint_tendsto
      (BoundedFlow.flow_trajectory hv hb hl hT.le p.1 p.2) hl hT
    simpa only [endpointMap, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] using
      ((h.sub_const (BoundedFlow.flow hv hb hl hT.le p.1 p.2 T)).norm.pow 2)

theorem endpoint_meanSquare_integrable [CompleteSpace E]
    {v : ℝ → E → E} {M K : ℝ≥0}
    (hv : Continuous (Function.uncurry v)) (hb : ∀ t x, ‖v t x‖ ≤ M)
    (hl : ∀ t, LipschitzWith K (v t)) (hT : 0 ≤ T)
    (P : ProbabilityMeasure (E × C(Icc 0 T, E))) (n : ℕ) :
    Integrable (fun p => ‖endpointMap hT v n p - BoundedFlow.flow hv hb hl hT p.1 p.2 T‖^2)
      (P : Measure (E × C(Icc 0 T,E))) := by
  apply Integrable.mono' (integrable_const ((2*(M : ℝ)*T)^2))
  · exact (((endpointMap_measurable hT (fun t => (hl t).continuous.measurable) n).sub
      (BoundedFlow.flow_continuous hv hb hl hT ⟨hT,le_rfl⟩).measurable).norm.pow_const 2).aestronglyMeasurable
  · apply Eventually.of_forall
    intro p
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
      (trajectory_endpoint_error_bound (BoundedFlow.flow_trajectory hv hb hl hT p.1 p.2) hb hT n)

end Euler
end SharpWasserstein
