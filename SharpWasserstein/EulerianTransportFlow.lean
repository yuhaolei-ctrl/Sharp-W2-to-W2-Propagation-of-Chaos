import SharpWasserstein.EulerianTransportEquation
import SharpWasserstein.NarrowFlow

/-! The actual bounded deterministic characteristic flow produces a narrowly
continuous probability law and satisfies the first-order weak equation.
The Lagrangian representation is constructed from the ODE, not assumed. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal ContDiff Interval BoundedContinuousFunction
namespace SharpWasserstein.EulerianTransport
open NoiseAverage
variable {d N : ℕ} {v : ℝ → Configuration d N → Configuration d N} {M K : ℝ≥0}
  (hv : Continuous (Function.uncurry v)) (hb : ∀ t x, ‖v t x‖ ≤ M)
  (hl : ∀ t, LipschitzWith K (v t)) {T : ℝ} (hT : 0 ≤ T)

/-- Endpoint extension makes the genuine finite-horizon trajectory a global
continuous time curve, without claiming an ODE outside the horizon. -/
def solution (x : Configuration d N) (t : ℝ) : Configuration d N :=
  BoundedFlow.flow hv hb hl hT x 0 (projIcc 0 T hT t)

theorem solution_joint_continuous :
    Continuous (fun p : ℝ × Configuration d N => solution hv hb hl hT p.2 p.1) := by
  have hc : Continuous (fun p : ℝ × Configuration d N =>
      ((p.2,(0 : C(Icc 0 T,Configuration d N))),projIcc 0 T hT p.1)) := by fun_prop
  exact (BoundedFlow.flow_joint_continuous hv hb hl hT).comp hc

theorem solution_initial (x : Configuration d N) : solution hv hb hl hT x 0 = x := by
  rw [solution,projIcc_of_mem _ (show (0:ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩)]
  exact (BoundedFlow.flow_trajectory hv hb hl hT x 0).initial hT rfl

theorem solution_hasDerivWithinAt (x : Configuration d N) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (solution hv hb hl hT x)
      (v t (solution hv hb hl hT x t)) (Icc 0 T) t := by
  have hd := (BoundedFlow.flow_trajectory hv hb hl hT x 0).compensated_derivative ht
  simp only [BoundedFlow.noiseExtension,ContinuousMap.zero_apply,sub_zero] at hd
  have he (r : ℝ) (hr : r ∈ Icc 0 T) :
      solution hv hb hl hT x r = BoundedFlow.flow hv hb hl hT x 0 r := by
    simp only [solution,projIcc_of_mem _ hr]
  rw [he t ht]
  exact hd.congr_of_mem he ht

/-- The constructed probability law of the deterministic characteristics. -/
def flowLaw (P : Measure (Configuration d N)) [IsProbabilityMeasure P] (t : ℝ) :
    ProbabilityMeasure (Configuration d N) :=
  randomProbabilityLaw P (fun r x => solution hv hb hl hT x r)
    (fun _ => ((solution_joint_continuous hv hb hl hT).comp
      (continuous_const.prodMk continuous_id)).measurable) t

theorem flowLaw_continuous (P : Measure (Configuration d N)) [IsProbabilityMeasure P] :
    Continuous (flowLaw hv hb hl hT P) := by
  exact randomProbabilityLaw_continuous P (fun r x => solution hv hb hl hT x r)
    (fun _ => ((solution_joint_continuous hv hb hl hT).comp
      (continuous_const.prodMk continuous_id)).measurable)
    (Eventually.of_forall fun _ => (solution_joint_continuous hv hb hl hT).comp
      (continuous_id.prodMk continuous_const))

theorem flowLaw_initial (P : Measure (Configuration d N)) [IsProbabilityMeasure P] :
    (flowLaw hv hb hl hT P 0 : Measure _) = P := by
  change P.map (fun x => solution hv hb hl hT x 0) = P
  simp only [solution_initial]
  exact Measure.map_id

theorem flowLaw_integral (P : Measure (Configuration d N)) [IsProbabilityMeasure P]
    {f : Configuration d N → ℝ} (hf : Continuous f) (t : ℝ) :
    (∫ y, f y ∂(flowLaw hv hb hl hT P t : Measure _)) =
      ∫ x, f (solution hv hb hl hT x t) ∂P :=
  integral_map ((solution_joint_continuous hv hb hl hT).comp
    (continuous_const.prodMk continuous_id)).measurable.aemeasurable hf.aestronglyMeasurable

theorem solution_test_equation {φ : Configuration d N → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (x : Configuration d N) {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) :
    φ (solution hv hb hl hT x t)-φ (solution hv hb hl hT x s) =
      ∫ r in s..t, generator (v r) φ (solution hv hb hl hT x r) := by
  wlog hst : s ≤ t generalizing s t
  · rw [intervalIntegral.integral_symm]
    have he := this ht hs (le_of_not_ge hst)
    linarith
  have hc : Continuous (fun r => solution hv hb hl hT x r) :=
    (solution_joint_continuous hv hb hl hT).comp (continuous_id.prodMk continuous_const)
  have hG : Continuous (fun r => generator (v r) φ (solution hv hb hl hT x r)) :=
    ((hφ.continuous_fderiv (by simp)).comp hc).clm_apply
      (hv.comp (continuous_id.prodMk hc))
  apply (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst
    (hφ.continuous.comp hc).continuousOn _ (hG.intervalIntegrable s t)).symm
  intro r hr
  have hrT : r ∈ Icc 0 T := ⟨hs.1.trans hr.1.le,hr.2.le.trans ht.2⟩
  have hd := (solution_hasDerivWithinAt hv hb hl hT x hrT).hasDerivAt
    (Icc_mem_nhds (hs.1.trans_lt hr.1) (hr.2.trans_le ht.2))
  exact ((hφ.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt r hd

/-- Actual characteristic laws satisfy the weak continuity equation for all
smooth bounded-derivative tests, with every integration justified internally. -/
theorem flowLaw_weakContinuity (P : Measure (Configuration d N)) [IsProbabilityMeasure P] :
    WeakContinuity v (flowLaw hv hb hl hT P) T := by
  refine ⟨flowLaw_continuous hv hb hl hT P, ?_⟩
  intro φ hφ hB s hs t ht
  obtain ⟨C,_,hC⟩ := hB.bounded
  obtain ⟨L,hL⟩ := hB.lipschitz (hφ.differentiable (by simp))
  have hX := solution_joint_continuous hv hb hl hT
  have hG : Continuous (fun p : ℝ × Configuration d N =>
      generator (v p.1) φ (solution hv hb hl hT p.2 p.1)) :=
    ((hφ.continuous_fderiv (by simp)).comp hX).clm_apply
      (hv.comp (continuous_fst.prodMk hX))
  have hGn (r : ℝ) (x : Configuration d N) :
      ‖generator (v r) φ (solution hv hb hl hT x r)‖ ≤ (L:ℝ)*M :=
    generator_norm_le hL (hb r) _
  have hE : Continuous (fun r => ∫ x, generator (v r) φ (solution hv hb hl hT x r) ∂P) := by
    apply continuous_of_dominated (bound := fun _ => (L:ℝ)*M)
    · intro r
      exact (hG.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    · intro r
      exact Eventually.of_forall (hGn r)
    · exact integrable_const _
    · exact Eventually.of_forall fun _ => hG.comp (continuous_id.prodMk continuous_const)
  have he (r : ℝ) :
      (∫ x, generator (v r) φ x ∂(flowLaw hv hb hl hT P r : Measure _)) =
        ∫ x, generator (v r) φ (solution hv hb hl hT x r) ∂P :=
    flowLaw_integral hv hb hl hT P
      ((hφ.continuous_fderiv (by simp)).clm_apply ((hv.comp
        (continuous_const.prodMk continuous_id)))) r
  have hi (r : ℝ) : Integrable (fun x => φ (solution hv hb hl hT x r)) P :=
    Integrable.of_bound (hφ.continuous.comp
      (hX.comp (continuous_const.prodMk continuous_id))).aestronglyMeasurable C
      (Eventually.of_forall fun x => hC _)
  letI : IsFiniteMeasure (volume.restrict (uIoc s t)) := ⟨by simp⟩
  have hj : Integrable (fun p : ℝ × Configuration d N =>
      generator (v p.1) φ (solution hv hb hl hT p.2 p.1))
      ((volume.restrict (uIoc s t)).prod P) :=
    Integrable.of_bound hG.aestronglyMeasurable ((L:ℝ)*M)
      (Eventually.of_forall fun p => hGn p.1 p.2)
  constructor
  · simpa only [he] using hE.intervalIntegrable s t
  · rw [flowLaw_integral hv hb hl hT P hφ.continuous t,
      flowLaw_integral hv hb hl hT P hφ.continuous s,← integral_sub (hi t) (hi s)]
    simp_rw [solution_test_equation hv hb hl hT hφ _ hs ht,he]
    exact (intervalIntegral_integral_swap hj).symm

end SharpWasserstein.EulerianTransport
