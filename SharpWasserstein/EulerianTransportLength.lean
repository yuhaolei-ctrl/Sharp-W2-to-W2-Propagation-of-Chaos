module

public import SharpWasserstein.Compat
public import SharpWasserstein.EulerianTransportFlow
public import SharpWasserstein.EulerianTransportUniqueness
public import SharpWasserstein.EulerianTransportL2

@[expose] public section

/-! A genuine Eulerian-to-Wasserstein bridge for bounded smooth spatially
Lipschitz velocities. The weak equation determines the constructed characteristic
law; actual moments and mixed `L¹(L²)` integrability are proved before using the
pointwise transport theorem. The result is for regular velocities, not a
rough finite-action superposition principle. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal Interval ContDiff
namespace SharpWasserstein.EulerianTransport
open NoiseAverage
variable {d N : ℕ} {v : ℝ → Configuration d N → Configuration d N} {M K : ℝ≥0}
  (hv : Continuous (Function.uncurry v)) (hb : ∀ t x, ‖v t x‖ ≤ M)
  (hl : ∀ t, LipschitzWith K (v t)) {T : ℝ} (hT : 0 ≤ T)

/-- Bounded drift gives a global label-moment bound for the endpoint-extended characteristics. -/
theorem solution_norm_le (x : Configuration d N) (t : ℝ) :
    ‖solution hv hb hl hT x t‖ ≤ ‖x‖+(M:ℝ)*T := by
  have hh := (BoundedFlow.flow_trajectory hv hb hl hT x 0).norm_le
    (fun s _ y => hb s y) (projIcc 0 T hT t).property
  simp only [BoundedFlow.noiseExtension, ContinuousMap.zero_apply, norm_zero, add_zero] at hh
  exact hh.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (projIcc 0 T hT t).property.2 M.coe_nonneg))

theorem solution_memLp (P : Measure (Configuration d N)) [IsProbabilityMeasure P]
    (hP : HasSecondMoment P) (t : ℝ) : MemLp (fun x => solution hv hb hl hT x t) 2 P := by
  have hx : MemLp (fun x : Configuration d N => x) 2 P := by
    apply memLp_of_hasSecondMoment_map measurable_id
    simpa only [Measure.map_id] using hP
  apply (hx.norm.add (memLp_const ((M:ℝ)*T))).mono'
    ((solution_joint_continuous hv hb hl hT).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  exact Eventually.of_forall (fun x => solution_norm_le hv hb hl hT x t)

theorem flowLaw_secondMoment (P : Measure (Configuration d N)) [IsProbabilityMeasure P]
    (hP : HasSecondMoment P) (t : ℝ) : HasSecondMoment (flowLaw hv hb hl hT P t : Measure (Configuration d N)) := by
  exact hasSecondMoment_map_of_memLp
    ((solution_joint_continuous hv hb hl hT).comp
      (continuous_const.prodMk continuous_id)).measurable (solution_memLp hv hb hl hT P hP t)

/-- The actual Euclidean velocity along a constructed characteristic. -/
def velocity (t : ℝ) (x : Configuration d N) : EuclideanSpace ℝ (Fin N × Fin d) :=
  euclideanMap (v t (solution hv hb hl hT x t))

theorem velocity_joint_continuous : Continuous (Function.uncurry (velocity hv hb hl hT)) :=
  euclideanMap.continuous.comp (hv.comp (continuous_fst.prodMk (solution_joint_continuous hv hb hl hT)))

theorem velocity_norm_le (t : ℝ) (x : Configuration d N) :
    ‖velocity hv hb hl hT t x‖ ≤ ‖(euclideanMap (d := d) (N := N))‖*(M:ℝ) :=
  (euclideanMap.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hb t _) (norm_nonneg _))

theorem velocity_memLp (P : Measure (Configuration d N)) [IsProbabilityMeasure P] (t : ℝ) :
    MemLp (velocity hv hb hl hT t) 2 P :=
  MemLp.of_bound ((velocity_joint_continuous hv hb hl hT).comp
    (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (‖(euclideanMap (d := d) (N := N))‖*(M:ℝ))
    (Eventually.of_forall (velocity_norm_le hv hb hl hT t))

/-- The exact action is the `L²` norm of the actual transported velocity. -/
theorem velocity_norm_eq_action (P : Measure (Configuration d N)) [IsProbabilityMeasure P] (t : ℝ) :
    ‖(velocity_memLp hv hb hl hT P t).toLp (velocity hv hb hl hT t)‖ =
      Real.sqrt (∫ x, productCost (v t x) 0 ∂(flowLaw hv hb hl hT P t : Measure (Configuration d N))) := by
  rw [PointwiseTrajectory.norm_toLp_two_eq_sqrt]
  congr 1
  have hc : Continuous (fun x => productCost (v t x) 0) := by
    have hvt : Continuous (v t) := hv.comp (continuous_const.prodMk continuous_id)
    unfold productCost
    fun_prop
  rw [flowLaw_integral hv hb hl hT P hc]
  apply integral_congr_ae
  filter_upwards [] with x
  exact euclideanMap_norm_sq _

/-- The constructed characteristic law satisfies the actual squared Wasserstein
length bound, with the true unnormalized Euclidean action. -/
theorem flowLaw_wassersteinSq_le_action (P : Measure (Configuration d N)) [IsProbabilityMeasure P]
    (hP : HasSecondMoment P) {a b : ℝ} (ha : a ∈ Icc 0 T) (hbT : b ∈ Icc 0 T) (hab : a ≤ b) :
    wassersteinSq (flowLaw hv hb hl hT P a : Measure (Configuration d N)) (flowLaw hv hb hl hT P b : Measure (Configuration d N)) ≤
      ENNReal.ofReal ((∫ t in a..b,
        Real.sqrt (∫ x, productCost (v t x) 0 ∂(flowLaw hv hb hl hT P t : Measure (Configuration d N)))) ^ 2) := by
  have hZ₂ (t : ℝ) : MemLp (fun x => configurationToEuclidean (solution hv hb hl hT x t)) 2 P :=
    euclideanMap.comp_memLp' (solution_memLp hv hb hl hT P hP t)
  have hV := intervalIntegrable_toLp_of_uniform_bound (velocity hv hb hl hT)
    (velocity_memLp hv hb hl hT P) (C := ‖(euclideanMap (d := d) (N := N))‖*(M:ℝ))
    (by positivity) (fun t => Eventually.of_forall (velocity_norm_le hv hb hl hT t))
    (Eventually.of_forall fun x => (velocity_joint_continuous hv hb hl hT).comp
      (continuous_id.prodMk continuous_const)) a b
  have hlen := wassersteinSq_of_pointwise_derivative P
    (fun t x => solution hv hb hl hT x t) hZ₂ (velocity hv hb hl hT)
    (velocity_joint_continuous hv hb hl hT).stronglyMeasurable
    (velocity_memLp hv hb hl hT P) hab hV
    (Eventually.of_forall fun x => (euclideanMap.continuous.comp
      ((solution_joint_continuous hv hb hl hT).comp (continuous_id.prodMk continuous_const))).continuousOn) ?_
  · simpa only [velocity_norm_eq_action, flowLaw, randomProbabilityLaw, ProbabilityMeasure.coe_mk] using hlen
  · filter_upwards [] with x
    intro t ht
    have htT : t ∈ Icc 0 T := ⟨ha.1.trans ht.1.le, ht.2.le.trans hbT.2⟩
    have hder := (solution_hasDerivWithinAt hv hb hl hT x htT).hasDerivAt
      (Icc_mem_nhds (ha.1.trans_lt ht.1) (ht.2.trans_le hbT.2))
    exact euclideanMap.hasFDerivAt.comp_hasDerivAt t hder

/-- Uniqueness of the weak equation proves the actual characteristic pushforward representation. -/
theorem WeakContinuity.eq_flowLaw {μ : ℝ → ProbabilityMeasure (Configuration d N)}
    (hμ : WeakContinuity v μ T) {K₁ : ℝ≥0}
    (hvs : ∀ t, ContDiff ℝ ∞ (v t)) (hvB : ∀ t, AllDerivativesBounded (v t))
    (hv₁ : ∀ t, LipschitzWith K₁ (fderiv ℝ (v t))) {t : ℝ} (ht : t ∈ Icc 0 T) :
    μ t = flowLaw hv hb hl hT (μ 0 : Measure (Configuration d N)) t := by
  apply hμ.eq_of_same_initial (flowLaw_weakContinuity hv hb hl hT (μ 0 : Measure (Configuration d N)))
    hv hvs hvB hl hv₁ hb _ ht
  apply ProbabilityMeasure.toMeasure_injective
  exact (flowLaw_initial hv hb hl hT (μ 0 : Measure (Configuration d N))).symm

include hv hb hl hT in
/-- The genuine regular Eulerian continuity equation implies a squared W₂ length
bound. No law=pushforward or Wasserstein speed statement occurs among the hypotheses. -/
theorem WeakContinuity.wassersteinSq_le_action {μ : ℝ → ProbabilityMeasure (Configuration d N)}
    (hμ : WeakContinuity v μ T) {K₁ : ℝ≥0}
    (hvs : ∀ t, ContDiff ℝ ∞ (v t)) (hvB : ∀ t, AllDerivativesBounded (v t))
    (hv₁ : ∀ t, LipschitzWith K₁ (fderiv ℝ (v t))) (hP : HasSecondMoment (μ 0 : Measure (Configuration d N)))
    {a b : ℝ} (ha : a ∈ Icc 0 T) (hbT : b ∈ Icc 0 T) (hab : a ≤ b) :
    wassersteinSq (μ a : Measure (Configuration d N)) (μ b : Measure (Configuration d N)) ≤
      ENNReal.ofReal ((∫ t in a..b, Real.sqrt (∫ x, productCost (v t x) 0 ∂(μ t : Measure (Configuration d N)))) ^ 2) := by
  have he (t : ℝ) (ht : t ∈ Icc 0 T) : flowLaw hv hb hl hT (μ 0 : Measure (Configuration d N)) t = μ t :=
    (hμ.eq_flowLaw hv hb hl hT hvs hvB hv₁ ht).symm
  have hh := flowLaw_wassersteinSq_le_action hv hb hl hT (μ 0 : Measure (Configuration d N)) hP ha hbT hab
  rw [he a ha, he b hbT] at hh
  have hi : (∫ t in a..b, Real.sqrt (∫ x, productCost (v t x) 0
        ∂(flowLaw hv hb hl hT (μ 0 : Measure (Configuration d N)) t : Measure (Configuration d N)))) =
      ∫ t in a..b, Real.sqrt (∫ x, productCost (v t x) 0 ∂(μ t : Measure (Configuration d N))) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hab] at ht
    dsimp only
    rw [he t ⟨ha.1.trans ht.1, ht.2.trans hbT.2⟩]
  rwa [hi] at hh

include hv hb hl hT in
/-- The corresponding real W₂ length bound, derived alongside the finite extended-valued cost bound. -/
theorem WeakContinuity.wasserstein_length_le_action {μ : ℝ → ProbabilityMeasure (Configuration d N)}
    (hμ : WeakContinuity v μ T) {K₁ : ℝ≥0}
    (hvs : ∀ t, ContDiff ℝ ∞ (v t)) (hvB : ∀ t, AllDerivativesBounded (v t))
    (hv₁ : ∀ t, LipschitzWith K₁ (fderiv ℝ (v t))) (hP : HasSecondMoment (μ 0 : Measure (Configuration d N)))
    {a b : ℝ} (ha : a ∈ Icc 0 T) (hbT : b ∈ Icc 0 T) (hab : a ≤ b) :
    Real.sqrt (wassersteinSq (μ a : Measure (Configuration d N)) (μ b : Measure (Configuration d N))).toReal ≤
      ∫ t in a..b, Real.sqrt (∫ x, productCost (v t x) 0 ∂(μ t : Measure (Configuration d N))) := by
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (hμ.wassersteinSq_le_action hv hb hl hT hvs hvB hv₁ hP ha hbT hab)
  rw [ENNReal.toReal_ofReal (sq_nonneg _)] at hh
  have hn : 0 ≤ ∫ t in a..b, Real.sqrt (∫ x, productCost (v t x) 0 ∂(μ t : Measure (Configuration d N))) :=
    intervalIntegral.integral_nonneg hab (fun _ _ => Real.sqrt_nonneg _)
  simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg hn] using Real.sqrt_le_sqrt hh

end SharpWasserstein.EulerianTransport
