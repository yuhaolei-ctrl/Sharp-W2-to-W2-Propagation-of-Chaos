module

public import SharpWasserstein.Compat
public import SharpWasserstein.RoughEulerianTransportContinuity
public import SharpWasserstein.SmoothCutoff

@[expose] public section

/-! Compact spatial tests extend to bounded smooth tests with bounded gradient
for the actual finite-energy space-time flux. No boundedness or regularity of
the flux is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped InnerProductSpace Topology ENNReal ProbabilityTheory Interval ContDiff
namespace SharpWasserstein.RoughEulerianCompression
open WeightedTangent RoughEulerianTransport
variable {d : ℕ} [MeasurableSpace (Point d)] [BorelSpace (Point d)]
  {μ : ℝ → ProbabilityMeasure (Point d)} {σ : ℝ → Test d →ₗ[ℝ] ℝ} {T : ℝ}
  (h : CompactDistributionContinuity μ σ T)

instance curveSpaceTimeMeasure_finite : IsFiniteMeasure (curveSpaceTimeMeasure h) := by
  unfold curveSpaceTimeMeasure
  infer_instance

/-- Bounded continuous gradient pairs integrably with the genuine rough joint L² flux. -/
theorem bounded_gradient_joint_integrable {F : Point d → ℝ}
    (hF : ContDiff ℝ ∞ F) {B : ℝ} (hB : ∀ x,‖gradient F x‖ ≤ B) :
    Integrable (fun z : ℝ × Point d => ⟪gradient F z.2,curveFlux h z⟫_ℝ)
      (curveSpaceTimeMeasure h) := by
  have hc : Continuous (gradient F) := (InnerProductSpace.toDual ℝ (Point d)).symm.continuous.comp
    (hF.continuous_fderiv (by simp))
  have hU := (Lp.memLp (curveFlux h)).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  apply (hU.norm.const_mul B).mono'
    ((hc.measurable.comp measurable_snd).aestronglyMeasurable.inner (Lp.aestronglyMeasurable _))
  exact Eventually.of_forall fun z => (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (hB z.2) (norm_nonneg _))

/-- Genuine time integrability of a bounded-gradient test against the joint flux. -/
theorem bounded_gradient_time_integrable {F : Point d → ℝ}
    (hF : ContDiff ℝ ∞ F) {B : ℝ} (hB : ∀ x,‖gradient F x‖ ≤ B) :
    IntegrableOn (fun t => ∫ x,⟪gradient F x,curveFlux h (t,x)⟫_ℝ
      ∂(μ t : Measure (Point d))) (Icc 0 T) := by
  have hi := bounded_gradient_joint_integrable h hF hB
  have hj := hi.integral_compProd
  convert hj using 1
  rfl

/-- The literal space-time integral equals the desired time integral on every subinterval. -/
theorem joint_pairing_eq_interval {F : Point d → ℝ}
    (hF : ContDiff ℝ ∞ F) {B : ℝ} (hB : ∀ x,‖gradient F x‖ ≤ B)
    {a b : ℝ} (ha : a ∈ Icc 0 T) (hb : b ∈ Icc 0 T) (hab : a ≤ b) :
    (∫ z in Ioc a b ×ˢ univ,⟪gradient F z.2,curveFlux h z⟫_ℝ ∂curveSpaceTimeMeasure h) =
      ∫ t in a..b,∫ x,⟪gradient F x,curveFlux h (t,x)⟫_ℝ ∂(μ t : Measure (Point d)) := by
  have hsub : Ioc a b ⊆ Icc 0 T := fun t ht => ⟨ha.1.trans ht.1.le,ht.2.trans hb.2⟩
  rw [intervalIntegral.integral_of_le hab]
  have he := Measure.setIntegral_compProd (μ := volume.restrict (Icc 0 T))
    (κ := probabilityCurveKernel μ h.continuous) (s := Ioc a b) measurableSet_Ioc MeasurableSet.univ
    (bounded_gradient_joint_integrable h hF hB).integrableOn
  simpa only [Measure.restrict_univ,Measure.restrict_restrict_of_subset hsub,
    curveSpaceTimeMeasure,probabilityCurveKernel_apply] using he

/-- The actual distributional weak equation extends from compact tests to all
bounded smooth functions with bounded Euclidean gradient. -/
theorem bounded_smooth_continuity_equation (hT : 0 ≤ T) {E : ℝ → ℝ}
    (hE : IntegrableOn E (Icc 0 T))
    (hbound : ∀ᵐ t ∂volume.restrict (Icc 0 T), ∀ φ : Test d,
      testObjective (μ t : Measure (Point d)) (σ t) φ ≤ E t)
    {F : Point d → ℝ} (hF : ContDiff ℝ ∞ F)
    {A B : ℝ} (hA : ∀ x,|F x| ≤ A) (hB : ∀ x,‖gradient F x‖ ≤ B)
    {a b : ℝ} (ha : a ∈ Icc 0 T) (hb : b ∈ Icc 0 T) (hab : a ≤ b) :
    IntervalIntegrable (fun t => ∫ x,⟪gradient F x,curveFlux h (t,x)⟫_ℝ
      ∂(μ t : Measure (Point d))) volume a b ∧
    (∫ x,F x ∂(μ b : Measure (Point d)))-(∫ x,F x ∂(μ a : Measure (Point d))) =
      ∫ t in a..b,∫ x,⟪gradient F x,curveFlux h (t,x)⟫_ℝ ∂(μ t : Measure (Point d)) := by
  have hA₀ : 0 ≤ A := (abs_nonneg (F 0)).trans (hA 0)
  have hB₀ : 0 ≤ B := (norm_nonneg (gradient F 0)).trans (hB 0)
  let ψ : ℕ → Test d := SmoothCutoff.approximate F hF
  let C : ℝ := B+A*(SmoothCutoff.baseLipschitzConstant d:ℝ)
  have hψC (j : ℕ) (x : Point d) : ‖gradient (ψ j : Point d → ℝ) x‖ ≤ C :=
    SmoothCutoff.approximate_gradient_bound F hF hA₀ hA hB j x
  have hψA (j : ℕ) (x : Point d) : |(ψ j : Point d → ℝ) x| ≤ A := by
    change |SmoothCutoff.cutoff d j x*F x| ≤ A
    rw [abs_mul]
    exact (mul_le_mul (SmoothCutoff.cutoff_abs_le_one d j x) (hA x) (abs_nonneg _) (by norm_num)).trans_eq (one_mul A)
  have hval (t : ℝ) : Tendsto (fun j => ∫ x,(ψ j : Point d → ℝ) x ∂(μ t : Measure (Point d)))
      atTop (𝓝 (∫ x,F x ∂(μ t : Measure (Point d)))) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => A)
      (fun j => (ψ j).property.1.continuous.aestronglyMeasurable) (integrable_const _) ?_ ?_
    · intro j
      exact Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hψA j x
    · filter_upwards [] with x
      apply tendsto_const_nhds.congr'
      filter_upwards [SmoothCutoff.cutoff_eventuallyEq_one x] with j hj
      change F x = SmoothCutoff.cutoff d j x*F x
      rw [hj.eq_of_nhds,one_mul]
  let ρ := (curveSpaceTimeMeasure h).restrict (Ioc a b ×ˢ univ)
  have hdom : Integrable (fun z => C*‖curveFlux h z‖) ρ :=
    (((Lp.memLp (curveFlux h)).integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)).norm.const_mul C).integrableOn
  have hlim : Tendsto (fun j => ∫ z,⟪gradient (ψ j : Point d → ℝ) z.2,curveFlux h z⟫_ℝ ∂ρ)
      atTop (𝓝 (∫ z,⟪gradient F z.2,curveFlux h z⟫_ℝ ∂ρ)) := by
    apply tendsto_integral_of_dominated_convergence (fun z => C*‖curveFlux h z‖) ?_ hdom ?_ ?_
    · intro j
      exact ((continuous_test_gradient (ψ j)).measurable.comp measurable_snd).aestronglyMeasurable.inner
        ((Lp.stronglyMeasurable (curveFlux h)).aestronglyMeasurable)
    · intro j
      exact Eventually.of_forall fun z => (norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (hψC j z.2) (norm_nonneg _))
    · filter_upwards [] with z
      apply tendsto_const_nhds.congr'
      filter_upwards [SmoothCutoff.approximate_gradient_eventuallyEq F hF z.2] with j hj
      rw [hj]
  have hsub : Ioc a b ⊆ Icc 0 T := fun t ht => ⟨ha.1.trans ht.1.le,ht.2.trans hb.2⟩
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
    ((bounded_gradient_time_integrable h hF hB).mono_set hsub),?_⟩
  rw [← joint_pairing_eq_interval h hF hB ha hb hab]
  apply tendsto_nhds_unique ((hval b).sub (hval a))
  apply hlim.congr'
  exact Eventually.of_forall fun j => by
    change (∫ z in Ioc a b ×ˢ univ,⟪gradient (ψ j : Point d → ℝ) z.2,curveFlux h z⟫_ℝ
      ∂curveSpaceTimeMeasure h) = _
    rw [joint_pairing_eq_interval h (ψ j).property.1 (hψC j) ha hb hab]
    exact (curveFlux_continuity_equation h hT hE hbound (ψ j) ha hb hab).2.symm

end SharpWasserstein.RoughEulerianCompression
