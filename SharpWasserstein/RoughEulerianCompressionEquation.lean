module

public import SharpWasserstein.Compat
public import SharpWasserstein.RoughEulerianCompressionTests
public import SharpWasserstein.RoughEulerianCompressionFlux
public import SharpWasserstein.RoughEulerianCompressionEndpoint

@[expose] public section

/-! The compressed probability curve and actual pushed flux satisfy the literal
compact-test continuity equation. Its action bound and endpoint convergence
come from the separately proved Jacobian contraction and graph coupling. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped InnerProductSpace Topology ENNReal ProbabilityTheory Interval ContDiff
namespace SharpWasserstein.RoughEulerianCompression
open WeightedTangent RoughEulerianTransport
variable {d : ℕ} [MeasurableSpace (Point d)] [BorelSpace (Point d)]

omit [MeasurableSpace (Point d)] [BorelSpace (Point d)] in
/-- The real chain rule identifies the compressed gradient pairing, with its exact sign. -/
theorem compression_gradient_pairing {R : ℝ} (φ : Test d) (x u : Point d) :
    ⟪gradient ((φ : Point d → ℝ) ∘ compression R) x,u⟫_ℝ =
      ⟪gradient (φ : Point d → ℝ) (compression R x),fderiv ℝ (compression R) x u⟫_ℝ := by
  rw [inner_gradient_left,inner_gradient_left,
    fderiv_comp x (test_differentiable φ _) ((compression_contDiff R).differentiable (by simp) x),
    ContinuousLinearMap.comp_apply]

omit [MeasurableSpace (Point d)] [BorelSpace (Point d)] in
/-- A compact output test becomes a bounded smooth input test with bounded Euclidean gradient. -/
theorem compressed_test_bounds {R : ℝ} (hR : R ≠ 0) (φ : Test d) :
    ∃ A B : ℝ, (∀ x,|φ.val (compression R x)| ≤ A) ∧
      ∀ x,‖gradient ((φ : Point d → ℝ) ∘ compression R) x‖ ≤ B := by
  obtain ⟨A,hA⟩ := φ.property.2.exists_bound_of_continuous φ.property.1.continuous
  obtain ⟨B,hB⟩ := (φ.property.2.fderiv ℝ).exists_bound_of_continuous
    (φ.property.1.continuous_fderiv (by simp))
  refine ⟨A,B,fun x => by simpa only [Real.norm_eq_abs] using hA (compression R x),?_⟩
  intro x
  rw [SmoothCutoff.norm_gradient_eq_fderiv,
    fderiv_comp x (test_differentiable φ _) ((compression_contDiff R).differentiable (by simp) x)]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_left (compression_fderiv_norm_le hR x) (norm_nonneg _)).trans
      (by simpa only [mul_one] using hB (compression R x)))

/-- Localized pushed pairing is exactly the original pairing with the compressed test. -/
theorem compressedFlux_localized_gradient {α : Type*} [MeasurableSpace α]
    (ρ : Measure (α × Point d)) [IsFiniteMeasure ρ] {R : ℝ} (hR : R ≠ 0)
    (U : Lp (Point d) 2 ρ) (s : Set α) (hs : MeasurableSet s) (φ : Test d) :
    (∫ z in s ×ˢ univ,⟪gradient (φ : Point d → ℝ) z.2,compressedFlux ρ hR U z⟫_ℝ
      ∂ρ.map (compressionMap R)) =
      ∫ z in s ×ˢ univ,⟪gradient ((φ : Point d → ℝ) ∘ compression R) z.2,U z⟫_ℝ ∂ρ := by
  classical
  let G : α × Point d → Point d := (s ×ˢ univ).indicator
    (fun z => gradient (φ : Point d → ℝ) z.2)
  have hG : MemLp G 2 (ρ.map (compressionMap R)) := by
    obtain ⟨C,hC⟩ := (compactSupport_test_gradient φ).exists_bound_of_continuous
      (continuous_test_gradient φ)
    exact (MemLp.of_bound ((continuous_test_gradient φ).measurable.comp measurable_snd).aestronglyMeasurable
      C (Eventually.of_forall fun z => hC z.2)).indicator (hs.prod MeasurableSet.univ)
  have hp := compressedFlux_pairing ρ hR U G hG
  have hl : (fun z => ⟪G z,compressedFlux ρ hR U z⟫_ℝ) =
      (s ×ˢ univ).indicator (fun z => ⟪gradient (φ : Point d → ℝ) z.2,compressedFlux ρ hR U z⟫_ℝ) := by
    funext z
    by_cases hz : z ∈ s ×ˢ univ <;> simp [G,hz]
  have hr : (fun z => ⟪G (z.1,compression R z.2),fderiv ℝ (compression R) z.2 (U z)⟫_ℝ) =
      (s ×ˢ univ).indicator (fun z => ⟪gradient ((φ : Point d → ℝ) ∘ compression R) z.2,U z⟫_ℝ) := by
    funext z
    by_cases hz : z.1 ∈ s
    · simp only [G,mem_prod,hz,mem_univ,and_self,indicator_of_mem]
      exact (compression_gradient_pairing φ z.2 (U z)).symm
    · simp [G,hz]
  rw [hl,hr,integral_indicator (hs.prod MeasurableSet.univ),
    integral_indicator (hs.prod MeasurableSet.univ)] at hp
  exact hp

/-- The genuinely compressed probability law at each time. -/
def compressedCurve (R : ℝ) (μ : ℝ → ProbabilityMeasure (Point d)) (t : ℝ) :
    ProbabilityMeasure (Point d) :=
  (μ t).map (compression R)

theorem compressedCurve_continuous (R : ℝ) {μ : ℝ → ProbabilityMeasure (Point d)}
    (hμ : Continuous μ) : Continuous (compressedCurve R μ) :=
  (ProbabilityMeasure.continuous_map (compression_contDiff R).continuous).comp hμ

variable {μ : ℝ → ProbabilityMeasure (Point d)} {σ : ℝ → Test d →ₗ[ℝ] ℝ} {T : ℝ}
  (h : CompactDistributionContinuity μ σ T)

/-- The output joint measure disintegrates into the actual compressed curve. -/
theorem compressedCurve_jointMeasure (R : ℝ) :
    (curveSpaceTimeMeasure h).map (compressionMap R) =
      (volume.restrict (Icc 0 T)) ⊗ₘ probabilityCurveKernel (compressedCurve R μ)
        (compressedCurve_continuous R h.continuous) := by
  rw [curveSpaceTimeMeasure,compressionMap_compProd]
  congr 1
  ext t s hs
  rw [Kernel.map_apply _ (compression_contDiff R).continuous.measurable]
  rfl

/-- The compressed curve satisfies the actual compact-test continuity equation
against its pushed joint flux. This form directly supports space-time smoothing. -/
theorem compressed_curve_joint_equation (hT : 0 ≤ T) {E : ℝ → ℝ}
    (hE : IntegrableOn E (Icc 0 T))
    (hbound : ∀ᵐ t ∂volume.restrict (Icc 0 T), ∀ φ : Test d,
      testObjective (μ t : Measure (Point d)) (σ t) φ ≤ E t)
    {R : ℝ} (hR : R ≠ 0) (φ : Test d)
    {a b : ℝ} (ha : a ∈ Icc 0 T) (hb : b ∈ Icc 0 T) (hab : a ≤ b) :
    (∫ x,(φ : Point d → ℝ) x ∂(compressedCurve R μ b : Measure (Point d)))-
      (∫ x,(φ : Point d → ℝ) x ∂(compressedCurve R μ a : Measure (Point d))) =
      ∫ z in Ioc a b ×ˢ univ,⟪gradient (φ : Point d → ℝ) z.2,
        compressedFlux (curveSpaceTimeMeasure h) hR (curveFlux h) z⟫_ℝ
        ∂(curveSpaceTimeMeasure h).map (compressionMap R) := by
  obtain ⟨A,B,hA,hB⟩ := compressed_test_bounds hR φ
  have hf : ContDiff ℝ ∞ ((φ : Point d → ℝ) ∘ compression R) :=
    φ.property.1.comp (compression_contDiff R)
  rw [compressedFlux_localized_gradient (curveSpaceTimeMeasure h) hR (curveFlux h)
    (Ioc a b) measurableSet_Ioc φ,joint_pairing_eq_interval h hf hB ha hb hab]
  change (∫ x,(φ : Point d → ℝ) x ∂(μ b : Measure (Point d)).map (compression R))-
    (∫ x,(φ : Point d → ℝ) x ∂(μ a : Measure (Point d)).map (compression R)) = _
  rw [integral_map (compression_contDiff R).continuous.measurable.aemeasurable
      φ.property.1.continuous.aestronglyMeasurable,
    integral_map (compression_contDiff R).continuous.measurable.aemeasurable
      φ.property.1.continuous.aestronglyMeasurable]
  exact (bounded_smooth_continuity_equation h hT hE hbound hf hA hB ha hb hab).2

/-- The output compact-test pairing is integrable in the actual joint carrying law. -/
theorem compressed_curve_pairing_integrable {R : ℝ} (hR : R ≠ 0) (φ : Test d) :
    Integrable (fun z => ⟪gradient (φ : Point d → ℝ) z.2,
      compressedFlux (curveSpaceTimeMeasure h) hR (curveFlux h) z⟫_ℝ)
      ((curveSpaceTimeMeasure h).map (compressionMap R)) := by
  obtain ⟨C,hC⟩ := (compactSupport_test_gradient φ).exists_bound_of_continuous
    (continuous_test_gradient φ)
  have hU := (Lp.memLp (compressedFlux (curveSpaceTimeMeasure h) hR (curveFlux h))).integrable
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  apply (hU.norm.const_mul C).mono'
    (((continuous_test_gradient φ).measurable.comp measurable_snd).aestronglyMeasurable.inner
      (Lp.aestronglyMeasurable _))
  exact Eventually.of_forall fun z => (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (hC z.2) (norm_nonneg _))

/-- The joint weak identity disintegrates into the literal time-dependent
continuity equation for the compressed probability curve and actual rough flux. -/
theorem compressed_curve_continuity_equation (hT : 0 ≤ T) {E : ℝ → ℝ}
    (hE : IntegrableOn E (Icc 0 T))
    (hbound : ∀ᵐ t ∂volume.restrict (Icc 0 T), ∀ φ : Test d,
      testObjective (μ t : Measure (Point d)) (σ t) φ ≤ E t)
    {R : ℝ} (hR : R ≠ 0) (φ : Test d)
    {a b : ℝ} (ha : a ∈ Icc 0 T) (hb : b ∈ Icc 0 T) (hab : a ≤ b) :
    IntervalIntegrable (fun t => ∫ x,⟪gradient (φ : Point d → ℝ) x,
      compressedFlux (curveSpaceTimeMeasure h) hR (curveFlux h) (t,x)⟫_ℝ
      ∂(compressedCurve R μ t : Measure (Point d))) volume a b ∧
    (∫ x,(φ : Point d → ℝ) x ∂(compressedCurve R μ b : Measure (Point d)))-
      (∫ x,(φ : Point d → ℝ) x ∂(compressedCurve R μ a : Measure (Point d))) =
      ∫ t in a..b,∫ x,⟪gradient (φ : Point d → ℝ) x,
        compressedFlux (curveSpaceTimeMeasure h) hR (curveFlux h) (t,x)⟫_ℝ
        ∂(compressedCurve R μ t : Measure (Point d)) := by
  let G : ℝ × Point d → ℝ := fun z => ⟪gradient (φ : Point d → ℝ) z.2,
    compressedFlux (curveSpaceTimeMeasure h) hR (curveFlux h) z⟫_ℝ
  let κ := probabilityCurveKernel (compressedCurve R μ) (compressedCurve_continuous R h.continuous)
  have hi : Integrable G ((volume.restrict (Icc 0 T)) ⊗ₘ κ) := by
    rw [← compressedCurve_jointMeasure h R]
    exact compressed_curve_pairing_integrable h hR φ
  have hit : IntegrableOn (fun t => ∫ x,G (t,x) ∂(compressedCurve R μ t : Measure (Point d)))
      (Icc 0 T) := by
    have hh := hi.integral_compProd
    convert hh using 1
    rfl
  have hsub : Ioc a b ⊆ Icc 0 T := fun t ht => ⟨ha.1.trans ht.1.le,ht.2.trans hb.2⟩
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr (hit.mono_set hsub),?_⟩
  rw [compressed_curve_joint_equation h hT hE hbound hR φ ha hb hab,
    intervalIntegral.integral_of_le hab]
  change (∫ z in Ioc a b ×ˢ univ,G z ∂(curveSpaceTimeMeasure h).map (compressionMap R)) = _
  have hm := congrArg (fun η : Measure (ℝ × Point d) => ∫ z in Ioc a b ×ˢ univ,G z ∂η)
    (compressedCurve_jointMeasure h R)
  apply hm.trans
  have he := Measure.setIntegral_compProd (μ := volume.restrict (Icc 0 T)) (κ := κ)
    (s := Ioc a b) measurableSet_Ioc MeasurableSet.univ hi.integrableOn
  simpa only [Measure.restrict_univ,Measure.restrict_restrict_of_subset hsub,
    κ,probabilityCurveKernel_apply] using he

/-- The compressed curve's genuine flux retains the given total action bound unchanged. -/
theorem compressed_curve_action_le {E : ℝ → ℝ} (hE : IntegrableOn E (Icc 0 T))
    (hbound : ∀ᵐ t ∂volume.restrict (Icc 0 T), ∀ φ : Test d,
      testObjective (μ t : Measure (Point d)) (σ t) φ ≤ E t)
    {R : ℝ} (hR : R ≠ 0) :
    (∫ z,‖compressedFlux (curveSpaceTimeMeasure h) hR (curveFlux h) z‖^2
      ∂(curveSpaceTimeMeasure h).map (compressionMap R)) ≤ ∫ t in Icc 0 T,E t :=
  (compressedFlux_energy_le (curveSpaceTimeMeasure h) hR (curveFlux h)).trans
    (curveFlux_energy_le h hE hbound)

end SharpWasserstein.RoughEulerianCompression
