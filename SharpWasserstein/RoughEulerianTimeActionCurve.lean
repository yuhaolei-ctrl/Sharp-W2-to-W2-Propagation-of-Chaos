import SharpWasserstein.RoughEulerianTimeActionMoments
import SharpWasserstein.WeakTestContinuity

/-! An actual global probability curve for an interior smoothing interval.
Narrow continuity follows from dominated compact-test integrals and an
actual uniform quadratic-moment bound. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff ProbabilityTheory
namespace SharpWasserstein.RoughEulerianSmoothing
open WeightedTangent RoughEulerianTime
variable {d : ℕ} [MeasurableSpace (Point d)] [BorelSpace (Point d)]

/-- Actual compact-test continuity of the regularized law, before clamping. -/
theorem spaceTimeRegularizedLaw_integral_test_continuous {τ ε δ : ℝ}
    (hτ : 0 < τ) (hε : 0 < ε) (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (ρ : Measure (ℝ × Point d)) [IsFiniteMeasure ρ] (φ : Test d) :
    Continuous (fun t => ∫ x,φ.val x ∂spaceTimeRegularizedLaw τ hτ ε hε δ ρ t) := by
  obtain ⟨C,hCpos,hC⟩ := (spaceTimeKernel_allDerivativesBounded (d := d) hτ hε).bounded
  have hD (p : ℝ × Point d) : ‖spaceTimeDensity τ hτ ε hε ρ p‖ ≤ C*ρ.real univ :=
    norm_integral_le_of_norm_le_const (Eventually.of_forall fun z => hC (p-z))
  have hF : Continuous (fun t => ∫ x : Point d,spaceTimeDensity τ hτ ε hε ρ (t,x)*φ.val x) := by
    apply continuous_of_dominated (bound := fun x => (C*ρ.real univ)*‖φ.val x‖)
    · intro t
      exact (((spaceTimeDensity_smooth hτ hε ρ).continuous.comp
        (continuous_const.prodMk continuous_id)).mul φ.property.1.continuous).aestronglyMeasurable
    · intro t
      exact Eventually.of_forall fun x => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hD (t,x)) (norm_nonneg _)
    · exact (φ.property.1.continuous.integrable_of_hasCompactSupport φ.property.2).norm.const_mul _
    · exact Eventually.of_forall fun x =>
        ((spaceTimeDensity_smooth hτ hε ρ).continuous.comp
          (continuous_id.prodMk continuous_const)).mul continuous_const
  have he (t : ℝ) : (∫ x,φ.val x ∂spaceTimeRegularizedLaw τ hτ ε hε δ ρ t) =
      (1-δ)*(∫ x : Point d,spaceTimeDensity τ hτ ε hε ρ (t,x)*φ.val x) +
        δ*(∫ x : Point d,gaussianFloor x*φ.val x) := by
    rw [spaceTimeRegularizedLaw_eq]
    have hd : Continuous (fun x : Point d => floorDensity (1-δ) (spaceTimeDensity τ hτ ε hε ρ)
        (fun p => δ*gaussianFloor p.2) (t,x)) :=
      (continuous_const.mul ((spaceTimeDensity_smooth hτ hε ρ).continuous.comp
        (continuous_const.prodMk continuous_id))).add (continuous_const.mul gaussianFloor_smooth.continuous)
    rw [integral_withDensity_eq_integral_toReal_smul hd.measurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (floorDensity_pos (sub_nonneg.mpr hδ₁)
      (spaceTimeDensity_nonneg hτ hε ρ) (fun p => mul_pos hδ (gaussianFloor_pos p.2)) _).le,smul_eq_mul]
    simp only [floorDensity,add_mul,mul_assoc]
    have hiD : Integrable (fun x : Point d => spaceTimeDensity τ hτ ε hε ρ (t,x)*φ.val x) :=
      (((spaceTimeDensity_smooth hτ hε ρ).continuous.comp
        (continuous_const.prodMk continuous_id)).mul φ.property.1.continuous).integrable_of_hasCompactSupport
          φ.property.2.mul_left
    have hig : Integrable (fun x : Point d => gaussianFloor x*φ.val x) :=
      (gaussianFloor_smooth.continuous.mul φ.property.1.continuous).integrable_of_hasCompactSupport
        φ.property.2.mul_left
    rw [integral_add (hiD.const_mul (1-δ)) (hig.const_mul δ),integral_const_mul,integral_const_mul]
  simp_rw [he]
  exact (continuous_const.mul hF).add continuous_const

/-- Interior physical time corresponding to a globally clamped local time. -/
def averagingTime {a b : ℝ} (hab : a ≤ b) (t : ℝ) : ℝ :=
  a + (projIcc 0 (b-a) (sub_nonneg.mpr hab) t).val

theorem averagingTime_mem {a b : ℝ} (hab : a ≤ b) (t : ℝ) : averagingTime hab t ∈ Icc a b := by
  have hh := (projIcc 0 (b-a) (sub_nonneg.mpr hab) t).property
  dsimp [averagingTime]
  constructor <;> linarith [hh.1,hh.2]

theorem averagingTime_continuous {a b : ℝ} (hab : a ≤ b) : Continuous (averagingTime hab) :=
  continuous_const.add (continuous_subtype_val.comp continuous_projIcc)

theorem averagingTime_eq {a b : ℝ} (hab : a ≤ b) {t : ℝ} (ht : t ∈ Icc 0 (b-a)) :
    averagingTime hab t = a+t := by
  simp only [averagingTime,projIcc_of_mem _ ht]

/-- The actual smoothed probability curve, with no unproved probability or
continuity field supplied by the caller. -/
def spaceTimeProbabilityCurve {τ ε δ a b T : ℝ} (hτ : 0 < τ) (hε : 0 < ε)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (κ : Kernel ℝ (Point d)) [IsMarkovKernel κ]
    (hab : a ≤ b) (ha : τ ≤ a) (hb : b+τ ≤ T) (t : ℝ) : ProbabilityMeasure (Point d) :=
  ⟨spaceTimeRegularizedLaw τ hτ ε hε δ ((volume.restrict (Icc 0 T)) ⊗ₘ κ) (averagingTime hab t),
    spaceTimeRegularizedLaw_probability hτ hε hδ hδ₁ κ
      (by have hh := (averagingTime_mem hab t).1; simpa only [zero_add] using ha.trans hh)
      (by have hh := (averagingTime_mem hab t).2; linarith)⟩

theorem spaceTimeProbabilityCurve_coe {τ ε δ a b T : ℝ} (hτ : 0 < τ) (hε : 0 < ε)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (κ : Kernel ℝ (Point d)) [IsMarkovKernel κ]
    (hab : a ≤ b) (ha : τ ≤ a) (hb : b+τ ≤ T) {t : ℝ} (ht : t ∈ Icc 0 (b-a)) :
    (spaceTimeProbabilityCurve hτ hε hδ hδ₁ κ hab ha hb t  : Measure (Point d)) =
      spaceTimeRegularizedLaw τ hτ ε hε δ ((volume.restrict (Icc 0 T)) ⊗ₘ κ) (a+t) := by
  change spaceTimeRegularizedLaw _ _ _ _ _ _ (averagingTime hab t) = _
  rw [averagingTime_eq hab ht]

theorem spaceTimeProbabilityCurve_quadratic {τ ε δ R a b T : ℝ} (hτ : 0 < τ) (hε : 0 < ε)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (κ : Kernel ℝ (Point d)) [IsMarkovKernel κ]
    (hab : a ≤ b) (ha : τ ≤ a) (hb : b+τ ≤ T)
    (hρ : ∀ᵐ z ∂((volume.restrict (Icc 0 T)) ⊗ₘ κ),‖z.2‖ ≤ R) (t : ℝ) :
    Integrable (fun x : Point d => ‖x‖^2)
      (spaceTimeProbabilityCurve hτ hε hδ hδ₁ κ hab ha hb t  : Measure (Point d)) ∧
    (∫ x,‖x‖^2 ∂(spaceTimeProbabilityCurve hτ hε hδ hδ₁ κ hab ha hb t  : Measure (Point d))) ≤
      (1-δ)*(R+ε)^2 + δ*∫ x : Point d,gaussianFloor x*‖x‖^2 := by
  exact spaceTimeRegularizedLaw_quadratic hτ hε hδ hδ₁ κ hρ
    (by have hh := (averagingTime_mem hab t).1; simpa only [zero_add] using ha.trans hh)
    (by have hh := (averagingTime_mem hab t).2; linarith)

/-- Genuine global narrow continuity follows from the derived compact-test
continuity and the genuine uniform moment bound. -/
theorem spaceTimeProbabilityCurve_continuous {τ ε δ R a b T : ℝ} (hτ : 0 < τ) (hε : 0 < ε)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (κ : Kernel ℝ (Point d)) [IsMarkovKernel κ]
    (hab : a ≤ b) (ha : τ ≤ a) (hb : b+τ ≤ T)
    (hρ : ∀ᵐ z ∂((volume.restrict (Icc 0 T)) ⊗ₘ κ),‖z.2‖ ≤ R) :
    Continuous (spaceTimeProbabilityCurve hτ hε hδ hδ₁ κ hab ha hb) := by
  apply WeakTestContinuity.continuous_probabilityMeasure_of_uniformMoment _
    (fun t => (spaceTimeProbabilityCurve_quadratic hτ hε hδ hδ₁ κ hab ha hb hρ t).1)
    (fun t => (spaceTimeProbabilityCurve_quadratic hτ hε hδ hδ₁ κ hab ha hb hρ t).2)
  intro φ
  exact (spaceTimeRegularizedLaw_integral_test_continuous hτ hε hδ hδ₁
    ((volume.restrict (Icc 0 T)) ⊗ₘ κ) φ).comp (averagingTime_continuous hab)

end SharpWasserstein.RoughEulerianSmoothing
