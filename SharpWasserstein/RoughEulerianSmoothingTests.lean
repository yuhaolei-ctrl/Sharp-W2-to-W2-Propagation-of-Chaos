import SharpWasserstein.RoughEulerianSmoothingCoupling

/-! Compact smooth tests are preserved by the actual compact noise average.
The derivative and law-pairing identities are proved for the real convolution,
so original weak equations can be applied before spatial regularization. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff InnerProductSpace
namespace SharpWasserstein.RoughEulerianSmoothing
open WeightedTangent NoiseAverage
variable {d : ℕ} [MeasurableSpace (Point d)] [BorelSpace (Point d)]

def smoothTestFunction (ε : ℝ) (hε : 0 < ε) (φ : Test d) : Point d → ℝ :=
  NoiseAverage.average (mollifierLaw ε hε) id (φ : Point d → ℝ)

theorem smoothTestFunction_integral {ε : ℝ} (hε : 0 < ε) (φ : Test d) (y : Point d) :
    smoothTestFunction ε hε φ y = ∫ z, mollifier ε hε z * (φ : Point d → ℝ) (y+z) := by
  rw [smoothTestFunction, NoiseAverage.average, mollifierLaw, integral_withDensity_eq_integral_toReal_smul
    (mollifier_smooth hε).continuous.measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (mollifier_nonneg hε _), smul_eq_mul, id_eq]

theorem smoothTestFunction_smooth {ε : ℝ} (hε : 0 < ε) (φ : Test d) :
    ContDiff ℝ ∞ (smoothTestFunction ε hε φ) :=
  contDiff_infty_average (mollifierLaw ε hε) id stronglyMeasurable_id φ.property.1
    (allDerivativesBounded_of_compact φ.property.1 φ.property.2)

theorem smoothTestFunction_compact {ε : ℝ} (hε : 0 < ε) (φ : Test d) :
    HasCompactSupport (smoothTestFunction ε hε φ) := by
  obtain ⟨R,hR⟩ := φ.property.2.isBounded.subset_closedBall (0 : Point d)
  apply HasCompactSupport.intro' (isCompact_closedBall (0 : Point d) (R+ε)) Metric.isClosed_closedBall
  intro y hy
  have hy' : R+ε < ‖y‖ := by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hy
  rw [smoothTestFunction_integral hε φ y]
  apply integral_eq_zero_of_ae
  apply Eventually.of_forall
  intro z
  by_cases hz : ε ≤ ‖z‖
  · simp only [mollifier_eq_zero hε hz, zero_mul, Pi.zero_apply]
  · have hφ : (φ : Point d → ℝ) (y+z) = 0 := by
      by_contra hn
      have hnorm : ‖y+z‖ ≤ R := by
        have hm := hR (subset_closure (show y+z ∈ Function.support (φ : Point d → ℝ) from hn))
        simpa only [Metric.mem_closedBall, dist_zero_right] using hm
      have hh : ‖y‖ ≤ ‖y+z‖+‖z‖ := by simpa only [add_sub_cancel_right] using norm_sub_le (y+z) z
      have hz' := lt_of_not_ge hz
      linarith
    simp only [hφ, mul_zero, Pi.zero_apply]

def smoothTest (ε : ℝ) (hε : 0 < ε) (φ : Test d) : Test d :=
  ⟨smoothTestFunction ε hε φ, smoothTestFunction_smooth hε φ, smoothTestFunction_compact hε φ⟩

theorem smoothTest_fderiv {ε : ℝ} (hε : 0 < ε) (φ : Test d) :
    fderiv ℝ (smoothTest ε hε φ : Point d → ℝ) =
      NoiseAverage.average (mollifierLaw ε hε) id (fderiv ℝ (φ : Point d → ℝ)) := by
  obtain ⟨C,_,hC⟩ := (allDerivativesBounded_of_compact φ.property.1 φ.property.2).bounded
  obtain ⟨L,hL⟩ := (allDerivativesBounded_of_compact φ.property.1 φ.property.2).lipschitz
    (φ.property.1.differentiable (by simp))
  exact fderiv_average (mollifierLaw ε hε) id stronglyMeasurable_id
    (φ.property.1.of_le (by simp)) hL hC

theorem smoothTest_gradient_pairing {ε : ℝ} (hε : 0 < ε) (φ : Test d) (y u : Point d) :
    ⟪gradient (smoothTest ε hε φ : Point d → ℝ) y,u⟫_ℝ =
      ∫ z, ⟪gradient (φ : Point d → ℝ) (y+z),u⟫_ℝ ∂mollifierLaw ε hε := by
  rw [inner_gradient_left, smoothTest_fderiv hε φ]
  obtain ⟨C,_,hC⟩ := (allDerivativesBounded_of_compact φ.property.1 φ.property.2).fderiv.bounded
  have hi := integrable_translate (mollifierLaw ε hε) id stronglyMeasurable_id
    (φ.property.1.continuous_fderiv (by simp)) hC y
  simp only [id_eq] at hi
  change (∫ z, fderiv ℝ (φ : Point d → ℝ) (y+z) ∂mollifierLaw ε hε) u = _
  rw [ContinuousLinearMap.integral_apply hi u]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by simp only [inner_gradient_left]

/-- Exact duality between the constructed convolution law and a genuine
compact smooth test of the original law. -/
theorem convolvedLaw_test_pairing {ε : ℝ} (hε : 0 < ε)
    (μ : Measure (Point d)) [IsProbabilityMeasure μ] (φ : Test d) :
    (∫ x, (φ : Point d → ℝ) x ∂convolvedLaw ε hε μ) =
      ∫ y, (smoothTest ε hε φ : Point d → ℝ) y ∂μ := by
  have hm : Measurable (fun z : Point d × Point d => z.1+z.2) := measurable_fst.add measurable_snd
  rw [convolvedLaw_eq_map_add hε μ, integral_map hm.aemeasurable φ.property.1.continuous.aestronglyMeasurable]
  obtain ⟨C,hC⟩ := φ.property.2.exists_bound_of_continuous φ.property.1.continuous
  have hi : Integrable (fun z : Point d × Point d => (φ : Point d → ℝ) (z.1+z.2))
      (μ.prod (mollifierLaw ε hε)) :=
    Integrable.of_bound (φ.property.1.continuous.comp (continuous_fst.add continuous_snd)).aestronglyMeasurable
      C (Eventually.of_forall fun z => hC (z.1+z.2))
  rw [integral_prod _ hi]
  rfl

end SharpWasserstein.RoughEulerianSmoothing
