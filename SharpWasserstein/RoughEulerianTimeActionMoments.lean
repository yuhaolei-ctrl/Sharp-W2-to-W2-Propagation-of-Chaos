import SharpWasserstein.RoughEulerianTimeActionIdentification

/-! Bounded spatial carrying support survives genuine time averaging. The
regularized probability laws have actual finite quadratic moments, with a
uniform bound independent of the averaging time. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff ProbabilityTheory
namespace SharpWasserstein.RoughEulerianSmoothing
open WeightedTangent RoughEulerianTime
variable {d : ℕ} [MeasurableSpace (Point d)] [BorelSpace (Point d)]

theorem averagedKernel_norm_le {τ R : ℝ} (hτ : 0 < τ)
    (ρ : Measure (ℝ × Point d)) [IsFiniteMeasure ρ]
    (hρ : ∀ᵐ z ∂ρ, ‖z.2‖ ≤ R) (t : ℝ) :
    ∀ᵐ x ∂averagedKernel τ hτ ρ t,‖x‖ ≤ R := by
  have hz : ρ (univ ×ˢ (Metric.closedBall (0 : Point d) R)ᶜ)=0 := by
    have he : univ ×ˢ (Metric.closedBall (0 : Point d) R)ᶜ = {z : ℝ × Point d | ¬‖z.2‖ ≤ R} := by
      ext z
      simp
    rw [he]
    exact ae_iff.mp hρ
  have hh := averagedKernel_support hτ ρ (Metric.closedBall (0 : Point d) R)
    Metric.isClosed_closedBall.measurableSet hz t
  apply ae_iff.mpr
  convert hh using 2
  ext x
  simp

/-- The compactly convolved density vanishes outside the enlarged carrying
ball, even when the original probability is singular. -/
theorem density_eq_zero_of_norm_gt {ε R : ℝ} (hε : 0 < ε)
    (μ : Measure (Point d)) (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ R) {x : Point d} (hx : R+ε < ‖x‖) :
    density ε hε μ x = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [hμ] with y hy
  apply mollifier_eq_zero hε
  have hh := norm_le_norm_sub_add x y
  linarith

/-- Uniform moment bound for the actual positive-floor regularization of
any probability supported in a fixed ball. -/
theorem regularizedLaw_quadratic_le {ε δ R : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (μ : Measure (Point d)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ R) :
    (∫ x,‖x‖^2 ∂regularizedLaw ε hε δ μ) ≤
      (1-δ)*(R+ε)^2 + δ*∫ x : Point d,gaussianFloor x*‖x‖^2 := by
  have hρi : Integrable (fun x : Point d => density ε hε μ x*‖x‖^2) :=
    ((density_smooth hε μ).continuous.mul (continuous_norm.pow 2)).integrable_of_hasCompactSupport
      (density_compact hε μ hμ).mul_right
  have hρle : (∫ x : Point d,density ε hε μ x*‖x‖^2) ≤ (R+ε)^2 := by
    calc
      _ ≤ ∫ x : Point d,density ε hε μ x*(R+ε)^2 := by
        apply integral_mono hρi ((density_integrable hε μ).mul_const _)
        intro x
        dsimp only
        by_cases hx : ‖x‖ ≤ R+ε
        · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx 2)
            (density_nonneg hε μ x)
        · rw [density_eq_zero_of_norm_gt hε μ hμ (lt_of_not_ge hx),zero_mul,zero_mul]
      _ = _ := by rw [integral_mul_const,density_integral hε μ,one_mul]
  rw [regularizedLaw,integral_withDensity_eq_integral_toReal_smul
    (regularizedDensity_smooth hε δ μ).continuous.measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (regularizedDensity_pos hε hδ hδ₁ μ _).le,smul_eq_mul]
  simp only [regularizedDensity,floorDensity,add_mul,mul_assoc]
  rw [integral_add (hρi.const_mul (1-δ)) (gaussianFloor_quadratic_integrable.const_mul δ),
    integral_const_mul,integral_const_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left hρle (sub_nonneg.mpr hδ₁)) le_rfl

/-- Genuine P₂ and one uniform moment bound for every interior averaging
time. No moment of a selected timewise flux enters the assumptions. -/
theorem spaceTimeRegularizedLaw_quadratic {τ ε δ R a b t : ℝ} (hτ : 0 < τ) (hε : 0 < ε)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (κ : Kernel ℝ (Point d)) [IsMarkovKernel κ]
    (hρ : ∀ᵐ z ∂((volume.restrict (Icc a b)) ⊗ₘ κ),‖z.2‖ ≤ R)
    (ha : a+τ ≤ t) (hb : t+τ ≤ b) :
    Integrable (fun x : Point d => ‖x‖^2)
      (spaceTimeRegularizedLaw τ hτ ε hε δ ((volume.restrict (Icc a b)) ⊗ₘ κ) t) ∧
    (∫ x,‖x‖^2 ∂spaceTimeRegularizedLaw τ hτ ε hε δ
      ((volume.restrict (Icc a b)) ⊗ₘ κ) t) ≤
      (1-δ)*(R+ε)^2 + δ*∫ x : Point d,gaussianFloor x*‖x‖^2 := by
  letI := averagedKernel_probability hτ κ ha hb
  have hs := averagedKernel_norm_le hτ ((volume.restrict (Icc a b)) ⊗ₘ κ) hρ t
  exact ⟨regularizedLaw_quadratic_integrable hε hδ hδ₁ _ hs,
    regularizedLaw_quadratic_le hε hδ hδ₁ _ hs⟩

end SharpWasserstein.RoughEulerianSmoothing
