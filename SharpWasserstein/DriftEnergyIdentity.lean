import SharpWasserstein.BochnerIdentity
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Actual differential and integral identities for the internal drift contribution
to weighted tangent energy. Symmetry is derived from the potential, and the test
pairings are genuine compact-support integrations by parts. -/

noncomputable section
namespace SharpWasserstein.DriftEnergyIdentity
open WeightedTangent PDEPairings BochnerIdentity
open scoped InnerProductSpace Topology ContDiff
variable {d : ℕ}

/-- Differentiating the genuine gradient and pairing is exactly the second directional derivative. -/
theorem fderiv_gradient_inner {f : Point d → ℝ} (hf : ContDiff ℝ ∞ f) (v w x : Point d) :
    ⟪fderiv ℝ (gradient f) x v, w⟫_ℝ = directionDeriv v (directionDeriv w f) x := by
  have hg : Differentiable ℝ (gradient f) := (smooth_gradient hf).differentiable (by simp)
  have heq : (fun y => ⟪gradient f y, w⟫_ℝ) = directionDeriv w f := by
    funext y
    exact inner_gradient_left
  have hd := fderiv_inner_apply ℝ (hg x) (differentiableAt_const w) v
  rw [heq] at hd
  simpa only [directionDeriv, fderiv_const_apply, zero_apply, inner_zero_right, zero_add] using hd.symm

/-- The genuine derivative of a smooth gradient is self-adjoint. -/
theorem fderiv_gradient_symmetric {f : Point d → ℝ} (hf : ContDiff ℝ ∞ f) (v w x : Point d) :
    ⟪fderiv ℝ (gradient f) x v, w⟫_ℝ = ⟪fderiv ℝ (gradient f) x w, v⟫_ℝ := by
  rw [fderiv_gradient_inner hf, fderiv_gradient_inner hf]
  exact directionDeriv_commute (contDiff_two_of_smooth hf) _ _ _

/-- Exact pointwise internal-drift cancellation for an actual smooth potential. -/
theorem drift_energy_integrand {f : Point d → ℝ} (hf : ContDiff ℝ ∞ f)
    {a : Point d → Point d} (ha : Differentiable ℝ a) (x : Point d) :
    2 * ⟪gradient f x, gradient (fun y => ⟪a y, gradient f y⟫_ℝ) x⟫_ℝ -
      ⟪a x, gradient (fun y => ‖gradient f y‖ ^ 2) x⟫_ℝ =
        2 * ⟪fderiv ℝ a x (gradient f x), gradient f x⟫_ℝ := by
  have hg : Differentiable ℝ (gradient f) := (smooth_gradient hf).differentiable (by simp)
  have hs : ⟪a x, fderiv ℝ (gradient f) x (gradient f x)⟫_ℝ =
      ⟪fderiv ℝ (gradient f) x (a x), gradient f x⟫_ℝ := by
    rw [real_inner_comm, fderiv_gradient_symmetric hf]
  have hn : (fun y => ‖gradient f y‖ ^ 2) = fun y => ⟪gradient f y, gradient f y⟫_ℝ := by
    funext y
    exact (real_inner_self_eq_norm_sq _).symm
  rw [inner_gradient_right (f := fun y => ⟪a y, gradient f y⟫_ℝ),
    inner_gradient_right (f := fun y => ‖gradient f y‖ ^ 2)]
  simp only [RCLike.conj_to_real]
  rw [hn, fderiv_inner_apply ℝ (ha x) (hg x), fderiv_inner_apply ℝ (hg x) (hg x), hs]
  rw [real_inner_comm (gradient f x) (fderiv ℝ (gradient f) x (a x))]
  ring

/-- The true Jacobian operator norm controls its quadratic form with the Euclidean energy. -/
theorem jacobian_quadratic_le (A : Point d →L[ℝ] Point d) {L : ℝ} (hA : ‖A‖ ≤ L)
    (w : Point d) : ⟪A w, w⟫_ℝ ≤ L * ‖w‖ ^ 2 := by
  calc
    _ ≤ ‖A w‖ * ‖w‖ := real_inner_le_norm _ _
    _ ≤ (‖A‖ * ‖w‖) * ‖w‖ := mul_le_mul_of_nonneg_right (A.le_opNorm w) (norm_nonneg _)
    _ ≤ (L * ‖w‖) * ‖w‖ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hA (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

/-- Testing a smooth vector field against the actual compact-test gradient gives a compact smooth scalar test. -/
def driftTest (a : Point d → Point d) (ha : ContDiff ℝ ∞ a) (φ : Test d) : Test d :=
  ⟨fun y => ⟪a y, gradient (φ : Point d → ℝ) y⟫_ℝ,
    ha.inner ℝ (smooth_gradient φ.property.1),
    (compactSupport_test_gradient φ).mono (by
      intro x hx hz
      exact hx (by simp only [hz, inner_zero_right]))⟩

open MeasureTheory
variable [MeasurableSpace (Point d)] [BorelSpace (Point d)]
variable (μ : Measure (Point d)) [Measure.IsAddHaarMeasure μ]

/-- Density times a continuous flux paired against an actual compact-test gradient is genuinely integrable. -/
theorem integrable_density_testGradient (ρ : Point d → ℝ) (hρ : Continuous ρ)
    (F : Point d → Point d) (hF : Continuous F) (φ : Test d) :
    Integrable (fun x => ρ x * ⟪F x, gradient (φ : Point d → ℝ) x⟫_ℝ) μ := by
  apply (hρ.mul (hF.inner (continuous_test_gradient φ))).integrable_of_hasCompactSupport
  apply HasCompactSupport.mul_left
  apply (compactSupport_test_gradient φ).mono
  intro x hx hz
  exact hx (by simp only [hz, inner_zero_right])

/-- The actual strong drift pairings collapse to the derivative of the drift, with no Hessian term. -/
theorem integral_drift_energy (ρ : Point d → ℝ) (hρ : ContDiff ℝ 1 ρ)
    (a : Point d → Point d) (ha : ContDiff ℝ ∞ a) (φ : Test d) :
    2 * (∫ x, (-divergence (fun y => ρ y • gradient (φ : Point d → ℝ) y) x) *
      ⟪a x, gradient (φ : Point d → ℝ) x⟫_ℝ ∂μ) +
      (∫ x, divergence (fun y => ρ y • a y) x * ‖gradient (φ : Point d → ℝ) x‖ ^ 2 ∂μ) =
    2 * ∫ x, ρ x * ⟪fderiv ℝ a x (gradient (φ : Point d → ℝ) x),
      gradient (φ : Point d → ℝ) x⟫_ℝ ∂μ := by
  let F : Point d → Point d := fun x => ρ x • gradient (φ : Point d → ℝ) x
  let G : Point d → Point d := fun x => ρ x • a x
  have hφ1 : ContDiff ℝ 1 (gradient (φ : Point d → ℝ)) :=
    (smooth_gradient φ.property.1).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)
  have ha1 : ContDiff ℝ 1 a := ha.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)
  have hF : ContDiff ℝ 1 F := hρ.smul hφ1
  have hG : ContDiff ℝ 1 G := hρ.smul ha1
  have hp1 := integral_divergence_mul μ F hF (driftTest a ha φ)
  have hp2 := integral_divergence_mul μ G hG (gradientNormSqTest φ)
  have hfirst : (∫ x, (-divergence F x) * ⟪a x, gradient (φ : Point d → ℝ) x⟫_ℝ ∂μ) =
      ∫ x, ρ x * ⟪gradient (φ : Point d → ℝ) x, gradient (driftTest a ha φ : Point d → ℝ) x⟫_ℝ ∂μ := by
    simp only [neg_mul, integral_neg]
    change -(∫ x, divergence F x * (driftTest a ha φ : Point d → ℝ) x ∂μ) = _
    rw [hp1, neg_neg]
    apply integral_congr_ae
    filter_upwards [] with x
    exact real_inner_smul_left _ _ _
  have hsecond : (∫ x, divergence G x * ‖gradient (φ : Point d → ℝ) x‖ ^ 2 ∂μ) =
      -(∫ x, ρ x * ⟪a x, gradient (gradientNormSqTest φ : Point d → ℝ) x⟫_ℝ ∂μ) := by
    change (∫ x, divergence G x * (gradientNormSqTest φ : Point d → ℝ) x ∂μ) = _
    rw [hp2]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with x
    exact real_inner_smul_left _ _ _
  change 2 * (∫ x, (-divergence F x) * ⟪a x, gradient (φ : Point d → ℝ) x⟫_ℝ ∂μ) +
    (∫ x, divergence G x * ‖gradient (φ : Point d → ℝ) x‖ ^ 2 ∂μ) = _
  rw [hfirst, hsecond, ← sub_eq_add_neg, ← integral_const_mul]
  have hint1 := (integrable_density_testGradient μ ρ hρ.continuous
    (gradient (φ : Point d → ℝ)) (continuous_test_gradient φ) (driftTest a ha φ)).const_mul 2
  have hint2 := integrable_density_testGradient μ ρ hρ.continuous a ha.continuous (gradientNormSqTest φ)
  rw [← integral_sub hint1 hint2, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  change 2 * (ρ x * ⟪gradient (φ : Point d → ℝ) x,
      gradient (fun y => ⟪a y, gradient (φ : Point d → ℝ) y⟫_ℝ) x⟫_ℝ) -
    ρ x * ⟪a x, gradient (fun y => ‖gradient (φ : Point d → ℝ) y‖ ^ 2) x⟫_ℝ = _
  calc
    _ = ρ x * (2 * ⟪gradient (φ : Point d → ℝ) x,
        gradient (fun y => ⟪a y, gradient (φ : Point d → ℝ) y⟫_ℝ) x⟫_ℝ -
      ⟪a x, gradient (fun y => ‖gradient (φ : Point d → ℝ) y‖ ^ 2) x⟫_ℝ) := by ring
    _ = ρ x * (2 * ⟪fderiv ℝ a x (gradient (φ : Point d → ℝ) x),
        gradient (φ : Point d → ℝ) x⟫_ℝ) :=
      congrArg (fun r => ρ x * r) (drift_energy_integrand φ.property.1 (ha.differentiable (by simp)) x)
    _ = _ := by ring

/-- The actual integrated drift contribution is bounded by the Euclidean tangent energy,
with a dimension-free coefficient given by the genuine Jacobian bound. -/
theorem integral_drift_energy_le (ρ : Point d → ℝ) (hρ : ContDiff ℝ 1 ρ)
    (a : Point d → Point d) (ha : ContDiff ℝ ∞ a) (φ : Test d) {L : ℝ}
    (hρnonneg : ∀ᵐ x ∂μ, 0 ≤ ρ x) (hA : ∀ᵐ x ∂μ, ‖fderiv ℝ a x‖ ≤ L) :
    2 * (∫ x, (-divergence (fun y => ρ y • gradient (φ : Point d → ℝ) y) x) *
      ⟪a x, gradient (φ : Point d → ℝ) x⟫_ℝ ∂μ) +
      (∫ x, divergence (fun y => ρ y • a y) x * ‖gradient (φ : Point d → ℝ) x‖ ^ 2 ∂μ) ≤
    2 * L * ∫ x, ρ x * ‖gradient (φ : Point d → ℝ) x‖ ^ 2 ∂μ := by
  rw [integral_drift_energy μ ρ hρ a ha φ, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  rw [← integral_const_mul]
  have hint1 : Integrable (fun x => ρ x *
      ⟪fderiv ℝ a x (gradient (φ : Point d → ℝ) x), gradient (φ : Point d → ℝ) x⟫_ℝ) μ :=
    integrable_density_testGradient μ ρ hρ.continuous
      (fun x => fderiv ℝ a x (gradient (φ : Point d → ℝ) x))
      ((ha.continuous_fderiv (by simp)).clm_apply (continuous_test_gradient φ)) φ
  have hint2 : Integrable (fun x => L * (ρ x * ‖gradient (φ : Point d → ℝ) x‖ ^ 2)) μ :=
    ((hρ.continuous.mul (smooth_gradient_norm_sq φ.property.1).continuous).integrable_of_hasCompactSupport
      (gradientNormSqTest φ).property.2.mul_left).const_mul L
  apply integral_mono_ae hint1 hint2
  filter_upwards [hρnonneg, hA] with x hx hAx
  calc
    _ ≤ ρ x * (L * ‖gradient (φ : Point d → ℝ) x‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (jacobian_quadratic_le (fderiv ℝ a x) hAx _) hx
    _ = _ := by ring

end SharpWasserstein.DriftEnergyIdentity
