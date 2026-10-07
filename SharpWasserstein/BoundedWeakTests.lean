module

public import SharpWasserstein.Compat
public import SharpWasserstein.SmoothCutoffSecondOrder
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-! Extension of actual compact-smooth weak evolution identities to bounded
smooth tests with bounded first derivatives and Laplacian. The generator is
integrated over an arbitrary finite space carrying measurable positions and an
integrable velocity, so this applies to time-space occupation measures and to
marginal cylinder tests without an independence hypothesis. -/

noncomputable section
namespace SharpWasserstein.BoundedWeakTests
open MeasureTheory Set Filter WeightedTangent PDEPairings BochnerIdentity SmoothCutoff
open scoped InnerProductSpace Topology ContDiff
variable {d : ℕ} [MeasurableSpace (Point d)] [BorelSpace (Point d)]

/-- The actual Euclidean diffusion-and-drift generator at a position and velocity. -/
def generator (f : Point d → ℝ) (x v : Point d) : ℝ :=
  laplacian f x + ⟪v, gradient f x⟫_ℝ

omit [MeasurableSpace (Point d)] [BorelSpace (Point d)] in
/-- Pointwise convergence of actual compact approximants includes the values themselves. -/
theorem approximate_eventuallyEq (f : Point d → ℝ) (hf : ContDiff ℝ ∞ f) (x : Point d) :
    ∀ᶠ j in atTop, (approximate f hf j : Point d → ℝ) x = f x := by
  filter_upwards [cutoff_eventuallyEq_one x] with j hj
  change cutoff d j x * f x = f x
  rw [hj.self_of_nhds, one_mul]

/-- Actual endpoint integrals converge for every finite Borel measure. -/
theorem tendsto_integral_approximate (μ : Measure (Point d)) [IsFiniteMeasure μ]
    (f : Point d → ℝ) (hf : ContDiff ℝ ∞ f) {A : ℝ} (hfa : ∀ x, |f x| ≤ A) :
    Tendsto (fun j => ∫ x, (approximate f hf j : Point d → ℝ) x ∂μ)
      atTop (𝓝 (∫ x, f x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => A)
    (fun j => (approximate f hf j).property.1.continuous.aestronglyMeasurable) (integrable_const _) ?_ ?_
  · intro j
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs] using approximate_abs_bound f hf hfa j x
  · filter_upwards [] with x
    exact tendsto_const_nhds.congr' (Filter.EventuallyEq.symm (approximate_eventuallyEq f hf x))

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace (Point d)] [BorelSpace (Point d)] in
/-- A bounded smooth generator with integrable velocity is genuinely integrable. -/
theorem integrable_generator (τ : Measure Ω) [IsFiniteMeasure τ]
    (X v : Ω → Point d) (hX : AEStronglyMeasurable X τ) (hv : Integrable v τ)
    (f : Point d → ℝ) (hf : ContDiff ℝ ∞ f) {B D : ℝ}
    (hfb : ∀ x, ‖gradient f x‖ ≤ B) (hfd : ∀ x, |laplacian f x| ≤ D) :
    Integrable (fun z => generator f (X z) (v z)) τ := by
  apply ((integrable_const D).add (hv.norm.mul_const B)).mono'
    (((smooth_laplacian hf).continuous.comp_aestronglyMeasurable hX).add
      (hv.aestronglyMeasurable.inner ((smooth_gradient hf).continuous.comp_aestronglyMeasurable hX)))
  filter_upwards [] with z
  change ‖laplacian f (X z) + ⟪v z, gradient f (X z)⟫_ℝ‖ ≤ D + ‖v z‖ * B
  exact (norm_add_le _ _).trans (add_le_add
    (by simpa only [Real.norm_eq_abs] using hfd (X z))
    ((norm_inner_le_norm (𝕜 := ℝ) _ _).trans
      (mul_le_mul_of_nonneg_left (hfb (X z)) (norm_nonneg _))))

omit [MeasurableSpace (Point d)] [BorelSpace (Point d)] in
/-- The true generators of the compact approximants converge in actual integrals.
The domination uses finite mass and an integrable velocity, with no moment assumption on positions. -/
theorem tendsto_integral_generator_approximate (τ : Measure Ω) [IsFiniteMeasure τ]
    (X v : Ω → Point d) (hX : AEStronglyMeasurable X τ) (hv : Integrable v τ)
    (f : Point d → ℝ) (hf : ContDiff ℝ ∞ f) {A B D : ℝ}
    (hfa : ∀ x, |f x| ≤ A) (hfb : ∀ x, ‖gradient f x‖ ≤ B)
    (hfd : ∀ x, |laplacian f x| ≤ D) :
    Tendsto (fun j => ∫ z, generator (approximate f hf j : Point d → ℝ) (X z) (v z) ∂τ)
      atTop (𝓝 (∫ z, generator f (X z) (v z) ∂τ)) := by
  have hA : 0 ≤ A := (abs_nonneg (f 0)).trans (hfa 0)
  let Cg : ℝ := B + A * (baseLipschitzConstant d : ℝ)
  let Cd : ℝ := D + A * ((d : ℝ) * (baseHessianConstant d : ℝ)) +
    2 * (baseLipschitzConstant d : ℝ) * B
  refine tendsto_integral_of_dominated_convergence (fun z => Cd + ‖v z‖ * Cg)
    ?_ ((integrable_const Cd).add (hv.norm.mul_const Cg)) ?_ ?_
  · intro j
    exact (((smooth_laplacian (approximate f hf j).property.1).continuous.comp_aestronglyMeasurable hX).add
      (hv.aestronglyMeasurable.inner ((continuous_test_gradient (approximate f hf j)).comp_aestronglyMeasurable hX)))
  · intro j
    filter_upwards [] with z
    change ‖laplacian (approximate f hf j : Point d → ℝ) (X z) +
      ⟪v z, gradient (approximate f hf j : Point d → ℝ) (X z)⟫_ℝ‖ ≤ _
    apply (norm_add_le _ _).trans
    apply add_le_add
    · simpa only [Real.norm_eq_abs] using approximate_laplacian_bound f hf hA hfa hfb hfd j (X z)
    · exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
        (mul_le_mul_of_nonneg_left (approximate_gradient_bound f hf hA hfa hfb j (X z)) (norm_nonneg _))
  · filter_upwards [] with z
    apply tendsto_const_nhds.congr'
    filter_upwards [approximate_laplacian_eventuallyEq f hf (X z),
      approximate_gradient_eventuallyEq f hf (X z)] with j hj hk
    simp only [generator, hj, hk]

/-- Actual compact-test weak evolution identities extend to bounded smooth tests with
bounded gradient and Laplacian, including noncompact cylinder lifts. -/
theorem extend_weak_generator_identity
    (μ₀ μ₁ : Measure (Point d)) [IsFiniteMeasure μ₀] [IsFiniteMeasure μ₁]
    (τ : Measure Ω) [IsFiniteMeasure τ]
    (X v : Ω → Point d) (hX : AEStronglyMeasurable X τ) (hv : Integrable v τ)
    (hweak : ∀ φ : Test d,
      (∫ x, (φ : Point d → ℝ) x ∂μ₁) - (∫ x, (φ : Point d → ℝ) x ∂μ₀) =
        ∫ z, generator φ (X z) (v z) ∂τ)
    (f : Point d → ℝ) (hf : ContDiff ℝ ∞ f) {A B D : ℝ}
    (hfa : ∀ x, |f x| ≤ A) (hfb : ∀ x, ‖gradient f x‖ ≤ B)
    (hfd : ∀ x, |laplacian f x| ≤ D) :
    (∫ x, f x ∂μ₁) - (∫ x, f x ∂μ₀) = ∫ z, generator f (X z) (v z) ∂τ := by
  have hl := (tendsto_integral_approximate μ₁ f hf hfa).sub
    (tendsto_integral_approximate μ₀ f hf hfa)
  have hr := tendsto_integral_generator_approximate τ X v hX hv f hf hfa hfb hfd
  apply tendsto_nhds_unique hl
  apply hr.congr'
  filter_upwards [] with j
  exact (hweak (approximate f hf j)).symm

end SharpWasserstein.BoundedWeakTests
