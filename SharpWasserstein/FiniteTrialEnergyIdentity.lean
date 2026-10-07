module

public import SharpWasserstein.Compat
public import SharpWasserstein.FiniteTrialDriftResidual
public import SharpWasserstein.FiniteGeneratorBounds

@[expose] public section

/-! The complete static generator energy identity for the actual finite
coefficient optimizer. The underlying finite measure is arbitrary, and the
unclosed drift residual is explicit rather than discarded. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace BigOperators
namespace SharpWasserstein.FiniteGradientTrial
open WeightedTangent NoiseAverage BochnerIdentity PDEPairings
variable {n : ℕ} [MeasurableSpace (Point n)] [BorelSpace (Point n)]

/-- Bounded actual derivatives give genuine integrability against any L²
source, for every finite carrying measure. -/
theorem integrable_smooth_gradient_pairing (μ : Measure (Point n)) [IsFiniteMeasure μ]
    {f : Point n → ℝ} (hf : ContDiff ℝ ∞ f) (hB : AllDerivativesBounded f)
    (U : Lp (Point n) 2 μ) : Integrable (fun x => ⟪gradient f x,U x⟫_ℝ) μ := by
  obtain ⟨B,_,h⟩ := (WeightedPeriodicCoefficientEvolution.gradient_allDerivativesBounded hf hB).bounded
  have hg := bounded_smooth_gradient_memLp μ f hf ⟨B,h⟩
  apply (L2.integrable_inner (𝕜 := ℝ) (hg.toLp _) U).congr
  filter_upwards [hg.coeFn_toLp] with x hx
  rw [hx]

omit [MeasurableSpace (Point n)] [BorelSpace (Point n)] in
theorem gradient_fun_add {f g : Point n → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (x : Point n) :
    gradient (fun y => f y+g y) x = gradient f x+gradient g x := by
  unfold gradient
  rw [fderiv_fun_add (hf x) (hg x),map_add]

variable {ι : Type*} [Fintype ι]
  (μ : Measure (Point n)) [IsFiniteMeasure μ]
  (a : ι → Point n → ℝ) (ha : ∀ i,ContDiff ℝ ∞ (a i))
  (hB : ∀ i,∃ B : ℝ,∀ x,‖gradient (a i) x‖ ≤ B)

/-- Exact diffusion, Jacobian, and trial-residual terms for the coefficient
optimizer. No density, smooth optimizer limit, or integration by parts for μ
is used. -/
theorem solution_generator_identity (δ : ℝ) (hδ : 0 < δ) (U : Lp (Point n) 2 μ)
    (hBa : ∀ i,AllDerivativesBounded (a i))
    (Λ : ι → ℝ) (hΛ : ∀ i x,PDEPairings.laplacian (a i) x = -Λ i*a i x)
    {b : Point n → Point n} (hb : ContDiff ℝ ∞ b) (hBb : AllDerivativesBounded b) :
    let c := RegularizedTrialEnergy.solution (gradientMap μ a ha hB) δ U
    let f := potential a c
    2*(∫ x,⟪gradient (FiniteGeneratorCalculus.generator b f) x,U x⟫_ℝ ∂μ)-
      (∫ x,FiniteGeneratorCalculus.generator b (fun y => ‖gradient f y‖^2) x ∂μ) =
    -2*(∫ x,HierarchyAlgebra.frobeniusSq (hessian f x) ∂μ)-2*δ*(∑ i,Λ i*(c i)^2)+
      2*(∫ x,⟪fderiv ℝ b x (gradient f x),gradient f x⟫_ℝ ∂μ)+
      2*(∫ x,⟪U x-gradient f x,gradient (fun y => ⟪b y,gradient f y⟫_ℝ) x⟫_ℝ ∂μ) := by
  dsimp only
  let c := RegularizedTrialEnergy.solution (gradientMap μ a ha hB) δ U
  let f := potential a c
  let D := fun y => ⟪b y,gradient f y⟫_ℝ
  have hf := potential_smooth a ha c
  have hBf := potential_allDerivativesBounded a ha hBa c
  have hD : ContDiff ℝ ∞ D := hb.inner ℝ (smooth_gradient hf)
  have hBD : AllDerivativesBounded D := by
    have he : D = fun y => fderiv ℝ f y (b y) := by
      funext y
      exact inner_gradient_right
    rw [he]
    exact hBf.fderiv.clm_apply (contDiff_infty_iff_fderiv.mp hf).2 hb hBb
  have hΔ := integrable_smooth_gradient_pairing μ (smooth_laplacian hf)
    (FiniteGeneratorCalculus.laplacian_allDerivativesBounded hf hBf) U
  have hDU := integrable_smooth_gradient_pairing μ hD hBD U
  have hg := potential_gradient_memLp μ a ha hB c
  have hDG : Integrable (fun x => ⟪gradient D x,gradient f x⟫_ℝ) μ := by
    apply (integrable_smooth_gradient_pairing μ hD hBD (hg.toLp _)).congr
    filter_upwards [hg.coeFn_toLp] with x hx
    rw [hx]
  have hS := smooth_gradient_norm_sq hf
  have hBS : AllDerivativesBounded (fun y => ‖gradient f y‖^2) := by
    have he : (fun y => ‖gradient f y‖^2) = WeightedPeriodicCoefficientEvolution.gramTest f f := by
      funext y
      exact (real_inner_self_eq_norm_sq _).symm
    rw [he]
    exact WeightedPeriodicCoefficientEvolution.gramTest_allDerivativesBounded hf hf hBf hBf
  have hLapS : Integrable (PDEPairings.laplacian (fun y => ‖gradient f y‖^2)) μ := by
    obtain ⟨C,_,hC⟩ := (FiniteGeneratorCalculus.laplacian_allDerivativesBounded hS hBS).bounded
    exact Integrable.of_bound (smooth_laplacian hS).continuous.aestronglyMeasurable C
      (Eventually.of_forall hC)
  have hDriftS : Integrable (fun x => ⟪b x,gradient (fun y => ‖gradient f y‖^2) x⟫_ℝ) μ := by
    have he : (fun x => ⟪b x,gradient (fun y => ‖gradient f y‖^2) x⟫_ℝ) =
        fun x => fderiv ℝ (fun y => ‖gradient f y‖^2) x (b x) := by
      funext x
      exact inner_gradient_right
    rw [he]
    have hs := (contDiff_infty_iff_fderiv.mp hS).2.clm_apply hb
    obtain ⟨C,_,hC⟩ := (hBS.fderiv.clm_apply (contDiff_infty_iff_fderiv.mp hS).2 hb hBb).bounded
    exact Integrable.of_bound hs.continuous.aestronglyMeasurable C (Eventually.of_forall hC)
  have hDrift : 2*(∫ x,⟪gradient D x,U x⟫_ℝ ∂μ)-
      (∫ x,⟪b x,gradient (fun y => ‖gradient f y‖^2) x⟫_ℝ ∂μ) =
      2*(∫ x,⟪fderiv ℝ b x (gradient f x),gradient f x⟫_ℝ ∂μ)+
      2*(∫ x,⟪U x-gradient f x,gradient D x⟫_ℝ ∂μ) := by
    have he : 2*(∫ x,⟪gradient D x,gradient f x⟫_ℝ ∂μ)-
        (∫ x,⟪b x,gradient (fun y => ‖gradient f y‖^2) x⟫_ℝ ∂μ) =
        2*(∫ x,⟪fderiv ℝ b x (gradient f x),gradient f x⟫_ℝ ∂μ) := by
      rw [← integral_const_mul,← integral_sub (hDG.const_mul 2) hDriftS,← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [real_inner_comm (gradient f x) (gradient D x)]
      exact DriftEnergyIdentity.drift_energy_integrand hf (hb.differentiable (by simp)) x
    have hr : (∫ x,⟪U x-gradient f x,gradient D x⟫_ℝ ∂μ) =
        (∫ x,⟪gradient D x,U x⟫_ℝ ∂μ)-(∫ x,⟪gradient D x,gradient f x⟫_ℝ ∂μ) := by
      have he : (fun x => ⟪U x-gradient f x,gradient D x⟫_ℝ) =
          fun x => ⟪gradient D x,U x⟫_ℝ-⟪gradient D x,gradient f x⟫_ℝ := by
        funext x
        rw [real_inner_comm,inner_sub_right]
      rw [he]
      exact integral_sub hDU hDG
    rw [hr]
    linarith
  have hDiff := solution_diffusion_identity μ a ha hB δ hδ U hBa Λ hΛ
  change 2*(∫ x,⟪gradient (PDEPairings.laplacian f) x,U x⟫_ℝ ∂μ)-_ = _ at hDiff
  have hgen : gradient (FiniteGeneratorCalculus.generator b f) =
      fun x => gradient (PDEPairings.laplacian f) x+gradient D x :=
    funext (gradient_fun_add ((smooth_laplacian hf).differentiable (by simp)) (hD.differentiable (by simp)))
  change 2*(∫ x,⟪gradient (FiniteGeneratorCalculus.generator b f) x,U x⟫_ℝ ∂μ)-_ = _
  simp_rw [hgen,inner_add_left]
  rw [integral_add hΔ hDU]
  change 2*((∫ x,⟪gradient (PDEPairings.laplacian f) x,U x⟫_ℝ ∂μ)+
    (∫ x,⟪gradient D x,U x⟫_ℝ ∂μ))-
    (∫ x,PDEPairings.laplacian (fun y => ‖gradient f y‖^2) x+
      ⟪b x,gradient (fun y => ‖gradient f y‖^2) x⟫_ℝ ∂μ) = _
  rw [integral_add hLapS hDriftS]
  linarith

end SharpWasserstein.FiniteGradientTrial
