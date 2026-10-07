module

public import SharpWasserstein.Compat
public import SharpWasserstein.FiniteTrialEnergyEstimate

@[expose] public section

/-! The full finite coefficient energy inequality, retaining the negative
Hessian term and isolating all auxiliary drift-supremum dependence in the
true trial-energy gap. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace BigOperators
namespace SharpWasserstein.FiniteGradientTrial
open WeightedTangent NoiseAverage BochnerIdentity
variable {n : ℕ} [MeasurableSpace (Point n)] [BorelSpace (Point n)]
  (μ : Measure (Point n)) [IsFiniteMeasure μ]

theorem jacobian_integral_le {f : Point n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hBf : AllDerivativesBounded f)
    {b : Point n → Point n} (hb : ContDiff ℝ ∞ b) {L : ℝ}
    (hL : 0 ≤ L) (hbL : ∀ x,‖fderiv ℝ b x‖ ≤ L) :
    (∫ x,⟪fderiv ℝ b x (gradient f x),gradient f x⟫_ℝ ∂μ) ≤
      L*(∫ x,‖gradient f x‖^2 ∂μ) := by
  obtain ⟨B,hB,hBg⟩ := (WeightedPeriodicCoefficientEvolution.gradient_allDerivativesBounded hf hBf).bounded
  have hg := bounded_smooth_gradient_memLp μ f hf ⟨B,hBg⟩
  have hgs := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  have hi : Integrable (fun x => ⟪fderiv ℝ b x (gradient f x),gradient f x⟫_ℝ) μ := by
    apply Integrable.of_bound
      (((hb.continuous_fderiv (by simp)).clm_apply (smooth_gradient hf).continuous).inner
        (smooth_gradient hf).continuous).aestronglyMeasurable (L*B^2)
    exact Eventually.of_forall fun x => calc
      _ ≤ ‖fderiv ℝ b x (gradient f x)‖*‖gradient f x‖ := norm_inner_le_norm _ _
      _ ≤ (‖fderiv ℝ b x‖*‖gradient f x‖)*‖gradient f x‖ :=
        mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ (L*‖gradient f x‖)*‖gradient f x‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hbL x) (norm_nonneg _)) (norm_nonneg _)
      _ = L*‖gradient f x‖^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hBg x) 2) hL
  rw [← integral_const_mul]
  exact integral_mono hi (hgs.const_mul L) (fun x => DriftEnergyIdentity.jacobian_quadratic_le _ (hbL x) _)

variable {ι : Type*} [Fintype ι]
  (a : ι → Point n → ℝ) (ha : ∀ i,ContDiff ℝ ∞ (a i))
  (hB : ∀ i,∃ B : ℝ,∀ x,‖gradient (a i) x‖ ≤ B)

/-- Negative diffusion absorbs the finite residual Hessian before passage to
an infinite-dimensional limit. No uniform Hessian convergence is needed. -/
theorem solution_generator_le (δ : ℝ) (hδ : 0 < δ) (U : Lp (Point n) 2 μ)
    (hBa : ∀ i,AllDerivativesBounded (a i))
    (Λ : ι → ℝ) (hΛ : ∀ i x,PDEPairings.laplacian (a i) x = -Λ i*a i x)
    (hΛnonneg : ∀ i,0 ≤ Λ i)
    {b : Point n → Point n} (hb : ContDiff ℝ ∞ b) (hBb : AllDerivativesBounded b)
    {L M ε : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hbL : ∀ x,‖fderiv ℝ b x‖ ≤ L) (hbM : ∀ x,‖b x‖ ≤ M) (hε : 0 < ε) :
    let T := gradientMap μ a ha hB
    let c := RegularizedTrialEnergy.solution T δ U
    let f := potential a c
    2*(∫ x,⟪gradient (FiniteGeneratorCalculus.generator b f) x,U x⟫_ℝ ∂μ)-
      (∫ x,FiniteGeneratorCalculus.generator b (fun y => ‖gradient f y‖^2) x ∂μ) ≤
      (2*L+ε)*RegularizedTrialEnergy.energy T δ U-
        (2-ε)*(∫ x,HierarchyAlgebra.frobeniusSq (hessian f x) ∂μ)+
      (2*(L^2+M^2)/ε)*(‖U‖^2-RegularizedTrialEnergy.energy T δ U) := by
  dsimp only
  let T := gradientMap μ a ha hB
  let c := RegularizedTrialEnergy.solution T δ U
  let f := potential a c
  let E := RegularizedTrialEnergy.energy T δ U
  have hf := potential_smooth a ha c
  have hBf := potential_allDerivativesBounded a ha hBa c
  have hJ := jacobian_integral_le μ hf hBf hb hL hbL
  have hR := integral_drift_residual_le μ hf hBf hb hBb hL hM hbL hbM hε U
  have hGap := solution_residual_integral_le μ a ha hB δ hδ U
  have hC : 0 ≤ 2*(L^2+M^2)/ε := by positivity
  have hRgap := mul_le_mul_of_nonneg_left hGap hC
  have hE := RegularizedTrialEnergy.energy_eq_penalized_norm T δ hδ U
  rw [gradientMap_norm_sq μ a ha hB] at hE
  have hEg : (∫ x,‖gradient f x‖^2 ∂μ) ≤ E := by
    have hp : 0 ≤ δ*‖c‖^2 := mul_nonneg hδ.le (sq_nonneg _)
    change E = (∫ x,‖gradient f x‖^2 ∂μ)+δ*‖c‖^2 at hE
    linarith
  have hEg' := mul_le_mul_of_nonneg_left hEg (show 0 ≤ 2*L+ε by positivity)
  have hdiag : 0 ≤ 2*δ*(∑ i,Λ i*(c i)^2) :=
    mul_nonneg (by positivity) (Finset.sum_nonneg (fun i _ => mul_nonneg (hΛnonneg i) (sq_nonneg _)))
  rw [solution_generator_identity μ a ha hB δ hδ U hBa Λ hΛ hb hBb]
  change -2*(∫ x,HierarchyAlgebra.frobeniusSq (hessian f x) ∂μ)-2*δ*(∑ i,Λ i*(c i)^2)+
    2*(∫ x,⟪fderiv ℝ b x (gradient f x),gradient f x⟫_ℝ ∂μ)+
    2*(∫ x,⟪U x-gradient f x,gradient (fun y => ⟪b y,gradient f y⟫_ℝ) x⟫_ℝ ∂μ) ≤ _
  linarith

end SharpWasserstein.FiniteGradientTrial
