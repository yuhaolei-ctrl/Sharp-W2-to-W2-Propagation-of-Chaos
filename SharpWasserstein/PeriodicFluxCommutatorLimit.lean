import SharpWasserstein.PeriodicFluxCommutator
import SharpWasserstein.PeriodicCommutatorLimit

/-! Vanishing weighted quadratic action of the actual coefficient/flux
commutator for every finite-energy original vector measure. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SharpWasserstein.PeriodicConvolution
open PeriodicIntegrationByParts PeriodicPositiveKernel
variable {n : ℕ} {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  (μ : Measure (Coordinates n)) [IsProbabilityMeasure μ]

omit [CompleteSpace E] [CompleteSpace F] in
theorem coefficient_flux_difference_joint_integrable {A : Coordinates n → E →L[ℝ] F}
    (hA : Continuous A) {M : ℝ} (hM : ∀ x, ‖A x‖ ≤ M)
    {v : Coordinates n → E} (hv₂ : Integrable (fun y => ‖v y‖^2) μ) (κ : ℝ) :
    Integrable (fun p : Coordinates n × Coordinates n =>
      kernel κ (p.1-p.2)*‖A p.2-A p.1‖^2*‖v p.2‖^2) ((cube n).prod μ) := by
  apply (hv₂.comp_snd (cube n)).bdd_mul
    ((((kernel_smooth n κ).continuous.comp (continuous_fst.sub continuous_snd)).mul
      (((hA.comp continuous_snd).sub (hA.comp continuous_fst)).norm.pow 2)).aestronglyMeasurable)
  exact Eventually.of_forall fun p => by
    change ‖kernel κ (p.1-p.2)*‖A p.2-A p.1‖^2‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (kernel_pos κ _).le (sq_nonneg _))]
    exact mul_le_mul (kernel_bounds κ _).2 (differenceSquare_bound hM p.1 p.2)
      (sq_nonneg _) (pow_nonneg (div_pos (Real.exp_pos _) (normalizer_pos κ)).le n)

omit [CompleteSpace E] [CompleteSpace F] in
/-- The real dominating integral tends to zero by approximate-identity
convergence and the original, integrable squared flux. -/
theorem integrated_coefficient_flux_difference_tendsto {A : Coordinates n → E →L[ℝ] F}
    (hp : ∀ i, Function.Periodic A (Pi.single i 1)) (hA : Continuous A)
    {v : Coordinates n → E} (hv₂ : Integrable (fun y => ‖v y‖^2) μ) :
    Tendsto (fun k : ℕ => ∫ x, ∫ y,
      kernel (k : ℝ) (x-y)*‖A y-A x‖^2*‖v y‖^2 ∂μ ∂cube n) atTop (𝓝 0) := by
  obtain ⟨M,_,hM⟩ := PeriodicSmoothBounds.norm_bound hp hA
  have he (k : ℕ) : (∫ x, ∫ y, kernel (k : ℝ) (x-y)*‖A y-A x‖^2*‖v y‖^2 ∂μ ∂cube n) =
      ∫ y, (∫ x, kernel (k : ℝ) (x-y)*‖A y-A x‖^2 ∂cube n)*‖v y‖^2 ∂μ := by
    rw [integral_integral_swap (coefficient_flux_difference_joint_integrable μ hA hM hv₂ k)]
    simp_rw [integral_mul_const]
  simp_rw [he]
  have hlim (y : Coordinates n) : Tendsto
      (fun k : ℕ => ∫ x, kernel (k : ℝ) (x-y)*‖A y-A x‖^2 ∂cube n) atTop (𝓝 0) := by
    have hpF : ∀ i, Function.Periodic (fun x => ‖A y-A x‖^2) (Pi.single i 1) := by
      intro i x
      change ‖A y-A (x+Pi.single i 1)‖^2 = _
      rw [hp i]
    simpa only [smul_eq_mul,sub_self,norm_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      integral_kernel_translate_tendsto hpF ((continuous_const.sub hA).norm.pow 2) y
  have h := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun k y => (∫ x, kernel (k : ℝ) (x-y)*‖A y-A x‖^2 ∂cube n)*‖v y‖^2)
    (f := fun _ => (0 : ℝ)) (fun y => (2*M)^2*‖v y‖^2)
    (fun k => ((differenceSquare_joint_integrable hA hM k μ).integral_prod_right.aestronglyMeasurable).mul
      hv₂.aestronglyMeasurable)
    (hv₂.const_mul _) ?_ ?_
  · simpa only [integral_zero] using h
  · intro k
    exact Eventually.of_forall fun y => by
      rw [norm_mul,Real.norm_eq_abs (‖v y‖^2),abs_of_nonneg (sq_nonneg _)]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact norm_weighted_test_integral_le ((continuous_const.sub hA).norm.pow 2)
        (fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]; exact differenceSquare_bound hM x y)
        k y
  · exact Eventually.of_forall fun y => by simpa using (hlim y).mul_const (‖v y‖^2)

/-- Actual source-flux commutators vanish in their natural weighted action;
there is no density lower bound uniform in the smoothing parameter. -/
theorem fluxCommutator_action_tendsto {A : Coordinates n → E →L[ℝ] F}
    (hp : ∀ i, Function.Periodic A (Pi.single i 1)) (hA : Continuous A)
    {v : Coordinates n → E} (hv : Integrable v μ)
    (hv₂ : Integrable (fun y => ‖v y‖^2) μ) :
    Tendsto (fun k : ℕ => ∫ x, ‖fluxCommutator (k : ℝ) μ A v x‖^2/density (k : ℝ) μ x ∂cube n)
      atTop (𝓝 0) := by
  obtain ⟨M,_,hM⟩ := PeriodicSmoothBounds.norm_bound hp hA
  apply squeeze_zero (fun k : ℕ => integral_nonneg fun x =>
    div_nonneg (sq_nonneg _) (density_pos k μ x).le) _
    (integrated_coefficient_flux_difference_tendsto μ hp hA hv₂)
  intro k
  exact integral_mono (fluxCommutator_action_integrable k μ hA hM hv)
    (coefficient_flux_difference_joint_integrable μ hA hM hv₂ k).integral_prod_left
    (fluxCommutator_action_le k μ hA hM hv hv₂)

end SharpWasserstein.PeriodicConvolution
