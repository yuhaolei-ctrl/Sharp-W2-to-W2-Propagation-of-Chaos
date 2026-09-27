import SharpWasserstein.WeightedPeriodicFourierAverage
import SharpWasserstein.PeriodicFourierDensity
import SharpWasserstein.PointwiseTrajectory

/-! Smoothing preserves actual finite Fourier trial spaces, and turns genuine
Haar square-integral approximation into uniform approximation. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff BigOperators InnerProductSpace
namespace SharpWasserstein.WeightedPeriodicFourier
open PeriodicIntegrationByParts PeriodicTorusBridge PeriodicPositiveKernel PeriodicConvolution
open PeriodicFourierTests PeriodicFourierPolynomials PeriodicFourierDensity
variable {n : ℕ}

theorem testAverage_add (κ : ℝ) {f g : Coordinates n → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    testAverage κ (f+g) = testAverage κ f + testAverage κ g := by
  funext y
  simp only [testAverage, Pi.add_apply, mul_add]
  exact integral_add
    (continuous_integrable_cube ((kernel_smooth n κ).continuous.mul
      (hf.comp (continuous_const.add continuous_id))))
    (continuous_integrable_cube ((kernel_smooth n κ).continuous.mul
      (hg.comp (continuous_const.add continuous_id))))

theorem testAverage_smul (κ c : ℝ) (f : Coordinates n → ℝ) :
    testAverage κ (c • f) = c • testAverage κ f := by
  funext y
  simp only [testAverage, Pi.smul_apply, smul_eq_mul]
  simp_rw [show ∀ z, kernel κ z * (c*f (y+z)) = c*(kernel κ z*f (y+z)) by intro z; ring]
  exact integral_const_mul c _

theorem testAverage_sub (κ : ℝ) {f g : Coordinates n → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    testAverage κ (f-g) = testAverage κ f - testAverage κ g := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ g, testAverage_add κ hf (hg.const_smul _),
    testAverage_smul, neg_one_smul, ← sub_eq_add_neg]

theorem testAverage_cosine (κ : ℝ) (k : Fin n → ℤ) :
    testAverage κ (cosine k) =
      (∫ z, kernel κ z*cosine k z ∂cube n) • cosine k +
        (-(∫ z, kernel κ z*sine k z ∂cube n)) • sine k := by
  funext y
  have hc := continuous_integrable_cube ((kernel_smooth n κ).continuous.mul (smooth_cosine k).continuous)
  have hs := continuous_integrable_cube ((kernel_smooth n κ).continuous.mul (smooth_sine k).continuous)
  change Integrable (fun z => kernel κ z * Real.cos (phase k z)) (cube n) at hc
  change Integrable (fun z => kernel κ z * Real.sin (phase k z)) (cube n) at hs
  simp only [testAverage, cosine, sine, map_add, Real.cos_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [show ∀ z, kernel κ z*(Real.cos (phase k y)*Real.cos (phase k z)-
      Real.sin (phase k y)*Real.sin (phase k z)) =
      Real.cos (phase k y)*(kernel κ z*Real.cos (phase k z))-
        Real.sin (phase k y)*(kernel κ z*Real.sin (phase k z)) by intro z; ring]
  rw [integral_sub (hc.const_mul _) (hs.const_mul _), integral_const_mul, integral_const_mul]
  ring

theorem testAverage_sine (κ : ℝ) (k : Fin n → ℤ) :
    testAverage κ (sine k) =
      (∫ z, kernel κ z*sine k z ∂cube n) • cosine k +
        (∫ z, kernel κ z*cosine k z ∂cube n) • sine k := by
  funext y
  have hc := continuous_integrable_cube ((kernel_smooth n κ).continuous.mul (smooth_cosine k).continuous)
  have hs := continuous_integrable_cube ((kernel_smooth n κ).continuous.mul (smooth_sine k).continuous)
  change Integrable (fun z => kernel κ z * Real.cos (phase k z)) (cube n) at hc
  change Integrable (fun z => kernel κ z * Real.sin (phase k z)) (cube n) at hs
  simp only [testAverage, cosine, sine, map_add, Real.sin_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [show ∀ z, kernel κ z*(Real.sin (phase k y)*Real.cos (phase k z)+
      Real.cos (phase k y)*Real.sin (phase k z)) =
      Real.sin (phase k y)*(kernel κ z*Real.cos (phase k z))+
        Real.cos (phase k y)*(kernel κ z*Real.sin (phase k z)) by intro z; ring]
  rw [integral_add (hc.const_mul _) (hs.const_mul _), integral_const_mul, integral_const_mul]
  ring

theorem testAverage_frequencySpace (κ : ℝ) (s : Finset (Fin n → ℤ))
    {f : Coordinates n → ℝ} (hf : f ∈ frequencySpace (frequencySet s)) :
    testAverage κ f ∈ frequencySpace (frequencySet s) := by
  classical
  have hboth (k : Fin n → ℤ) (hk : k ∈ s) :
      cosine k ∈ frequencySpace (frequencySet s) ∧ sine k ∈ frequencySpace (frequencySet s) := by
    constructor
    · exact Submodule.subset_span ⟨(k,false), Finset.mem_product.mpr ⟨hk,Finset.mem_univ _⟩,rfl⟩
    · exact Submodule.subset_span ⟨(k,true), Finset.mem_product.mpr ⟨hk,Finset.mem_univ _⟩,rfl⟩
  have h : Continuous f ∧ testAverage κ f ∈ frequencySpace (frequencySet s) := by
    induction hf using Submodule.span_induction with
    | mem f hf =>
        rcases hf with ⟨⟨k,c⟩,hk,rfl⟩
        have hb := hboth k (Finset.mem_product.mp hk).1
        refine ⟨(smooth_atom _).continuous,?_⟩
        cases c
        · change testAverage κ (cosine k) ∈ _
          rw [testAverage_cosine]
          exact Submodule.add_mem _ (Submodule.smul_mem _ _ hb.1) (Submodule.smul_mem _ _ hb.2)
        · change testAverage κ (sine k) ∈ _
          rw [testAverage_sine]
          exact Submodule.add_mem _ (Submodule.smul_mem _ _ hb.1) (Submodule.smul_mem _ _ hb.2)
    | zero =>
        refine ⟨continuous_const,?_⟩
        have hz : testAverage κ (0 : Coordinates n → ℝ) = 0 := by
          funext y
          simp [testAverage]
        rw [hz]
        exact (frequencySpace (frequencySet s)).zero_mem
    | add f g _ _ hf hg =>
        refine ⟨hf.1.add hg.1,?_⟩
        rw [testAverage_add κ hf.1 hg.1]
        exact Submodule.add_mem _ hf.2 hg.2
    | smul c f _ hf =>
        refine ⟨hf.1.const_smul c,?_⟩
        rw [testAverage_smul]
        exact Submodule.smul_mem _ _ hf.2
  exact h.2

theorem continuous_memLp_two_cube {g : Coordinates n → ℝ} (hg : Continuous g) :
    MemLp g 2 (cube n) :=
  (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mpr
    (continuous_integrable_cube (hg.norm.pow 2))

theorem testAverage_eq_shifted (κ : ℝ) {f : Coordinates n → ℝ}
    (hp : Periodic f) (hf : Continuous f) (y : Coordinates n) :
    testAverage κ f y = ∫ x, kernel κ (x-y)*f x ∂cube n := by
  change testAverage κ f y = ∫ x, kernel κ (x-y) • f x ∂cube n
  rw [integral_kernel_translate hp hf]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by simp [add_comm, smul_eq_mul]

theorem testAverage_abs_le_L2 (κ : ℝ) {f : Coordinates n → ℝ}
    (hp : Periodic f) (hf : Continuous f) (y : Coordinates n) :
    |testAverage κ f y| ≤ (Real.exp |κ| / normalizer κ)^n *
      Real.sqrt (∫ x, (f x)^2 ∂cube n) := by
  let B : ℝ := (Real.exp |κ| / normalizer κ)^n
  have hB : 0 ≤ B := pow_nonneg (div_pos (Real.exp_pos _) (normalizer_pos κ)).le _
  have hK : Continuous (fun x : Coordinates n => kernel κ (x-y)) :=
    (kernel_smooth n κ).continuous.comp (continuous_id.sub continuous_const)
  have hK2 := continuous_memLp_two_cube hK
  have hf2 := continuous_memLp_two_cube hf
  have hc := (norm_integral_le_integral_norm
    (fun x => ⟪kernel κ (x-y), f x⟫_ℝ)).trans
      (PointwiseTrajectory.integral_norm_inner_le hK2 hf2)
  rw [PointwiseTrajectory.norm_toLp_two_eq_sqrt hK2,
    PointwiseTrajectory.norm_toLp_two_eq_sqrt hf2] at hc
  simp only [Real.inner_apply, Real.norm_eq_abs, sq_abs] at hc
  have hsq : (∫ x, (kernel κ (x-y))^2 ∂cube n) ≤ B^2 := by
    calc
      _ ≤ ∫ _ : Coordinates n, B^2 ∂cube n :=
        integral_mono (continuous_integrable_cube (hK.pow 2)) (integrable_const _) fun x =>
          pow_le_pow_left₀ (kernel_pos κ (x-y)).le (kernel_bounds κ (x-y)).2 2
      _ = B^2 := by simp
  rw [testAverage_eq_shifted κ hp hf]
  calc
    _ ≤ Real.sqrt (∫ x, (kernel κ (x-y))^2 ∂cube n) * Real.sqrt (∫ x, (f x)^2 ∂cube n) := by
      simpa only [mul_comm] using hc
    _ ≤ B * Real.sqrt (∫ x, (f x)^2 ∂cube n) := by
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      exact (Real.sqrt_le_sqrt hsq).trans_eq (Real.sqrt_sq hB)

end SharpWasserstein.WeightedPeriodicFourier
