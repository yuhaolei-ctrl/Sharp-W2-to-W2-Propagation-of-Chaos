import SharpWasserstein.PeriodicConvolutionMarginal
import SharpWasserstein.PeriodicConvolutionApproximation
import SharpWasserstein.PeriodicFluxPairing
import SharpWasserstein.WeightedMarginal

/-! Product-kernel averaging of actual cylinder tests commutes with prefix
projection and Euclidean zero-extension. These identities preserve genuine
marginal source pairings under convolution. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology InnerProductSpace
namespace SharpWasserstein.PeriodicConvolution
open PeriodicIntegrationByParts PeriodicPositiveKernel WeightedTangent WeightedMarginal
variable {n m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [SecondCountableTopology E]

/-- Integrating out the genuine product-kernel suffix leaves precisely the
lower-dimensional test convolution. -/
theorem integral_kernel_prefix {F : Coordinates n → E} (hF : Continuous F)
    {C : ℝ} (hC : ∀ x, ‖F x‖ ≤ C)
    (κ : ℝ) (y : Coordinates (n+m)) :
    (∫ x, kernel κ (x-y) • F (prefixCoords n m x) ∂cube (n+m)) =
      ∫ x, kernel κ (x-prefixCoords n m y) • F x ∂cube n := by
  let g : Coordinates (n+m) → E := fun x => kernel κ (x-y) • F (prefixCoords n m x)
  have hg : Continuous g := ((kernel_smooth (n+m) κ).continuous.comp
    (continuous_id.sub continuous_const)).smul (hF.comp (prefix_continuous n m))
  have hmp := (splitCoordinates_measurePreserving n m).symm
  have hi : Integrable (fun p => g ((splitCoordinates n m).symm p)) ((cube n).prod (cube m)) :=
    (hmp.integrable_comp hg.aestronglyMeasurable).mpr
      (weighted_test_integrable (hF.comp (prefix_continuous n m)) (fun x => hC _) κ y)
  calc
    _ = ∫ p, g ((splitCoordinates n m).symm p) ∂(cube n).prod (cube m) :=
      (hmp.integral_comp' g).symm
    _ = ∫ x, ∫ z, g ((splitCoordinates n m).symm (x,z)) ∂cube m ∂cube n := integral_prod _ hi
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        simp only [g,kernel_split,prefix_sub,suffix_sub,prefix_splitCoordinates_symm,suffix_splitCoordinates_symm]
        simp_rw [mul_comm (kernel κ (x-prefixCoords n m y)),mul_smul]
        rw [integral_smul_const,integral_cube_sub (kernel_periodic m κ)
          (kernel_smooth m κ).continuous,kernel_integral,one_smul]

/-- Actual Euclidean zero-extension also commutes with product-kernel
averaging; no sup-norm identification is used. -/
theorem integral_kernel_prefixEmbedding {F : Coordinates n → Point n} (hF : Continuous F)
    {C : ℝ} (hC : ∀ x, ‖F x‖ ≤ C)
    (κ : ℝ) (y : Coordinates (n+m)) :
    (∫ x, kernel κ (x-y) • prefixEmbedding n m (F (prefixCoords n m x)) ∂cube (n+m)) =
      prefixEmbedding n m (∫ x, kernel κ (x-prefixCoords n m y) • F x ∂cube n) := by
  have hi : Integrable (fun x => kernel κ (x-y) • F (prefixCoords n m x)) (cube (n+m)) :=
    weighted_test_integrable (hF.comp (prefix_continuous n m)) (fun x => hC _) κ y
  calc
    _ = prefixEmbedding n m (∫ x, kernel κ (x-y) • F (prefixCoords n m x) ∂cube (n+m)) := by
      convert (prefixEmbedding n m).toContinuousLinearMap.integral_comp_comm hi using 1
      · apply integral_congr_ae
        exact Eventually.of_forall fun x => (map_smul (prefixEmbedding n m) _ _).symm
      · rfl
    _ = _ := congrArg (prefixEmbedding n m) (integral_kernel_prefix hF hC κ y)

/-- The actual full convolved flux tested against a prefix cylinder field
is the original prefix-flux pairing with the lower-dimensional convolution. -/
theorem integral_inner_flux_prefix (κ : ℝ) (μ : Measure (Coordinates (n+m))) [IsProbabilityMeasure μ]
    {v : Coordinates (n+m) → Point (n+m)} (hv : Integrable v μ)
    {F : Coordinates n → Point n} (hF : Continuous F) {C : ℝ} (hC : ∀ x, ‖F x‖ ≤ C) :
    (∫ x, ⟪prefixEmbedding n m (F (prefixCoords n m x)),flux κ μ v x⟫_ℝ ∂cube (n+m)) =
      ∫ y, ⟪∫ x, kernel κ (x-prefixCoords n m y) • F x ∂cube n,
        prefixProjection n m (v y)⟫_ℝ ∂μ := by
  have hc := (prefixEmbedding n m).continuous.comp (hF.comp (prefix_continuous n m))
  change Continuous (fun x => prefixEmbedding n m (F (prefixCoords n m x))) at hc
  have hb (x : Coordinates (n+m)) : ‖prefixEmbedding n m (F (prefixCoords n m x))‖ ≤ C := by
    rw [LinearIsometry.norm_map]
    exact hC _
  rw [integral_inner_flux κ μ hv hc hb]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    dsimp only
    rw [integral_kernel_prefixEmbedding hF hC κ y,inner_prefixEmbedding]

end SharpWasserstein.PeriodicConvolution
