import SharpWasserstein.PeriodicConvolutionPrefixTests
import SharpWasserstein.PeriodicFluxEuclidean
import SharpWasserstein.WeightedGradientApproximation

/-! Averaging a genuine periodic scalar potential gives a genuine bounded
smooth potential whose Euclidean gradient is the averaged gradient. This
allows source marginal consistency to be used after convolution. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace
namespace SharpWasserstein.PeriodicConvolution
open PeriodicIntegrationByParts PeriodicPositiveKernel PeriodicBochner
open WeightedConvolution WeightedTangent
variable {n : ℕ}

def testAverage (κ : ℝ) (f : Coordinates n → ℝ) (y : Coordinates n) : ℝ :=
  ∫ z, kernel κ z * f (y+z) ∂cube n

theorem testAverage_eq_operatorAverage (κ : ℝ) (f : Coordinates n → ℝ) :
    testAverage κ f = operatorAverage (cube n) (fun z => z)
      (fun z => ContinuousLinearMap.toSpanSingleton ℝ (kernel κ z)) f := by
  funext y
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    simp only [ContinuousLinearMap.toSpanSingleton_apply,smul_eq_mul,mul_comm]

theorem testAverage_smooth (κ : ℝ) {f : Coordinates n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Periodic f) : ContDiff ℝ ∞ (testAverage κ f) := by
  rw [testAverage_eq_operatorAverage]
  apply contDiff_infty_operatorAverage (cube n) (fun z => z) stronglyMeasurable_id
    ((ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).integrable_comp_iff.mpr
      (continuous_integrable_cube (kernel_smooth n κ).continuous)) hf
  exact PeriodicSmoothBounds.iteratedFDeriv_bound hp hf

theorem testAverage_periodic (κ : ℝ) {f : Coordinates n → ℝ}
    (hp : Periodic f) : Periodic (testAverage κ f) := by
  intro i y
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    dsimp only
    rw [show y+Pi.single i 1+z = y+z+Pi.single i 1 by abel,hp i]

theorem testAverage_fderiv (κ : ℝ) {f : Coordinates n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Periodic f) (y : Coordinates n) :
    fderiv ℝ (testAverage κ f) y =
      ∫ z, kernel κ z • fderiv ℝ f (y+z) ∂cube n := by
  obtain ⟨C,_,hC⟩ := PeriodicSmoothBounds.norm_bound hp hf.continuous
  obtain ⟨D,_,hD⟩ := PeriodicSmoothBounds.norm_bound
    (PeriodicSmoothBounds.periodic_fderiv hp) (hf.continuous_fderiv (by simp))
  rw [testAverage_eq_operatorAverage]
  have hh := (hasFDerivAt_operatorAverage (cube n) (fun z => z) stronglyMeasurable_id
    ((ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).integrable_comp_iff.mpr
      (continuous_integrable_cube (kernel_smooth n κ).continuous))
    (hf.of_le (by simp)) hC hD y).fderiv
  convert hh using 1
  · rfl
  · apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      ext v
      change kernel κ z * fderiv ℝ f (y+z) v = fderiv ℝ f (y+z) v * kernel κ z
      ring

theorem testAverage_coordinatePartial (κ : ℝ) {f : Coordinates n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Periodic f) (y : Coordinates n) (i : Fin n) :
    coordinatePartial (testAverage κ f) i y =
      ∫ z, kernel κ z * coordinatePartial f i (y+z) ∂cube n := by
  obtain ⟨D,_,hD⟩ := PeriodicSmoothBounds.norm_bound
    (PeriodicSmoothBounds.periodic_fderiv hp) (hf.continuous_fderiv (by simp))
  have hi : Integrable (fun z => kernel κ z • fderiv ℝ f (y+z)) (cube n) :=
    (continuous_integrable_cube (kernel_smooth n κ).continuous).smul_bdd D
      (((hf.continuous_fderiv (by simp)).comp
        (continuous_const.add continuous_id)).aestronglyMeasurable)
      (Eventually.of_forall fun z => hD _)
  rw [coordinatePartial,testAverage_fderiv κ hf hp,ContinuousLinearMap.integral_apply hi]
  rfl

theorem testAverage_euclideanGradient (κ : ℝ) {f : Coordinates n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Periodic f) (y : Coordinates n) :
    euclideanGradient (testAverage κ f) y =
      ∫ x, kernel κ (x-y) • euclideanGradient f x ∂cube n := by
  rw [integral_kernel_translate (euclideanGradient_periodic hp) (euclideanGradient_continuous hf)]
  obtain ⟨D,_,hD⟩ := PeriodicSmoothBounds.norm_bound
    (euclideanGradient_periodic hp) (euclideanGradient_continuous hf)
  have hi : Integrable (fun z => kernel κ z • euclideanGradient f (z+y)) (cube n) :=
    (continuous_integrable_cube (kernel_smooth n κ).continuous).smul_bdd D
      (((euclideanGradient_continuous hf).comp
        (continuous_id.add continuous_const)).aestronglyMeasurable)
      (Eventually.of_forall fun z => hD _)
  ext i
  rw [euclideanGradient_apply,testAverage_coordinatePartial κ hf hp]
  have he := (EuclideanSpace.proj i : Point n →L[ℝ] ℝ).integral_comp_comm hi
  convert he using 1
  · apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      change kernel κ z * coordinatePartial f i (y+z) =
        kernel κ z * euclideanGradient f (z+y) i
      rw [euclideanGradient_apply,add_comm y z]
  · rfl

end SharpWasserstein.PeriodicConvolution
