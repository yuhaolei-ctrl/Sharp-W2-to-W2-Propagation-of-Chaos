import SharpWasserstein.PeriodicFourierPolynomials
import SharpWasserstein.PeriodicTorusBridge
import SharpWasserstein.TorusFourierConvergence

/-! Actual mean-square Fourier approximation on the periodic fundamental cube,
including simultaneous approximation of every first coordinate derivative. -/

noncomputable section
namespace SharpWasserstein.PeriodicFourierDensity
open MeasureTheory Filter PeriodicIntegrationByParts PeriodicFourierTests PeriodicFourierDerivative
open PeriodicFourierPolynomials PeriodicTorusBridge
open scoped ENNReal Topology BigOperators ContDiff

/-- The real part of the actual complex Fourier sum is the concrete real polynomial. -/
theorem series_re_toTorus {n : ℕ} (f : Coordinates n → ℝ) (hp : Periodic f) (hf : Continuous f)
    (s : Finset (Fin n → ℤ)) (x : Coordinates n) :
    (TorusFourierConvergence.series s (complexLift f hp hf) (toTorus x)).re = polynomial s f x := by
  rw [polynomial_eq_re]
  simp only [TorusFourierConvergence.series, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul, mFourierCoeff_complexLift, mFourier_toTorus_cosine_sine]

/-- Genuine real Fourier partial sums converge in square-integral on the cube. -/
theorem integral_polynomial_error_tendsto {n : ℕ} (f : Coordinates n → ℝ)
    (hp : Periodic f) (hf : Continuous f) :
    Tendsto (fun s => ∫ x, (polynomial s f x - f x) ^ 2 ∂cube n) atTop (𝓝 (0 : ℝ)) := by
  let F := complexLift f hp hf
  have ht := TorusFourierConvergence.integral_error_tendsto F
  change Tendsto (fun s => ∫ z, ‖TorusFourierConvergence.series s F z - F z‖ ^ 2 ∂haar n)
    atTop (𝓝 (0 : ℝ)) at ht
  have hc : Tendsto (fun s => ∫ x,
      ‖TorusFourierConvergence.series s F (toTorus x) - F (toTorus x)‖ ^ 2 ∂cube n)
      atTop (𝓝 (0 : ℝ)) := by
    convert ht using 1
    funext s
    exact integral_toTorus _
      (((TorusFourierConvergence.series s F).continuous.sub F.continuous).norm.pow 2).aestronglyMeasurable
  apply squeeze_zero (fun s => integral_nonneg fun _ => sq_nonneg _) _ hc
  intro s
  have hleft : Integrable (fun x => (polynomial s f x - f x) ^ 2) (cube n) :=
    continuous_integrable_cube (((smooth_polynomial s f).continuous.sub hf).pow 2)
  have hright : Integrable (fun x =>
      ‖TorusFourierConvergence.series s F (toTorus x) - F (toTorus x)‖ ^ 2) (cube n) :=
    continuous_integrable_cube
      ((((TorusFourierConvergence.series s F).continuous.sub F.continuous).norm.pow 2).comp
        (toTorus_continuous n))
  apply integral_mono hleft hright
  intro x
  have hre : (TorusFourierConvergence.series s F (toTorus x) - F (toTorus x)).re =
      polynomial s f x - f x := by
    rw [Complex.sub_re, series_re_toTorus, complexLift_toTorus, Complex.ofReal_re]
  dsimp only
  rw [← hre, Complex.sq_norm]
  simpa only [pow_two] using Complex.re_sq_le_normSq
    (TorusFourierConvergence.series s F (toTorus x) - F (toTorus x))

/-- For a `C¹` periodic potential, the same actual polynomials converge with each derivative. -/
theorem integral_derivative_error_tendsto {n : ℕ} (f : Coordinates n → ℝ)
    (hp : Periodic f) (hf : ContDiff ℝ 1 f) (i : Fin n) :
    Tendsto (fun s => ∫ x,
      (coordinatePartial (polynomial s f) i x - coordinatePartial f i x) ^ 2 ∂cube n)
      atTop (𝓝 (0 : ℝ)) := by
  simp_rw [coordinatePartial_polynomial_eq _ hf hp]
  exact integral_polynomial_error_tendsto (coordinatePartial f i)
    (periodic_coordinatePartial hp i) (continuous_coordinatePartial hf i)

end SharpWasserstein.PeriodicFourierDensity
