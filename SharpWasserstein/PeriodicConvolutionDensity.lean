import SharpWasserstein.PeriodicPositiveKernel
import SharpWasserstein.NoiseAverageSmooth
import Mathlib.MeasureTheory.Group.Integral

/-! Actual strictly positive smooth periodic convolution densities for every
probability law, including singular laws. Normalization is an exact Fubini
and Haar-translation calculation, not an assumed density representation. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal ContDiff
namespace SharpWasserstein.PeriodicConvolution
open PeriodicIntegrationByParts PeriodicTorusBridge PeriodicPositiveKernel

theorem toTorus_sub {n : ℕ} (x y : Coordinates n) : toTorus (x-y) = toTorus x-toTorus y := by
  ext i
  exact AddCircle.coe_sub 1 (x i) (y i)

theorem integral_cube_sub {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [SecondCountableTopology F] {f : Coordinates n → F}
    (hp : ∀ i, Function.Periodic f (Pi.single i 1)) (hf : Continuous f) (y : Coordinates n) :
    (∫ x, f (x-y) ∂cube n) = ∫ x, f x ∂cube n := by
  have hc : Continuous (fun z => lift f (z-toTorus y)) :=
    (lift_continuous hp hf).comp (continuous_id.sub continuous_const)
  calc
    _ = ∫ x, lift f (toTorus x-toTorus y) ∂cube n := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by
        change f (x-y) = lift f (toTorus x-toTorus y)
        rw [← toTorus_sub,lift_toTorus hp])
    _ = ∫ z, lift f (z-toTorus y) ∂haar n := integral_toTorus _ hc.aestronglyMeasurable
    _ = ∫ z, lift f z ∂haar n := by
      rw [← torus_volume_eq_haar]
      exact integral_sub_right_eq_self _ _
    _ = _ := integral_lift hp hf

def density {n : ℕ} (κ : ℝ) (μ : Measure (Coordinates n)) (x : Coordinates n) : ℝ :=
  ∫ y, kernel κ (x-y) ∂μ

theorem kernel_translate_integrable {n : ℕ} (κ : ℝ) (μ : Measure (Coordinates n))
    [IsProbabilityMeasure μ] (x : Coordinates n) : Integrable (fun y => kernel κ (x-y)) μ := by
  apply Integrable.of_bound ((kernel_smooth n κ).continuous.comp
    (continuous_const.sub continuous_id)).aestronglyMeasurable ((Real.exp |κ|/normalizer κ)^n)
  exact Eventually.of_forall (fun y => by
    change ‖kernel κ (x-y)‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_pos (kernel_pos κ (x-y))]
    exact (kernel_bounds κ (x-y)).2)

theorem density_bounds {n : ℕ} (κ : ℝ) (μ : Measure (Coordinates n))
    [IsProbabilityMeasure μ] (x : Coordinates n) :
    (Real.exp (-|κ|)/normalizer κ)^n ≤ density κ μ x ∧
      density κ μ x ≤ (Real.exp |κ|/normalizer κ)^n := by
  constructor
  · have h := integral_mono (integrable_const ((Real.exp (-|κ|)/normalizer κ)^n))
      (kernel_translate_integrable κ μ x) (fun y => (kernel_bounds κ (x-y)).1)
    simpa only [integral_const,probReal_univ,one_smul,density] using h
  · have h := integral_mono (kernel_translate_integrable κ μ x)
      (integrable_const ((Real.exp |κ|/normalizer κ)^n)) (fun y => (kernel_bounds κ (x-y)).2)
    simpa only [integral_const,probReal_univ,one_smul,density] using h

theorem density_pos {n : ℕ} (κ : ℝ) (μ : Measure (Coordinates n))
    [IsProbabilityMeasure μ] (x : Coordinates n) : 0 < density κ μ x :=
  (pow_pos (div_pos (Real.exp_pos _) (normalizer_pos κ)) n).trans_le (density_bounds κ μ x).1

theorem density_periodic {n : ℕ} (κ : ℝ) (μ : Measure (Coordinates n)) : Periodic (density κ μ) := by
  intro i x
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  have he : (x+Pi.single i 1)-y = (x-y)+Pi.single i 1 := by abel
  change kernel κ ((x+Pi.single i 1)-y) = kernel κ (x-y)
  rw [he,kernel_periodic n κ i]

theorem density_smooth {n : ℕ} (κ : ℝ) (μ : Measure (Coordinates n)) [IsProbabilityMeasure μ] :
    ContDiff ℝ ∞ (density κ μ) := by
  have h := NoiseAverage.contDiff_infty_average μ (fun y : Coordinates n => -y)
    continuous_neg.stronglyMeasurable (kernel_smooth n κ) (kernel_derivatives_bounded n κ)
  convert h using 1
  funext x
  simp only [density,NoiseAverage.average,sub_eq_add_neg]

theorem density_derivatives_bounded {n : ℕ} (κ : ℝ) (μ : Measure (Coordinates n)) [IsProbabilityMeasure μ]
    (m : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ m (density κ μ) x‖ ≤ C :=
  PeriodicSmoothBounds.iteratedFDeriv_bound (density_periodic κ μ) (density_smooth κ μ) m

theorem density_integral {n : ℕ} (κ : ℝ) (μ : Measure (Coordinates n)) [IsProbabilityMeasure μ] :
    (∫ x, density κ μ x ∂cube n) = 1 := by
  have hi : Integrable (fun p : Coordinates n × Coordinates n => kernel κ (p.1-p.2))
      ((cube n).prod μ) := by
    apply Integrable.of_bound ((kernel_smooth n κ).continuous.comp
      (continuous_fst.sub continuous_snd)).aestronglyMeasurable ((Real.exp |κ|/normalizer κ)^n)
    exact Eventually.of_forall (fun p => by
      change ‖kernel κ (p.1-p.2)‖ ≤ _
      rw [Real.norm_eq_abs,abs_of_pos (kernel_pos κ (p.1-p.2))]
      exact (kernel_bounds κ (p.1-p.2)).2)
  change (∫ x, ∫ y, kernel κ (x-y) ∂μ ∂cube n) = 1
  rw [integral_integral_swap hi]
  simp_rw [integral_cube_sub (kernel_periodic n κ) (kernel_smooth n κ).continuous,kernel_integral]
  simp

def smoothLaw {n : ℕ} (κ : ℝ) (μ : Measure (Coordinates n)) : Measure (Coordinates n) :=
  (cube n).withDensity (fun x => ENNReal.ofReal (density κ μ x))

theorem smoothLaw_probability {n : ℕ} (κ : ℝ) (μ : Measure (Coordinates n)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (smoothLaw κ μ) := by
  apply isProbabilityMeasure_iff.mpr
  rw [smoothLaw,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal
      (continuous_integrable_cube (density_smooth κ μ).continuous)
      (Eventually.of_forall (fun x => (density_pos κ μ x).le)),density_integral]
  exact ENNReal.ofReal_one

end SharpWasserstein.PeriodicConvolution
