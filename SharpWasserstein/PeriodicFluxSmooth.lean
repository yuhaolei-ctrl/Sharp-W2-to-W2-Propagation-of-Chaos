module

public import SharpWasserstein.Compat
public import SharpWasserstein.WeightedConvolutionSmooth
public import SharpWasserstein.PeriodicFluxContraction
public import SharpWasserstein.PeriodicDriftEnergy

@[expose] public section

/-! Actual C∞ regularization of arbitrary integrable fluxes by the periodic
product kernel, with the derivative given by differentiation of that kernel.
Neither the law nor the original flux is assumed to have a density or to be smooth. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace SharpWasserstein.PeriodicConvolution
open PeriodicIntegrationByParts PeriodicPositiveKernel NoiseAverage WeightedConvolution
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (κ : ℝ) (μ : Measure (Coordinates n))

/-- The actual periodic flux is smooth for every integrable original flux,
even when the underlying measure is not finite. -/
theorem flux_smooth_of_integrable {v : Coordinates n → E} (hv : Integrable v μ) :
    ContDiff ℝ ∞ (flux κ μ v) := by
  have hW : Integrable (fun y => ContinuousLinearMap.toSpanSingleton ℝ (v y)) μ :=
    (ContinuousLinearMap.toSpanSingletonLIE ℝ E).integrable_comp_iff.mpr hv
  have hh := contDiff_infty_operatorAverage μ (fun y : Coordinates n => -y)
    continuous_neg.stronglyMeasurable hW (kernel_smooth n κ) (kernel_derivatives_bounded n κ)
  convert hh using 1
  funext x
  simp only [flux,operatorAverage,ContinuousLinearMap.toSpanSingleton_apply,sub_eq_add_neg]

/-- The genuine Fréchet derivative is the integral of the differentiated
kernel against the original vector flux. -/
theorem hasFDerivAt_flux_of_integrable {v : Coordinates n → E} (hv : Integrable v μ)
    (x : Coordinates n) : HasFDerivAt (flux κ μ v)
      (∫ y,(fderiv ℝ (kernel (n := n) κ) (x-y)).smulRight (v y) ∂μ) x := by
  have hW : Integrable (fun y => ContinuousLinearMap.toSpanSingleton ℝ (v y)) μ :=
    (ContinuousLinearMap.toSpanSingletonLIE ℝ E).integrable_comp_iff.mpr hv
  have hB : AllDerivativesBounded (kernel (n := n) κ) := kernel_derivatives_bounded n κ
  obtain ⟨C,_,hC⟩ := hB.bounded
  obtain ⟨D,_,hD⟩ := hB.fderiv.bounded
  have hh := hasFDerivAt_operatorAverage μ (fun y : Coordinates n => -y)
    continuous_neg.stronglyMeasurable hW
    ((kernel_smooth n κ).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)) hC hD x
  convert hh using 1 <;> try rfl

theorem fderiv_flux_of_integrable {v : Coordinates n → E} (hv : Integrable v μ)
    (x : Coordinates n) : fderiv ℝ (flux κ μ v) x =
      ∫ y,(fderiv ℝ (kernel (n := n) κ) (x-y)).smulRight (v y) ∂μ :=
  (hasFDerivAt_flux_of_integrable κ μ hv x).fderiv

/-- Every derivative of the actual convolved flux is globally bounded. -/
theorem allDerivativesBounded_flux_of_integrable {v : Coordinates n → E} (hv : Integrable v μ) :
    ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ m (flux κ μ v) x‖ ≤ C :=
  PeriodicSmoothBounds.iteratedFDeriv_bound (flux_periodic κ μ v) (flux_smooth_of_integrable κ μ hv)

/-- The actual source obtained by regularizing an integrable vector flux. -/
def fluxSource (v : Coordinates n → Coordinates n) (x : Coordinates n) : ℝ :=
  -PeriodicDriftEnergy.divergence (flux κ μ v) x

theorem fluxSource_smooth_of_integrable {v : Coordinates n → Coordinates n} (hv : Integrable v μ) :
    ContDiff ℝ ∞ (fluxSource κ μ v) := by
  exact (ContDiff.sum fun i _ => PeriodicFourierTests.smooth_coordinatePartial
    ((contDiff_pi.mp (flux_smooth_of_integrable κ μ hv)) i) i).neg

theorem fluxSource_periodic (v : Coordinates n → Coordinates n) : Periodic (fluxSource κ μ v) := by
  have hp (i : Fin n) : Periodic (fun x => flux κ μ v x i) := fun j x =>
    congrFun (flux_periodic κ μ v j x) i
  intro j x
  unfold fluxSource PeriodicDriftEnergy.divergence
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact periodic_coordinatePartial (hp i) i j x

/-- The smoothed negative divergence represents the genuine flux pairing
against every C¹ periodic scalar test. -/
theorem integral_fluxSource_mul {v : Coordinates n → Coordinates n} (hv : Integrable v μ)
    {φ : Coordinates n → ℝ} (hφ : ContDiff ℝ 1 φ) (hpφ : Periodic φ) :
    (∫ x,fluxSource κ μ v x*φ x ∂cube n) =
      ∫ x,PeriodicDriftEnergy.drift (flux κ μ v) φ x ∂cube n := by
  have hp (i : Fin n) : Periodic (fun x => flux κ μ v x i) := fun j x =>
    congrFun (flux_periodic κ μ v j x) i
  simp only [fluxSource,neg_mul,integral_neg]
  rw [PeriodicDriftEnergy.integral_divergence_mul
    ((flux_smooth_of_integrable κ μ hv).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1))
    hp hφ hpφ,neg_neg]

/-- Conservation of mass is an exact consequence of periodic integration by
parts; it is not a separate compatibility premise on the smoothed source. -/
theorem integral_fluxSource_eq_zero {v : Coordinates n → Coordinates n} (hv : Integrable v μ) :
    (∫ x,fluxSource κ μ v x ∂cube n) = 0 := by
  have hh := integral_fluxSource_mul κ μ hv (φ := fun _ => 1) contDiff_const (fun _ _ => rfl)
  simpa [PeriodicDriftEnergy.drift,coordinatePartial] using hh

theorem allDerivativesBounded_fluxSource_of_integrable {v : Coordinates n → Coordinates n}
    (hv : Integrable v μ) : AllDerivativesBounded (fluxSource κ μ v) :=
  PeriodicSmoothBounds.iteratedFDeriv_bound (fluxSource_periodic κ μ v)
    (fluxSource_smooth_of_integrable κ μ hv)

/-- The actual velocity representing the smooth flux is itself smooth once
the convolved probability density supplies its proved positive denominator. -/
theorem fluxVelocity_smooth_of_integrable [IsProbabilityMeasure μ]
    {v : Coordinates n → E} (hv : Integrable v μ) : ContDiff ℝ ∞ (fluxVelocity κ μ v) :=
  ((density_smooth κ μ).inv (fun x => (density_pos κ μ x).ne')).smul
    (flux_smooth_of_integrable κ μ hv)

end SharpWasserstein.PeriodicConvolution
