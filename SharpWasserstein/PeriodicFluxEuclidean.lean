module

public import SharpWasserstein.Compat
public import SharpWasserstein.PeriodicFluxSmooth
public import SharpWasserstein.PeriodicFluxPairing

@[expose] public section

/-! Euclidean identification of the periodic convolved source and its quadratic
action. Coordinate arrays carry a sup norm in Lean; every energy statement
here explicitly uses the genuine Euclidean vector conversion. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ContDiff
namespace SharpWasserstein.PeriodicConvolution
open PeriodicIntegrationByParts PeriodicPositiveKernel PeriodicBochner WeightedTangent
variable {n : ℕ} (κ : ℝ) (μ : Measure (Coordinates n))

theorem euclidean_flux_eq {v : Coordinates n → Coordinates n} (hv : Integrable v μ)
    (x : Coordinates n) :
    (coordinateEquiv n).symm (flux κ μ v x) =
      flux κ μ (fun y => (coordinateEquiv n).symm (v y)) x := by
  calc
    _ = ∫ y, (coordinateEquiv n).symm (kernel κ (x-y) • v y) ∂μ :=
      ((coordinateEquiv n).symm.toContinuousLinearMap.integral_comp_comm
        (kernel_smul_integrable_of_integrable κ μ hv x)).symm
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun y => map_smul (coordinateEquiv n).symm _ _

/-- The actual periodic gradient test in Euclidean coordinates. -/
def euclideanGradient (f : Coordinates n → ℝ) (x : Coordinates n) : Point n :=
  gradient (pullback f) ((coordinateEquiv n).symm x)

theorem euclideanGradient_apply (f : Coordinates n → ℝ) (x : Coordinates n) (i : Fin n) :
    euclideanGradient f x i = coordinatePartial f i x := by
  rw [euclideanGradient,← PDEPairings.directionDeriv_eq_gradient_component,directionDeriv_pullback,
    ContinuousLinearEquiv.apply_symm_apply]

theorem euclideanGradient_periodic {f : Coordinates n → ℝ} (hpf : Periodic f) :
    ∀ i, Function.Periodic (euclideanGradient f) (Pi.single i 1) := by
  intro i x
  ext j
  simp only [euclideanGradient_apply,periodic_coordinatePartial hpf j i x]

theorem euclideanGradient_continuous {f : Coordinates n → ℝ} (hf : ContDiff ℝ ∞ f) :
    Continuous (euclideanGradient f) :=
  (BochnerIdentity.smooth_gradient (hf.comp (coordinateEquiv n).contDiff)).continuous.comp
    (coordinateEquiv n).symm.continuous

/-- Source pairing is exactly the genuine Euclidean flux-gradient pairing. -/
theorem integral_fluxSource_euclidean {v : Coordinates n → Coordinates n} (hv : Integrable v μ)
    {f : Coordinates n → ℝ} (hf : ContDiff ℝ ∞ f) (hpf : Periodic f) :
    (∫ x, fluxSource κ μ v x*f x ∂cube n) =
      ∫ x, ⟪euclideanGradient f x,flux κ μ (fun y => (coordinateEquiv n).symm (v y)) x⟫_ℝ ∂cube n := by
  rw [integral_fluxSource_mul κ μ hv (hf.of_le (by simp)) hpf]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  dsimp only
  rw [← euclidean_flux_eq κ μ hv x]
  have he := PeriodicDriftEnergy.inner_vector_gradient_pullback (flux κ μ v) f ((coordinateEquiv n).symm x)
  simpa only [PeriodicDriftEnergy.vectorPullback,ContinuousLinearEquiv.apply_symm_apply,
    euclideanGradient,real_inner_comm] using he.symm

variable [IsProbabilityMeasure μ]

/-- The exact source duality uses the actual original finite vector measure. -/
theorem integral_fluxSource_convolved_test {v : Coordinates n → Coordinates n}
    (hv : Integrable v μ) {f : Coordinates n → ℝ} (hf : ContDiff ℝ ∞ f) (hpf : Periodic f) :
    (∫ x, fluxSource κ μ v x*f x ∂cube n) =
      ∫ y, ⟪∫ x, kernel κ (x-y) • euclideanGradient f x ∂cube n,
        (coordinateEquiv n).symm (v y)⟫_ℝ ∂μ := by
  obtain ⟨C,_,hC⟩ := PeriodicSmoothBounds.norm_bound
    (euclideanGradient_periodic hpf) (euclideanGradient_continuous hf)
  rw [integral_fluxSource_euclidean κ μ hv hf hpf]
  exact integral_inner_flux κ μ ((coordinateEquiv n).symm.toContinuousLinearMap.integrable_comp hv)
    (euclideanGradient_continuous hf) hC

/-- Removing the initial smoothing converges on every actual smooth periodic
source test, with no assumption of an original source density. -/
theorem integral_fluxSource_tendsto {v : Coordinates n → Coordinates n}
    (hv : Integrable v μ) {f : Coordinates n → ℝ} (hf : ContDiff ℝ ∞ f) (hpf : Periodic f) :
    Tendsto (fun m : ℕ => ∫ x, fluxSource (m : ℝ) μ v x*f x ∂cube n) atTop
      (𝓝 (∫ y, ⟪euclideanGradient f y,(coordinateEquiv n).symm (v y)⟫_ℝ ∂μ)) := by
  simp_rw [integral_fluxSource_euclidean _ μ hv hf hpf]
  exact integral_inner_flux_tendsto μ ((coordinateEquiv n).symm.toContinuousLinearMap.integrable_comp hv)
    (euclideanGradient_continuous hf) (euclideanGradient_periodic hpf)

/-- The actual Euclidean velocity action contracts with coefficient one.
No coordinate sup-norm is substituted for the manuscript's Euclidean norm. -/
theorem integral_euclidean_fluxVelocity_sq_le {v : Coordinates n → Coordinates n}
    (hv : Integrable v μ)
    (hv₂ : Integrable (fun y => ‖(coordinateEquiv n).symm (v y)‖^2) μ) :
    (∫ x, ‖(coordinateEquiv n).symm (fluxVelocity κ μ v x)‖^2 ∂smoothLaw κ μ) ≤
      ∫ y, ‖(coordinateEquiv n).symm (v y)‖^2 ∂μ := by
  have he (x : Coordinates n) :
      (coordinateEquiv n).symm (fluxVelocity κ μ v x) =
        fluxVelocity κ μ (fun y => (coordinateEquiv n).symm (v y)) x := by
    rw [fluxVelocity,map_smul,euclidean_flux_eq κ μ hv]
    rfl
  simp_rw [he]
  exact integral_fluxVelocity_sq_le κ μ
    ((coordinateEquiv n).symm.toContinuousLinearMap.integrable_comp hv) hv₂

end SharpWasserstein.PeriodicConvolution
