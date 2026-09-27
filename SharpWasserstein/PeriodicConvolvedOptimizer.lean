import SharpWasserstein.PeriodicFluxEuclidean
import SharpWasserstein.PeriodicFluxOptimizer
import SharpWasserstein.PeriodicSmoothGradient

/-! Construct the actual density and tangent functional used by the periodic
elliptic optimizer from an arbitrary initial finite-energy vector measure.
Its source is the smooth convolved negative divergence and its optimizer
energy contracts with coefficient one in the genuine Euclidean norm. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ContDiff BoundedContinuousFunction
namespace SharpWasserstein.PeriodicConvolution
open PeriodicIntegrationByParts PeriodicPositiveKernel PeriodicBochner WeightedTangent
open PeriodicGalerkin PeriodicGradientClosure PeriodicSmoothGradient PeriodicFourierTests
variable {n : ℕ} [MeasurableSpace (Point n)] [BorelSpace (Point n)]
  (κ : ℝ) (μ : Measure (Coordinates n)) [IsProbabilityMeasure μ]

/-- The actual strictly positive convolution density in the energy's Banach space. -/
def densityBCF : Point n →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun y => density κ μ (coordinateEquiv n y))
    ((density_smooth κ μ).continuous.comp (coordinateEquiv n).continuous)
    ((Real.exp |κ|/normalizer κ)^n) (fun y => by
      rw [Real.norm_eq_abs,abs_of_pos (density_pos κ μ _)]
      exact (density_bounds κ μ _).2)

omit [MeasurableSpace (Point n)] [BorelSpace (Point n)] in
theorem densityBCF_lower (y : Point n) :
    (Real.exp (-|κ|)/normalizer κ)^n ≤ densityBCF κ μ y := (density_bounds κ μ _).1

omit [IsProbabilityMeasure μ] in
/-- The smoothed vector measure is an actual Euclidean L² field over the cube. -/
theorem convolvedFlux_memLp {v : Coordinates n → Coordinates n} (hv : Integrable v μ) :
    MemLp (fun y : Point n => flux κ μ (fun z => (coordinateEquiv n).symm (v z)) (coordinateEquiv n y))
      2 (cubePoint (n := n)) := by
  have hvE := (coordinateEquiv n).symm.toContinuousLinearMap.integrable_comp hv
  obtain ⟨C,_,hC⟩ := PeriodicSmoothBounds.norm_bound (flux_periodic κ μ _)
    (flux_continuous_of_integrable κ μ hvE)
  exact MemLp.of_bound ((flux_continuous_of_integrable κ μ hvE).comp
    (coordinateEquiv n).continuous).aestronglyMeasurable C (Eventually.of_forall fun _ => hC _)

def convolvedFluxLp (v : Coordinates n → Coordinates n) (hv : Integrable v μ) :
    Lp (Point n) 2 (cubePoint (n := n)) := (convolvedFlux_memLp κ μ hv).toLp _

omit [IsProbabilityMeasure μ] in
theorem convolvedFluxLp_ae (v : Coordinates n → Coordinates n) (hv : Integrable v μ) :
    convolvedFluxLp κ μ v hv =ᵐ[cubePoint]
      (fun y => flux κ μ (fun z => (coordinateEquiv n).symm (v z)) (coordinateEquiv n y)) :=
  (convolvedFlux_memLp κ μ hv).coeFn_toLp

def convolvedFunctional (v : Coordinates n → Coordinates n) (hv : Integrable v μ) :
    gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ :=
  PeriodicFluxOptimizer.functional (convolvedFluxLp κ μ v hv)

/-- The functional is exactly the genuine smooth source, on every smooth
periodic scalar test. Thus source regularity is a derived fact. -/
theorem convolvedFunctional_gradient (v : Coordinates n → Coordinates n) (hv : Integrable v μ)
    {f : Coordinates n → ℝ} (hf : ContDiff ℝ ∞ f) (hpf : Periodic f) :
    convolvedFunctional κ μ v hv (gradientVector f hf) =
      ∫ x, fluxSource κ μ v x*f x ∂cube n := by
  rw [convolvedFunctional,PeriodicFluxOptimizer.functional_apply]
  calc
    _ = ∫ y, ⟪flux κ μ (fun z => (coordinateEquiv n).symm (v z)) (coordinateEquiv n y),
        gradient (compactTest f hf : Point n → ℝ) y⟫_ℝ ∂cubePoint := by
      apply integral_congr_ae
      filter_upwards [convolvedFluxLp_ae κ μ v hv,
        testGradient_ae cubePoint (compactTest f hf)] with y hy hz
      change ⟪convolvedFluxLp κ μ v hv y,testGradient cubePoint (compactTest f hf) y⟫_ℝ = _
      rw [hy,hz]
    _ = ∫ x, ⟪euclideanGradient f x,flux κ μ (fun z => (coordinateEquiv n).symm (v z)) x⟫_ℝ ∂cube n := by
      rw [integral_cubePoint]
      apply integral_congr_ae
      filter_upwards [cube_ae_mem n] with x hx
      rw [ContinuousLinearEquiv.apply_symm_apply,compactTest_gradient_on_cube f hf hx]
      exact real_inner_comm _ _
    _ = _ := (integral_fluxSource_euclidean κ μ hv hf hpf).symm

theorem convolvedFunctional_trialGradient (v : Coordinates n → Coordinates n) (hv : Integrable v μ)
    (s : Finset ((Fin n → ℤ) × Bool)) (f : frequencySpace s) :
    convolvedFunctional κ μ v hv (trialGradient s f) =
      ∫ x, fluxSource κ μ v x*f.val x ∂cube n :=
  convolvedFunctional_gradient κ μ v hv
    (frequencySpace_properties s f.property).1 (frequencySpace_properties s f.property).2.1

/-- Initial smoothing contracts the energy of the actual periodic optimizer,
with no lower-density or dimension constant in the result. -/
theorem convolved_optimizer_energy_le (v : Coordinates n → Coordinates n) (hv : Integrable v μ)
    (hv₂ : Integrable (fun y => ‖(coordinateEquiv n).symm (v y)‖^2) μ) :
    convolvedFunctional κ μ v hv (optimizer (densityBCF κ μ) (convolvedFunctional κ μ v hv)) ≤
      ∫ y, ‖(coordinateEquiv n).symm (v y)‖^2 ∂μ := by
  have ha : 0 < (Real.exp (-|κ|)/normalizer κ)^n :=
    pow_pos (div_pos (Real.exp_pos _) (normalizer_pos κ)) n
  have h := PeriodicFluxOptimizer.optimizer_energy_le_fluxAction (densityBCF κ μ)
    (convolvedFluxLp κ μ v hv) ha (densityBCF_lower κ μ)
  change convolvedFunctional κ μ v hv (optimizer (densityBCF κ μ) (convolvedFunctional κ μ v hv)) ≤ _ at h
  apply h.trans
  calc
    _ = ∫ y, ‖flux κ μ (fun z => (coordinateEquiv n).symm (v z)) (coordinateEquiv n y)‖^2/
        density κ μ (coordinateEquiv n y) ∂cubePoint := by
      apply integral_congr_ae
      filter_upwards [convolvedFluxLp_ae κ μ v hv] with y hy
      rw [hy]
      rfl
    _ = ∫ x, ‖flux κ μ (fun z => (coordinateEquiv n).symm (v z)) x‖^2/density κ μ x ∂cube n := by
      rw [integral_cubePoint]
      simp only [ContinuousLinearEquiv.apply_symm_apply]
    _ ≤ _ := integral_flux_action_le κ μ
      ((coordinateEquiv n).symm.toContinuousLinearMap.integrable_comp hv) hv₂

end SharpWasserstein.PeriodicConvolution
