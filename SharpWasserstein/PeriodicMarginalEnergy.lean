import SharpWasserstein.PeriodicMarginalLift
import SharpWasserstein.PeriodicConvolvedOptimizer

/-! Exact weighted marginal pairing and energy increments for the actual
periodic convolution densities and the constructed periodic optimizers. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology InnerProductSpace ContDiff BoundedContinuousFunction
namespace SharpWasserstein.PeriodicMarginalEnergy
open PeriodicIntegrationByParts PeriodicBochner PeriodicGalerkin PeriodicGradientClosure
open PeriodicConvolution PeriodicMarginalLift WeightedTangent WeightedMarginal WeightedDensity
variable {n m : ℕ}
  [MeasurableSpace (Point n)] [BorelSpace (Point n)]
  [MeasurableSpace (Point (n+m))] [BorelSpace (Point (n+m))]

omit [MeasurableSpace (Point (n+m))] [BorelSpace (Point (n+m))] in
theorem integral_densityBCF (κ : ℝ) (μ : Measure (Coordinates n)) [IsProbabilityMeasure μ]
    (f : Point n → ℝ) :
    (∫ y, densityBCF κ μ y*f y ∂cubePoint) =
      ∫ x, f ((coordinateEquiv n).symm x) ∂smoothLaw κ μ := by
  rw [integral_cubePoint,integral_smoothLaw_density]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change density κ μ (coordinateEquiv n ((coordinateEquiv n).symm x))*_ = _
    rw [ContinuousLinearEquiv.apply_symm_apply]

variable (κ : ℝ) (μ : Measure (Coordinates (n+m))) [IsProbabilityMeasure μ]

local instance marginal_probability : IsProbabilityMeasure (μ.map (prefixCoords n m)) :=
  Measure.isProbabilityMeasure_map (prefix_continuous n m).measurable.aemeasurable

/-- The weighted bilinear form of two actual lifted fields is exactly the
lower-dimensional weighted form, with the genuine convolved marginal law. -/
theorem densityPairing_lift (u v : gradientClosure (cubePoint (n := n))) :
    ⟪weightedOperator cubePoint (densityBCF κ μ) (gradientLift (m := m) u),
      gradientLift (m := m) v⟫_ℝ =
    ⟪weightedOperator cubePoint (densityBCF κ (μ.map (prefixCoords n m))) u,v⟫_ℝ := by
  rw [weightedOperator_inner,weightedOperator_inner]
  let F : Point n → ℝ := fun y => ⟪(u : Lp (Point n) 2 cubePoint) y,
    (v : Lp (Point n) 2 cubePoint) y⟫_ℝ
  have hm : AEStronglyMeasurable (fun x => F ((coordinateEquiv n).symm x))
      (smoothLaw κ (μ.map (prefixCoords n m))) := by
    apply AEStronglyMeasurable.mono_ac (withDensity_absolutelyContinuous _ _)
    have hu := Lp.aestronglyMeasurable (u : Lp (Point n) 2 (cubePoint (n := n)))
    have hv := Lp.aestronglyMeasurable (v : Lp (Point n) 2 (cubePoint (n := n)))
    exact (hu.inner hv).comp_measurePreserving (coordinateSymm_measurePreserving (n := n))
  calc
    _ = ∫ y, densityBCF κ μ y*F (prefixProjection n m y) ∂cubePoint := by
      apply integral_congr_ae
      filter_upwards [liftLinear_ae (m := m) (u : Lp (Point n) 2 cubePoint),
        liftLinear_ae (m := m) (v : Lp (Point n) 2 cubePoint)] with y hy hz
      change densityBCF κ μ y*⟪liftLinear (m := m) (u : Lp (Point n) 2 cubePoint) y,
        liftLinear (m := m) (v : Lp (Point n) 2 cubePoint) y⟫_ℝ = _
      rw [hy,hz,LinearIsometry.inner_map_map]
    _ = ∫ x, F ((coordinateEquiv n).symm (prefixCoords n m x)) ∂smoothLaw κ μ :=
      integral_densityBCF κ μ _
    _ = ∫ x, F ((coordinateEquiv n).symm x) ∂smoothLaw κ (μ.map (prefixCoords n m)) := by
      rw [← smoothLaw_prefix κ μ] at hm ⊢
      exact (integral_map (prefix_continuous n m).measurable.aemeasurable hm).symm
    _ = _ := (integral_densityBCF κ (μ.map (prefixCoords n m)) F).symm

omit [IsProbabilityMeasure μ] in
/-- The actual marginal action is restriction to lifted cylinder gradients. -/
def marginalFunctional (ℓ : gradientClosure (cubePoint (n := n+m)) →L[ℝ] ℝ) :
    gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ := ℓ.comp (gradientLift (m := m))

theorem densityBCF_positive_lower (k : ℕ) (ν : Measure (Coordinates k)) [IsProbabilityMeasure ν] :
    0 < (Real.exp (-|κ|)/PeriodicPositiveKernel.normalizer κ)^k :=
  pow_pos (div_pos (Real.exp_pos _) (PeriodicPositiveKernel.normalizer_pos κ)) k

/-- The genuine difference of the two optimizers is orthogonal to every
lifted periodic gradient in the actual full density-weighted pairing. -/
theorem optimizer_residual_orthogonal
    (ℓ : gradientClosure (cubePoint (n := n+m)) →L[ℝ] ℝ)
    (w : periodicSpace (n := n)) :
    let U := (optimizer (densityBCF κ μ) ℓ : gradientClosure (cubePoint (n := n+m)))
    let u := (optimizer (densityBCF κ (μ.map (prefixCoords n m))) (marginalFunctional ℓ) :
      gradientClosure (cubePoint (n := n)))
    ⟪weightedOperator cubePoint (densityBCF κ μ) (U-gradientLift (m := m) u),
      gradientLift (m := m) (w : gradientClosure (cubePoint (n := n)))⟫_ℝ = 0 := by
  dsimp only
  rw [map_sub,inner_sub_left,densityPairing_lift]
  have hfull := optimizer_equation (densityBCF κ μ) ℓ
    (densityBCF_positive_lower κ (n+m) μ) (Eventually.of_forall (densityBCF_lower κ μ))
    (periodicLift (m := m) w)
  have hlow := optimizer_equation (densityBCF κ (μ.map (prefixCoords n m)))
    (marginalFunctional ℓ) (densityBCF_positive_lower κ n (μ.map (prefixCoords n m)))
    (Eventually.of_forall (densityBCF_lower κ (μ.map (prefixCoords n m)))) w
  rw [hlow]
  exact sub_eq_zero.mpr hfull

/-- Exact Pythagorean energy increment for the actual convolved marginal
optimizers; no projection or hierarchy estimate is assumed. -/
theorem optimizer_energy_increment
    (ℓ : gradientClosure (cubePoint (n := n+m)) →L[ℝ] ℝ) :
    let U := (optimizer (densityBCF κ μ) ℓ : gradientClosure (cubePoint (n := n+m)))
    let u := (optimizer (densityBCF κ (μ.map (prefixCoords n m))) (marginalFunctional ℓ) :
      gradientClosure (cubePoint (n := n)))
    ⟪weightedOperator cubePoint (densityBCF κ μ) (U-gradientLift (m := m) u),
      U-gradientLift (m := m) u⟫_ℝ = ℓ U-marginalFunctional ℓ u := by
  dsimp only
  let U := (optimizer (densityBCF κ μ) ℓ : gradientClosure (cubePoint (n := n+m)))
  let u := (optimizer (densityBCF κ (μ.map (prefixCoords n m))) (marginalFunctional ℓ) :
    gradientClosure (cubePoint (n := n)))
  let A := weightedOperator cubePoint (densityBCF κ μ)
  let V := gradientLift (m := m) u
  have ho := optimizer_residual_orthogonal κ μ ℓ
    (optimizer (densityBCF κ (μ.map (prefixCoords n m))) (marginalFunctional ℓ))
  have hf := optimizer_equation (densityBCF κ μ) ℓ
    (densityBCF_positive_lower κ (n+m) μ) (Eventually.of_forall (densityBCF_lower κ μ))
    (optimizer (densityBCF κ μ) ℓ)
  have hl := optimizer_equation (densityBCF κ (μ.map (prefixCoords n m)))
    (marginalFunctional ℓ) (densityBCF_positive_lower κ n (μ.map (prefixCoords n m)))
    (Eventually.of_forall (densityBCF_lower κ (μ.map (prefixCoords n m))))
    (optimizer (densityBCF κ (μ.map (prefixCoords n m))) (marginalFunctional ℓ))
  have hv : ⟪A V,V⟫_ℝ = marginalFunctional ℓ u := (densityPairing_lift κ μ u u).trans hl
  have hs : ⟪A V,U⟫_ℝ = ⟪A U,V⟫_ℝ := by
    rw [weightedOperator_symmetric,real_inner_comm]
  change ⟪A (U-V),V⟫_ℝ = 0 at ho
  change ⟪A U,U⟫_ℝ = ℓ U at hf
  change ⟪A (U-V),U-V⟫_ℝ = ℓ U-marginalFunctional ℓ u
  simp only [map_sub,inner_sub_left,inner_sub_right] at ho ⊢
  rw [hs,hf,hv]
  rw [hv] at ho
  linarith

/-- The increment is literally the weighted Euclidean square of the
optimizer fluctuation field, including correlations in the original law. -/
theorem optimizer_energy_increment_integral
    (ℓ : gradientClosure (cubePoint (n := n+m)) →L[ℝ] ℝ) :
    let U := (optimizer (densityBCF κ μ) ℓ : gradientClosure (cubePoint (n := n+m)))
    let u := (optimizer (densityBCF κ (μ.map (prefixCoords n m))) (marginalFunctional ℓ) :
      gradientClosure (cubePoint (n := n)))
    (∫ y, densityBCF κ μ y *
      ‖((U-gradientLift (m := m) u : gradientClosure (cubePoint (n := n+m))) :
        Lp (Point (n+m)) 2 cubePoint) y‖^2 ∂cubePoint) = ℓ U-marginalFunctional ℓ u := by
  have h := optimizer_energy_increment κ μ ℓ
  dsimp only at h ⊢
  rw [weightedOperator_inner] at h
  simpa only [real_inner_self_eq_norm_sq] using h

end SharpWasserstein.PeriodicMarginalEnergy
