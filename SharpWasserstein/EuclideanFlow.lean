import SharpWasserstein.FiniteTrajectory
import SharpWasserstein.ConfigurationEuclidean
import SharpWasserstein.EuclideanDrift

/-! The pathwise stability estimates use the actual Euclidean configuration
norm, so their constants have no hidden dependence on the particle number. -/

noncomputable section
open Set MeasureTheory
open scoped NNReal Interval

namespace SharpWasserstein

/-- Transport the actual integral equation by a continuous linear equivalence. -/
theorem FiniteAdditiveTrajectory.map_equiv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (L : E ≃L[ℝ] F) {v : ℝ → E → E} {w X : ℝ → E} {x₀ : E} {T : ℝ}
    (h : FiniteAdditiveTrajectory v w x₀ T X) :
    FiniteAdditiveTrajectory (fun t y => L (v t (L.symm y))) (fun t => L (w t))
      (L x₀) T (fun t => L (X t)) := by
  refine ⟨L.continuous.comp_continuousOn h.continuous, ?_, ?_⟩
  · simpa only [ContinuousLinearEquiv.symm_apply_apply, Function.comp_def] using
      L.continuous.comp_continuousOn h.driftContinuous
  · intro t ht
    simp only [ContinuousLinearEquiv.symm_apply_apply]
    have hi : IntervalIntegrable (fun s => v s (X s)) volume 0 t :=
      (h.driftContinuous.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
    have he : (∫ s in (0 : ℝ)..t, L (v s (X s))) = L (∫ s in (0 : ℝ)..t, v s (X s)) :=
      L.toContinuousLinearMap.intervalIntegral_comp_comm hi
    rw [he]
    simpa only [map_add] using congrArg L (h.equation t ht)

/-- Convert the actual uniform quadratic drift estimate into an actual
Euclidean Lipschitz estimate. -/
theorem euclidean_particleDrift_lipschitz {d N : ℕ}
    {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
    (hN : 0 < N) (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
    (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) :
    LipschitzWith ⟨Real.sqrt (2 * d * (L₁ ^ 2 + L₂ ^ 2)), Real.sqrt_nonneg _⟩
      (fun y => configurationEuclidean d N
        (particleDrift b ((configurationEuclidean d N).symm y))) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm]
  change ‖configurationEuclidean d N (particleDrift b ((configurationEuclidean d N).symm x)) -
      configurationEuclidean d N (particleDrift b ((configurationEuclidean d N).symm y))‖ ≤
    Real.sqrt (2 * d * (L₁ ^ 2 + L₂ ^ 2)) * ‖x - y‖
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  have h := particleDrift_quadratic_difference hN hb hbound hL₁ hL₂
    ((configurationEuclidean d N).symm x) ((configurationEuclidean d N).symm y)
  simpa only [productCost_eq_configurationEuclidean_dist_sq,
    ContinuousLinearEquiv.apply_symm_apply] using h

/-- Actual particle trajectories driven by common noise obey a quadratic
stability bound whose exponent is independent of `N`. -/
theorem particleTrajectory_productCost_le {d N : ℕ}
    {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
    (hN : 0 < N) (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
    (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    {w X Y : ℝ → Configuration d N} {x₀ y₀ : Configuration d N} {T t : ℝ}
    (hX : FiniteAdditiveTrajectory (fun _ => particleDrift b) w x₀ T X)
    (hY : FiniteAdditiveTrajectory (fun _ => particleDrift b) w y₀ T Y)
    (ht : t ∈ Icc 0 T) :
    productCost (X t) (Y t) ≤
      Real.exp (Real.sqrt (2 * d * (L₁ ^ 2 + L₂ ^ 2)) * t) ^ 2 * productCost x₀ y₀ := by
  have hv := euclidean_particleDrift_lipschitz hN hb hbound hL₁ hL₂
  have hs := (hX.map_equiv (configurationEuclidean d N)).stability (fun _ _ => hv)
    (hY.map_equiv (configurationEuclidean d N)) ht
  change ‖configurationEuclidean d N (X t) - configurationEuclidean d N (Y t)‖ ≤
    ‖configurationEuclidean d N x₀ - configurationEuclidean d N y₀‖ *
      Real.exp (Real.sqrt (2 * d * (L₁ ^ 2 + L₂ ^ 2)) * t) at hs
  have hs₂ := (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hs
  rw [productCost_eq_configurationEuclidean_dist_sq,
    productCost_eq_configurationEuclidean_dist_sq]
  simpa only [mul_pow, mul_comm] using hs₂

end SharpWasserstein
