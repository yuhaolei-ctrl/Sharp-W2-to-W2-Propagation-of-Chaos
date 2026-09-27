import SharpWasserstein.PeriodicSourceConvolutionSpatial

/-! Actual joint derivative bounds in both the translation parameter and state.
These are derived for the genuine kernel and generator, not imposed on the
source curve. -/
set_option maxHeartbeats 800000
noncomputable section
open scoped ContDiff BigOperators
namespace SharpWasserstein.PeriodicSourceConvolution
open NoiseAverage PropagatedSourceEquation WeightedTangent PeriodicBochner
open PeriodicIntegrationByParts PeriodicPositiveKernel
variable {P E F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The state derivative of a joint function is the actual derivative restricted
to the second coordinate direction. -/
theorem joint_fderiv_eq {f : P → E → F}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) (q : P×E) :
    fderiv ℝ (f q.1) q.2 =
      (fderiv ℝ (Function.uncurry f) q).comp (ContinuousLinearMap.inr ℝ P E) := by
  have hg : HasFDerivAt (fun y : E => (q.1,y)) (ContinuousLinearMap.inr ℝ P E) q.2 := by
    convert (hasFDerivAt_const (𝕜 := ℝ) q.1 q.2).prodMk (hasFDerivAt_id (𝕜 := ℝ) q.2) using 1 <;> rfl
  have h := ((hf.differentiable (by simp)) (q.1,q.2)).hasFDerivAt.comp q.2 hg
  exact h.fderiv

/-- Joint bounded derivatives are preserved by taking the true state derivative. -/
theorem joint_fderiv_bounded {f : P → E → F}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) (hB : AllDerivativesBounded (Function.uncurry f)) :
    AllDerivativesBounded (Function.uncurry (fun p => fderiv ℝ (f p))) := by
  let R : ((P×E) →L[ℝ] F) →L[ℝ] E →L[ℝ] F :=
    (ContinuousLinearMap.flipₗᵢ ℝ ((P×E) →L[ℝ] F) (E →L[ℝ] P×E) (E →L[ℝ] F)
      (ContinuousLinearMap.compL ℝ E (P×E) F)) (ContinuousLinearMap.inr ℝ P E)
  have he : Function.uncurry (fun p => fderiv ℝ (f p)) =
      fun q => R (fderiv ℝ (Function.uncurry f) q) := funext (joint_fderiv_eq hf)
  rw [he]
  exact hB.fderiv.linear_comp (contDiff_infty_iff_fderiv.mp hf).2 R

/-- The genuine product kernel has bounded mixed derivatives globally. -/
theorem joint_euclideanKernelTest_bounded {n : ℕ} (κ : ℝ) :
    AllDerivativesBounded (Function.uncurry (euclideanKernelTest (n := n) κ)) :=
  (show AllDerivativesBounded (kernel (n := n) κ) from kernel_derivatives_bounded n κ).comp_linear
    (kernel_smooth n κ)
    (ContinuousLinearMap.fst ℝ (Coordinates n) (Point n) -
      (coordinateEquiv n).toContinuousLinearMap.comp (ContinuousLinearMap.snd ℝ (Coordinates n) (Point n)))

variable {d N : ℕ}

theorem joint_coordinateDerivative_bounded {f : P → Configuration d N → ℝ}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) (hB : AllDerivativesBounded (Function.uncurry f))
    (i : Fin N) (a : Fin d) :
    AllDerivativesBounded (Function.uncurry (fun p => coordinateDerivative (f p) i a)) :=
  (joint_fderiv_bounded hf hB).linear_comp (joint_fderiv hf)
    (ContinuousLinearMap.apply ℝ ℝ (coordinateVector i a))

/-- Actual bounded smooth drift preserves all joint generator derivative bounds. -/
theorem joint_generator_bounded {f : P → Configuration d N → ℝ}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) (hBf : AllDerivativesBounded (Function.uncurry f))
    {b : Configuration d N → Configuration d N} (hb : ContDiff ℝ ∞ b) (hBb : AllDerivativesBounded b) :
    AllDerivativesBounded (Function.uncurry (fun p => generator b (f p))) := by
  have hLap : ContDiff ℝ ∞ (Function.uncurry (fun p => SharpWasserstein.laplacian (f p))) := by
    change ContDiff ℝ ∞ (fun q : P × Configuration d N => ∑ i : Fin N,∑ a : Fin d,
      coordinateDerivative (coordinateDerivative (f q.1) i a) i a q.2)
    exact ContDiff.sum fun i _ => ContDiff.sum fun a _ =>
      joint_coordinateDerivative (joint_coordinateDerivative hf i a) i a
  have hBLap : AllDerivativesBounded (Function.uncurry (fun p => SharpWasserstein.laplacian (f p))) :=
    AllDerivativesBounded.sum Finset.univ
      (fun i _ => ContDiff.sum fun a _ => joint_coordinateDerivative (joint_coordinateDerivative hf i a) i a)
      (fun i _ => AllDerivativesBounded.sum Finset.univ
        (fun a _ => joint_coordinateDerivative (joint_coordinateDerivative hf i a) i a)
        (fun a _ => joint_coordinateDerivative_bounded (joint_coordinateDerivative hf i a)
          (joint_coordinateDerivative_bounded hf hBf i a) i a))
  have he : Function.uncurry (fun p => generator b (f p)) =
      fun q : P × Configuration d N => SharpWasserstein.laplacian (f q.1) q.2+
        fderiv ℝ (f q.1) q.2 (b q.2) := by
    funext q
    exact generator_eq_laplacian_add_fderiv _ _ _
  rw [he]
  exact hBLap.add hLap ((joint_fderiv hf).clm_apply (hb.comp contDiff_snd))
    ((joint_fderiv_bounded hf hBf).clm_apply (joint_fderiv hf) (hb.comp contDiff_snd)
      (hBb.comp_linear hb (ContinuousLinearMap.snd ℝ P (Configuration d N))))

/-- Coordinate-conjugated generators retain those actual mixed bounds. -/
theorem joint_euclideanGenerator_bounded {f : P → Point (N*d) → ℝ}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) (hBf : AllDerivativesBounded (Function.uncurry f))
    {b : Configuration d N → Configuration d N} (hb : ContDiff ℝ ∞ b) (hBb : AllDerivativesBounded b) :
    AllDerivativesBounded (Function.uncurry (fun p => euclideanGenerator b (f p))) := by
  let L : (P×Configuration d N) →L[ℝ] P×Point (N*d) :=
    (ContinuousLinearMap.fst ℝ P (Configuration d N)).prod
      ((configurationEuclidean d N).toContinuousLinearMap.comp (ContinuousLinearMap.snd ℝ P (Configuration d N)))
  have hp : ContDiff ℝ ∞ (Function.uncurry (fun (p : P) (x : Configuration d N) =>
      f p (configurationEuclidean d N x))) := hf.comp L.contDiff
  have hBp : AllDerivativesBounded (Function.uncurry (fun (p : P) (x : Configuration d N) =>
      f p (configurationEuclidean d N x))) := hBf.comp_linear hf L
  let R : (P×Point (N*d)) →L[ℝ] P×Configuration d N :=
    (ContinuousLinearMap.fst ℝ P (Point (N*d))).prod
      ((configurationEuclidean d N).symm.toContinuousLinearMap.comp (ContinuousLinearMap.snd ℝ P (Point (N*d))))
  exact (joint_generator_bounded hp hBp hb hBb).comp_linear (joint_generator hp hb) R

end SharpWasserstein.PeriodicSourceConvolution
