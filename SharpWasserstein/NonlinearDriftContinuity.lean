import SharpWasserstein.DriftBounds
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! The genuine mean-field drift is jointly continuous along every narrowly
continuous probability curve. No density or moment regularity is required. -/

noncomputable section
open MeasureTheory
open scoped BoundedContinuousFunction

namespace SharpWasserstein

variable {d : ℕ} {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}

/-- Narrow convergence controls each bounded continuous coordinate of the kernel. -/
theorem nonlinearDrift_continuous_measure (hb : BoundedSmoothKernel b)
    (hbound : KernelBounds b M L₁ L₂) (x : Position d) :
    Continuous (fun μ : ProbabilityMeasure (Position d) => nonlinearDrift b μ x) := by
  apply continuous_pi
  intro a
  let f : Position d →ᵇ ℝ := BoundedContinuousFunction.mkOfBound
    ⟨fun y => b x y a, (continuous_apply a).comp (hb.contDiff_second x).continuous⟩
    (2 * M) (by
      intro y z
      calc
        dist (b x y a) (b x z a) ≤ ‖b x y a‖ + ‖b x z a‖ := dist_le_norm_add_norm _ _
        _ ≤ M + M := add_le_add ((norm_le_pi_norm (b x y) a).trans (hbound.value x y))
          ((norm_le_pi_norm (b x z) a).trans (hbound.value x z))
        _ = _ := by ring)
  have heq : (fun μ : ProbabilityMeasure (Position d) => nonlinearDrift b μ x a) =
      (fun μ : ProbabilityMeasure (Position d) => ∫ y, f y ∂μ) := by
    funext μ
    exact ((ContinuousLinearMap.proj a : Position d →L[ℝ] ℝ).integral_comp_comm
      (kernel_integrable hb hbound (μ : Measure (Position d)) x)).symm
  rw [heq]
  exact ProbabilityMeasure.continuous_integral_boundedContinuousFunction f

/-- Joint continuity in the law and spatial variable follows from the uniform
first-variable Lipschitz estimate, with its original constant. -/
theorem nonlinearDrift_joint_continuous (hb : BoundedSmoothKernel b)
    (hbound : KernelBounds b M L₁ L₂) (hL₁ : 0 ≤ L₁) :
    Continuous (fun p : ProbabilityMeasure (Position d) × Position d =>
      nonlinearDrift b p.1 p.2) := by
  exact continuous_prod_of_continuous_lipschitzWith' _ ⟨L₁, hL₁⟩
    (fun μ => nonlinearDrift_lipschitz hb hbound hL₁ μ)
    (nonlinearDrift_continuous_measure hb hbound)

theorem nonlinearDrift_continuous_curve {I : Type*} [TopologicalSpace I]
    (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂) (hL₁ : 0 ≤ L₁)
    {μ : I → ProbabilityMeasure (Position d)} (hμ : Continuous μ) :
    Continuous (fun p : I × Position d => nonlinearDrift b (μ p.1) p.2) :=
  (nonlinearDrift_joint_continuous hb hbound hL₁).comp
    ((hμ.comp continuous_fst).prodMk continuous_snd)

end SharpWasserstein
