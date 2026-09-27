import SharpWasserstein.Dynamics
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Bounds on the actual interaction and McKean--Vlasov drifts. The constants
below are independent of the particle number. The coordinate-space norm in
this file is the ambient sup norm; quadratic-cost bounds are stated separately. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace SharpWasserstein

variable {d N : ℕ} {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}

theorem BoundedSmoothKernel.contDiff_first (hb : BoundedSmoothKernel b) (y : Position d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => b x y) :=
  hb.smooth.comp (contDiff_id.prodMk contDiff_const)

theorem BoundedSmoothKernel.contDiff_second (hb : BoundedSmoothKernel b) (x : Position d) :
    ContDiff ℝ (⊤ : ℕ∞) (b x) :=
  hb.smooth.comp (contDiff_const.prodMk contDiff_id)

theorem kernel_first_difference (hb : BoundedSmoothKernel b)
    (hbound : KernelBounds b M L₁ L₂) (x x' y : Position d) :
    ‖b x y - b x' y‖ ≤ L₁ * ‖x - x'‖ := by
  exact (convex_univ : Convex ℝ (univ : Set (Position d))).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => (hb.contDiff_first y).differentiable (by simp) z)
    (fun z _ => hbound.first z y) (mem_univ x') (mem_univ x)

theorem kernel_second_difference (hb : BoundedSmoothKernel b)
    (hbound : KernelBounds b M L₁ L₂) (x y y' : Position d) :
    ‖b x y - b x y'‖ ≤ L₂ * ‖y - y'‖ := by
  exact (convex_univ : Convex ℝ (univ : Set (Position d))).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => (hb.contDiff_second x).differentiable (by simp) z)
    (fun z _ => hbound.second x z) (mem_univ y') (mem_univ y)

theorem kernel_joint_difference (hb : BoundedSmoothKernel b)
    (hbound : KernelBounds b M L₁ L₂) (x x' y y' : Position d) :
    ‖b x y - b x' y'‖ ≤ L₁ * ‖x - x'‖ + L₂ * ‖y - y'‖ := by
  calc
    ‖b x y - b x' y'‖ ≤ ‖b x y - b x' y‖ + ‖b x' y - b x' y'‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := add_le_add (kernel_first_difference hb hbound x x' y)
      (kernel_second_difference hb hbound x' y y')

theorem particleDrift_coordinate_bound (hN : 0 < N) (hbound : KernelBounds b M L₁ L₂)
    (x : Configuration d N) (i : Fin N) : ‖particleDrift b x i‖ ≤ M := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    ‖particleDrift b x i‖ = (N : ℝ)⁻¹ * ‖∑ j, b (x i) (x j)‖ := by
      simp [particleDrift, norm_smul]
    _ ≤ (N : ℝ)⁻¹ * ∑ j, ‖b (x i) (x j)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (le_of_lt (inv_pos.2 hNr))
    _ ≤ (N : ℝ)⁻¹ * ∑ _j : Fin N, M :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hbound.value (x i) (x j))
        (le_of_lt (inv_pos.2 hNr))
    _ = M := by simp [ne_of_gt hNr]

theorem particleDrift_difference (hN : 0 < N) (hb : BoundedSmoothKernel b)
    (hbound : KernelBounds b M L₁ L₂) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (x y : Configuration d N) :
    ‖particleDrift b x - particleDrift b y‖ ≤ (L₁ + L₂) * ‖x - y‖ := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro i
  change ‖(N : ℝ)⁻¹ • ∑ j, b (x i) (x j) - (N : ℝ)⁻¹ • ∑ j, b (y i) (y j)‖ ≤ _
  rw [← smul_sub, ← Finset.sum_sub_distrib, norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.2 hNr)]
  calc
    (N : ℝ)⁻¹ * ‖∑ j, (b (x i) (x j) - b (y i) (y j))‖ ≤
        (N : ℝ)⁻¹ * ∑ j, ‖b (x i) (x j) - b (y i) (y j)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (le_of_lt (inv_pos.2 hNr))
    _ ≤ (N : ℝ)⁻¹ * ∑ _j : Fin N, ((L₁ + L₂) * ‖x - y‖) := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt (inv_pos.2 hNr))
      apply Finset.sum_le_sum
      intro j _
      calc
        ‖b (x i) (x j) - b (y i) (y j)‖ ≤ L₁ * ‖x i - y i‖ + L₂ * ‖x j - y j‖ :=
          kernel_joint_difference hb hbound _ _ _ _
        _ ≤ L₁ * ‖x - y‖ + L₂ * ‖x - y‖ :=
          add_le_add (mul_le_mul_of_nonneg_left (norm_le_pi_norm (x - y) i) hL₁)
            (mul_le_mul_of_nonneg_left (norm_le_pi_norm (x - y) j) hL₂)
        _ = _ := by ring
    _ = _ := by simp [ne_of_gt hNr]

theorem particleDrift_lipschitz (hN : 0 < N) (hb : BoundedSmoothKernel b)
    (hbound : KernelBounds b M L₁ L₂) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) :
    LipschitzWith ⟨L₁ + L₂, add_nonneg hL₁ hL₂⟩ (particleDrift (N := N) b) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change ‖particleDrift b x - particleDrift b y‖ ≤ (L₁ + L₂) * ‖x - y‖
  exact particleDrift_difference hN hb hbound hL₁ hL₂ x y

theorem nonlinearDrift_bound (hbound : KernelBounds b M L₁ L₂)
    (μ : Measure (Position d)) [IsProbabilityMeasure μ] (x : Position d) :
    ‖nonlinearDrift b μ x‖ ≤ M := by
  simpa [nonlinearDrift] using (norm_integral_le_of_norm_le_const
    (μ := μ) (Filter.Eventually.of_forall (hbound.value x)))

theorem kernel_integrable (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
    (μ : Measure (Position d)) [IsFiniteMeasure μ] (x : Position d) : Integrable (b x) μ := by
  exact Integrable.mono' (integrable_const M)
    (hb.contDiff_second x).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall (hbound.value x))

theorem nonlinearDrift_difference (hb : BoundedSmoothKernel b)
    (hbound : KernelBounds b M L₁ L₂) (μ : Measure (Position d))
    [IsProbabilityMeasure μ] (x y : Position d) :
    ‖nonlinearDrift b μ x - nonlinearDrift b μ y‖ ≤ L₁ * ‖x - y‖ := by
  rw [nonlinearDrift, nonlinearDrift, ← integral_sub
    (kernel_integrable hb hbound μ x) (kernel_integrable hb hbound μ y)]
  simpa using (norm_integral_le_of_norm_le_const (μ := μ)
    (Filter.Eventually.of_forall fun z => kernel_first_difference hb hbound x y z))

theorem nonlinearDrift_lipschitz (hb : BoundedSmoothKernel b)
    (hbound : KernelBounds b M L₁ L₂) (hL₁ : 0 ≤ L₁)
    (μ : Measure (Position d)) [IsProbabilityMeasure μ] :
    LipschitzWith ⟨L₁, hL₁⟩ (nonlinearDrift b μ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change ‖nonlinearDrift b μ x - nonlinearDrift b μ y‖ ≤ L₁ * ‖x - y‖
  exact nonlinearDrift_difference hb hbound μ x y

end SharpWasserstein
