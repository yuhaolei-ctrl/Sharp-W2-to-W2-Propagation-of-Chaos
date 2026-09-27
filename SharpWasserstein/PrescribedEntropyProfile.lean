import SharpWasserstein.ReferenceTensorIdentification
import SharpWasserstein.RegularizedEntropyProfile

/-! Entropy regularization relative to the manuscript's supplied reference
law. The reference identification and the dimension-dependent Euclidean
Lipschitz conversion are proved here rather than assumed. -/
noncomputable section
open MeasureTheory InformationTheory
open scoped NNReal ENNReal
namespace SharpWasserstein

theorem euclideanDrift_lipschitz_of_sup {d : ℕ} {v : ℝ → Position d → Position d}
    {K : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t)) (t : ℝ) :
    LipschitzWith (⟨Real.sqrt (d:ℝ)*(K:ℝ),by positivity⟩ : ℝ≥0)
      (GaussianBridge.euclideanDrift v t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm,dist_eq_norm]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
    ((hv t).norm_sub_le (WithLp.ofLp x) (WithLp.ofLp y))
  have hp : positionSq (WithLp.ofLp x-WithLp.ofLp y) = ‖x-y‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    rfl
  calc
    _ = positionSq (v t (WithLp.ofLp x)-v t (WithLp.ofLp y)) := by
      rw [EuclideanSpace.real_norm_sq_eq]
      rfl
    _ ≤ (d:ℝ)*‖v t (WithLp.ofLp x)-v t (WithLp.ofLp y)‖^2 := positionSq_le_norm_sq _
    _ ≤ (d:ℝ)*((K:ℝ)*‖WithLp.ofLp x-WithLp.ofLp y‖)^2 :=
      mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg d)
    _ ≤ (d:ℝ)*(K:ℝ)^2*positionSq (WithLp.ofLp x-WithLp.ofLp y) := by
      rw [mul_pow,mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (norm_sq_le_positionSq _) (sq_nonneg _)) (Nat.cast_nonneg d)
    _ = _ := by
      rw [hp]
      change (d:ℝ)*(K:ℝ)^2*‖x-y‖^2 = (Real.sqrt (d:ℝ)*(K:ℝ)*‖x-y‖)^2
      rw [mul_pow,mul_pow,Real.sq_sqrt (Nat.cast_nonneg d)]

namespace PrescribedReference
variable {d : ℕ} {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
  (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
  (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁)
  {μ : ℝ → Measure (Position d)} (hμ : IsLimitEvolution b μ)

theorem singleBrownianLaw_eq_supplied {t : ℝ} (ht : 0 < t) :
    DecoupledFlow.singleBrownianLaw
      (singleDrift_continuous hb hbound hL₁ hμ) (singleDrift_bound hbound hM hμ)
      (singleDrift_lipschitz hb hbound hL₁ hμ) ht.le (μ 0) = μ t := by
  letI := hμ.1 0 le_rfl
  have hh := law_tensor_eq_supplied hb hbound hM hL₁ hμ 1 ht.le
  rw [law_eq_decoupled hb hbound hM hL₁ hμ 1 _ ht] at hh
  change DecoupledFlow.brownianLaw _ _ _ ht.le (tensorLaw (μ 0) 1) = tensorLaw (μ t) 1 at hh
  rw [DecoupledFlow.brownianLaw_tensor,tensorLaw_one_eq_singletonLaw,tensorLaw_one_eq_singletonLaw] at hh
  have he := congrArg (fun ν : Measure (Configuration d 1) => ν.map (fun x => x (0 : Fin 1))) hh
  simpa only [singletonLaw_map_coordinate] using he

theorem marginal_klDiv_le_initial_profile {N : ℕ}
    (P : Measure (Configuration d N)) [IsProbabilityMeasure P] (hP : HasSecondMoment P)
    {t : ℝ} (ht : 0 < t) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hinit : ∀ m, ∀ hm : m ≤ N, wassersteinSq (marginal hm P) (tensorLaw (μ 0) m) ≤
      ENNReal.ofReal (C₀*(m:ℝ)^2/(N:ℝ)^2)) (m : ℕ) (hm : m ≤ N) :
    klDiv (marginal hm (law hb hbound hM hL₁ hμ N P t)) (tensorLaw (μ t) m) ≤
      ENNReal.ofReal ((RegularizationRates.bridgeCost (Real.sqrt (d:ℝ)*L₁) t*C₀)*(m:ℝ)^2/(N:ℝ)^2) := by
  letI := hμ.1 0 le_rfl
  have hh := DecoupledFlow.regularized_marginal_klDiv_le
    (singleDrift_continuous hb hbound hL₁ hμ) (singleDrift_bound hbound hM hμ)
    (singleDrift_lipschitz hb hbound hL₁ hμ) P (μ 0) hP
    (IsLimitEvolution.initial_integrable_positionSq hμ)
    (euclideanDrift_lipschitz_of_sup (singleDrift_lipschitz hb hbound hL₁ hμ)) ht hC₀ hinit m hm
  rw [singleBrownianLaw_eq_supplied hb hbound hM hL₁ hμ ht] at hh
  rw [law_eq_decoupled hb hbound hM hL₁ hμ N P ht]
  exact hh

end PrescribedReference
end SharpWasserstein
