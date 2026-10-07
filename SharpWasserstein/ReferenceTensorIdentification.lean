module

public import SharpWasserstein.Compat
public import SharpWasserstein.ReferenceWeakIdentification

@[expose] public section

/-! The constructed reference from product initial data is exactly the
manuscript's supplied tensor curve at every nonnegative time. -/
noncomputable section
open MeasureTheory Set
namespace SharpWasserstein

theorem tensorLaw_one_eq_singletonLaw {d : ℕ} (μ : Measure (Position d)) :
    tensorLaw μ 1 = singletonLaw μ := by
  have h := (measurePreserving_funUnique μ (Fin 1)).symm
  exact h.map_eq.symm

theorem singletonLaw_map_coordinate {d : ℕ} (μ : Measure (Position d)) :
    (singletonLaw μ).map (fun x => x (0 : Fin 1)) = μ := by
  unfold singletonLaw
  rw [Measure.map_map (measurable_pi_apply (0 : Fin 1)) (by fun_prop)]
  simp only [Function.comp_def,Measure.map_id']

namespace PrescribedReference
variable {d : ℕ} {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
  (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
  (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁)
  {μ : ℝ → Measure (Position d)} (hμ : IsLimitEvolution b μ)

theorem law_tensor_eq_supplied (N : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    law hb hbound hM hL₁ hμ N (tensorLaw (μ 0) N) t = tensorLaw (μ t) N := by
  by_cases ht0 : t = 0
  · subst t
    letI := hμ.1 0 le_rfl
    exact law_initial hb hbound hM hL₁ hμ N (tensorLaw (μ 0) N)
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  have hs := singleton_eq_law hb hbound hM hL₁ hμ ht
  rw [← tensorLaw_one_eq_singletonLaw (μ 0),law_tensor hb hbound hM hL₁ hμ 1 htpos,
    tensorLaw_one_eq_singletonLaw] at hs
  have he := congrArg (fun ν : Measure (Configuration d 1) => ν.map (fun x => x (0 : Fin 1))) hs
  simp only [singletonLaw_map_coordinate] at he
  rw [law_tensor hb hbound hM hL₁ hμ N htpos,← he]

include hb hbound hM hL₁ hμ in
theorem supplied_tensor_weakEvolution (N : ℕ) :
    WeakEvolution (fun t x i => nonlinearDrift b (μ t) (x i)) (fun t => tensorLaw (μ t) N) := by
  have h := tensor_initial_weakEvolution hb hbound hM hL₁ hμ N
  have he (t : ℝ) (ht : 0 ≤ t) := law_tensor_eq_supplied hb hbound hM hL₁ hμ N ht
  refine {
    probability := fun t ht => by rw [← he t ht]; exact h.probability t ht
    secondMoment := fun t ht => by rw [← he t ht]; exact h.secondMoment t ht
    momentBound := ?_
    testContinuous := ?_
    generatorIntegrable := ?_
    timeIntegrable := ?_
    equation := ?_ }
  · intro T hT
    obtain ⟨C,hC,hb⟩ := h.momentBound T hT
    exact ⟨C,hC,fun t ht => by rw [← he t ht.1]; exact hb t ht⟩
  · intro φ hφ
    apply (h.testContinuous φ hφ).congr
    intro t ht
    dsimp only
    rw [he t ht]
  · intro φ hφ t ht
    rw [← he t ht]
    exact h.generatorIntegrable φ hφ t ht
  · intro φ hφ t ht
    apply (intervalIntegrable_congr (f := fun s => ∫ x, generator
      (fun x i => nonlinearDrift b (μ s) (x i)) φ x ∂law hb hbound hM hL₁ hμ N (tensorLaw (μ 0) N) s) ?_).mp
      (h.timeIntegrable φ hφ t ht)
    intro s hs
    rw [uIoc_of_le ht] at hs
    dsimp only
    rw [he s hs.1.le]
  · intro φ hφ t ht
    have hh := h.equation φ hφ t ht
    rw [he t ht,he 0 le_rfl] at hh
    rw [hh]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht] at hs
    dsimp only
    rw [he s hs.1]

end PrescribedReference
end SharpWasserstein
