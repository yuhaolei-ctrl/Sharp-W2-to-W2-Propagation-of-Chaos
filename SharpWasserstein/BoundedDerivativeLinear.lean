module

public import SharpWasserstein.Compat
public import SharpWasserstein.BoundedDerivativeComposition

@[expose] public section

/-! Finite sums and linear coordinate changes preserve actual bounded
derivatives of every order. -/
noncomputable section
open scoped ContDiff BigOperators
namespace SharpWasserstein.NoiseAverage
variable {D E F : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem AllDerivativesBounded.comp_linear {f : E → F}
    (hf : ContDiff ℝ ∞ f) (hB : AllDerivativesBounded f) (L : D →L[ℝ] E) :
    AllDerivativesBounded (fun x => f (L x)) := by
  apply AllDerivativesBounded.comp_of_fderiv hf L.contDiff hB
  have he : _root_.fderiv ℝ L = fun _ => L := funext (fun x => L.fderiv)
  rw [he]
  exact allDerivativesBounded_const L

theorem AllDerivativesBounded.linear_comp {f : D → E}
    (hf : ContDiff ℝ ∞ f) (hB : AllDerivativesBounded f) (L : E →L[ℝ] F) :
    AllDerivativesBounded (fun x => L (f x)) := by
  intro n
  obtain ⟨C,hC,hb⟩ := hB n
  refine ⟨‖L‖*C,mul_nonneg (norm_nonneg _) hC,fun x => ?_⟩
  exact (L.norm_iteratedFDeriv_comp_left hf.contDiffAt
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).trans
      (mul_le_mul_of_nonneg_left (hb x) (norm_nonneg _))

theorem AllDerivativesBounded.sum {ι : Type*} (s : Finset ι) {f : ι → E → F}
    (hf : ∀ i ∈ s, ContDiff ℝ ∞ (f i)) (hB : ∀ i ∈ s, AllDerivativesBounded (f i)) :
    AllDerivativesBounded (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using allDerivativesBounded_const (0:F)
  | @insert i s hi ih =>
    have hs : ContDiff ℝ ∞ (fun x => ∑ j ∈ s, f j x) := ContDiff.sum (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert hi] using (hB i (Finset.mem_insert_self i s)).add
      (hf i (Finset.mem_insert_self i s)) hs
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)) (fun j hj => hB j (Finset.mem_insert_of_mem hj)))

end SharpWasserstein.NoiseAverage
