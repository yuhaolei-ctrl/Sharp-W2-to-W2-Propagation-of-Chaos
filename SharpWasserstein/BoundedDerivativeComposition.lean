module

public import SharpWasserstein.Compat
public import SharpWasserstein.NoiseAverageSmooth
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

@[expose] public section

/-! Closure of actual bounded iterated derivatives under affine operations and
smooth composition. The inner map may be unbounded, as an Euler mean is. -/
noncomputable section
open scoped ContDiff NNReal BigOperators
namespace SharpWasserstein.NoiseAverage
universe u
variable {D E F : Type u} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem allDerivativesBounded_const (c : F) : AllDerivativesBounded (fun _ : E => c) := by
  intro n
  cases n with
  | zero => exact ⟨‖c‖,norm_nonneg _,fun x => by simp [norm_iteratedFDeriv_zero]⟩
  | succ n => exact ⟨0,le_rfl,fun x => by simp [iteratedFDeriv_succ_const]⟩

theorem AllDerivativesBounded.add {f g : E → F} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (hBf : AllDerivativesBounded f) (hBg : AllDerivativesBounded g) :
    AllDerivativesBounded (fun x => f x + g x) := by
  intro n
  obtain ⟨C,hC,hCf⟩ := hBf n
  obtain ⟨D,hD,hDg⟩ := hBg n
  refine ⟨C+D,add_nonneg hC hD,fun x => ?_⟩
  have hfn : ContDiff ℝ n f := hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)
  have hgn : ContDiff ℝ n g := hg.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)
  rw [fun_iteratedFDeriv_add_apply hfn.contDiffAt hgn.contDiffAt]
  exact (norm_add_le _ _).trans (add_le_add (hCf x) (hDg x))

theorem AllDerivativesBounded.const_smul {f : E → F} (hf : ContDiff ℝ ∞ f)
    (hBf : AllDerivativesBounded f) (a : ℝ) : AllDerivativesBounded (fun x => a • f x) := by
  intro n
  obtain ⟨C,hC,hCf⟩ := hBf n
  refine ⟨‖a‖*C,mul_nonneg (norm_nonneg _) hC,fun x => ?_⟩
  have hfn : ContDiff ℝ n f := hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)
  rw [iteratedFDeriv_const_smul_apply' hfn.contDiffAt, norm_smul]
  exact mul_le_mul_of_nonneg_left (hCf x) (norm_nonneg _)

/-- Bounded outer derivatives and bounded positive-order inner derivatives
imply bounded derivatives of the composition; the inner values need not be bounded. -/
theorem AllDerivativesBounded.comp_of_fderiv {f : E → F} {g : D → E}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hBf : AllDerivativesBounded f) (hBg : AllDerivativesBounded (_root_.fderiv ℝ g)) :
    AllDerivativesBounded (f ∘ g) := by
  classical
  choose C hC hCf using hBf
  choose B hB hBg' using hBg
  intro n
  let Cn : ℝ := ∑ i ∈ Finset.range (n+1), C i
  let Bn : ℝ := 1 + ∑ i ∈ Finset.range n, B i
  have hCn : 0 ≤ Cn := Finset.sum_nonneg fun i _ => hC i
  have hBn : 1 ≤ Bn := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => hB i)
  refine ⟨(n.factorial : ℝ)*Cn*Bn^n, by positivity, fun x => ?_⟩
  apply norm_iteratedFDeriv_comp_le hf hg (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)
  · intro i hi
    exact (hCf i (g x)).trans (Finset.single_le_sum (fun j _ => hC j)
      (Finset.mem_range.mpr (by omega)))
  · intro i hi hin
    have hei : i = (i-1)+1 := by omega
    have hb : ‖iteratedFDeriv ℝ i g x‖ ≤ B (i-1) := by
      rw [hei, ← norm_iteratedFDeriv_fderiv]
      exact hBg' (i-1) x
    have hbi : B (i-1) ≤ Bn := by
      apply le_trans (Finset.single_le_sum (fun j _ => hB j)
        (Finset.mem_range.mpr (by omega : i-1<n)))
      dsimp [Bn]
      linarith
    have hp : Bn ≤ Bn^i := by
      simpa only [pow_one] using pow_le_pow_right₀ hBn hi
    exact hb.trans (hbi.trans hp)

end SharpWasserstein.NoiseAverage
