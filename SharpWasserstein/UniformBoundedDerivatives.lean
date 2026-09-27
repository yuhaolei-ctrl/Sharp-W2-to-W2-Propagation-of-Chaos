import SharpWasserstein.BoundedDerivativeLinear
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! Uniform bounds on the actual spatial derivatives of parameterized
functions. These bounds are preserved by probability averaging and the
linear coordinate operations used by the prescribed reference drift. -/
noncomputable section
open MeasureTheory
open scoped NNReal ContDiff BigOperators
namespace SharpWasserstein.NoiseAverage
variable {I D E F : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

def UniformAllDerivativesBounded (f : I → E → F) : Prop :=
  ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t x, ‖iteratedFDeriv ℝ n (f t) x‖ ≤ C

theorem UniformAllDerivativesBounded.at {f : I → E → F}
    (h : UniformAllDerivativesBounded f) (t : I) : AllDerivativesBounded (f t) := by
  intro n
  obtain ⟨C,hC,hb⟩ := h n
  exact ⟨C,hC,hb t⟩

theorem UniformAllDerivativesBounded.fderiv {f : I → E → F}
    (h : UniformAllDerivativesBounded f) : UniformAllDerivativesBounded (fun t => _root_.fderiv ℝ (f t)) := by
  intro n
  obtain ⟨C,hC,hb⟩ := h (n+1)
  exact ⟨C,hC,fun t x => by rw [norm_iteratedFDeriv_fderiv]; exact hb t x⟩

theorem UniformAllDerivativesBounded.bounded {f : I → E → F}
    (h : UniformAllDerivativesBounded f) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t x, ‖f t x‖ ≤ C := by
  simpa only [norm_iteratedFDeriv_zero] using h 0

theorem UniformAllDerivativesBounded.lipschitz {f : I → E → F}
    (h : UniformAllDerivativesBounded f) (hf : ∀ t, Differentiable ℝ (f t)) :
    ∃ L : ℝ≥0, ∀ t, LipschitzWith L (f t) := by
  obtain ⟨C,hC,hb⟩ := h.fderiv.bounded
  exact ⟨⟨C,hC⟩,fun t => lipschitzWith_of_nnnorm_fderiv_le (hf t) (fun x => by exact_mod_cast hb t x)⟩

theorem UniformAllDerivativesBounded.comp_linear {f : I → E → F}
    (hf : ∀ t, ContDiff ℝ ∞ (f t)) (hB : UniformAllDerivativesBounded f) (L : D →L[ℝ] E) :
    UniformAllDerivativesBounded (fun t x => f t (L x)) := by
  intro n
  obtain ⟨C,hC,hb⟩ := hB n
  refine ⟨C*‖L‖^n,by positivity,fun t x => ?_⟩
  change ‖iteratedFDeriv ℝ n (f t ∘ L) x‖ ≤ C*‖L‖^n
  rw [L.iteratedFDeriv_comp_right (hf t) x (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)]
  exact (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
    (by simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
      mul_le_mul_of_nonneg_right (hb t (L x)) (pow_nonneg (norm_nonneg L) n))

theorem UniformAllDerivativesBounded.linear_comp {f : I → D → E}
    (hf : ∀ t, ContDiff ℝ ∞ (f t)) (hB : UniformAllDerivativesBounded f) (L : E →L[ℝ] F) :
    UniformAllDerivativesBounded (fun t x => L (f t x)) := by
  intro n
  obtain ⟨C,hC,hb⟩ := hB n
  refine ⟨‖L‖*C,by positivity,fun t x => ?_⟩
  exact (L.norm_iteratedFDeriv_comp_left (hf t).contDiffAt
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).trans
      (mul_le_mul_of_nonneg_left (hb t x) (norm_nonneg _))

theorem UniformAllDerivativesBounded.sum {ι : Type} [Fintype ι] {f : ι → I → E → F}
    (hf : ∀ i t, ContDiff ℝ ∞ (f i t)) (hB : ∀ i, UniformAllDerivativesBounded (f i)) :
    UniformAllDerivativesBounded (fun t x => ∑ i, f i t x) := by
  classical
  intro n
  choose C hC hb using (fun i => hB i n)
  refine ⟨∑ i, C i,Finset.sum_nonneg (fun i _ => hC i),fun t x => ?_⟩
  rw [iteratedFDeriv_fun_sum_apply (fun i _ =>
    ((hf i t).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt)]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => hb i t x))

theorem norm_iteratedFDeriv_average_le {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Ω → E) (hξ : StronglyMeasurable ξ)
    (n : ℕ) {f : E → F} (hf : ContDiff ℝ ∞ f) (hB : AllDerivativesBounded f)
    {C : ℝ} (hC : ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ C) (x : E) :
    ‖iteratedFDeriv ℝ n (average μ ξ f) x‖ ≤ C := by
  induction n generalizing F with
  | zero =>
    rw [norm_iteratedFDeriv_zero]
    exact norm_average_le μ ξ (fun y => by simpa only [norm_iteratedFDeriv_zero] using hC y) x
  | succ n ih =>
    have hdf := (contDiff_infty_iff_fderiv.mp hf).2
    obtain ⟨A,_,hA⟩ := hB.bounded
    obtain ⟨L,hL⟩ := hB.lipschitz (hf.differentiable (by simp))
    rw [← norm_iteratedFDeriv_fderiv,fderiv_average μ ξ hξ
      (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)) hL hA]
    exact ih hdf hB.fderiv (fun y => by rw [norm_iteratedFDeriv_fderiv]; exact hC y)

theorem uniformAllDerivativesBounded_average {Ω : Type} [MeasurableSpace Ω]
    (μ : I → ProbabilityMeasure Ω) (ξ : Ω → E) (hξ : StronglyMeasurable ξ)
    {f : E → F} (hf : ContDiff ℝ ∞ f) (hB : AllDerivativesBounded f) :
    UniformAllDerivativesBounded (fun t => average (μ t : Measure Ω) ξ f) := by
  intro n
  obtain ⟨C,hC,hb⟩ := hB n
  exact ⟨C,hC,fun t x => norm_iteratedFDeriv_average_le (μ t : Measure Ω) ξ hξ n hf hB hb x⟩

end SharpWasserstein.NoiseAverage
