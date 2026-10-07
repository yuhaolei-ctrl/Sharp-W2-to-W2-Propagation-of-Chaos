module

public import SharpWasserstein.Compat
public import SharpWasserstein.NoiseAverageDerivatives

@[expose] public section

/-! Probability translation averages preserve actual smoothness of every order
and global bounds on all iterated Fréchet derivatives. This is a dominated
Bochner-integral proof, suitable for periodic kernels and backward Euler tests. -/
noncomputable section
open MeasureTheory
open scoped Topology NNReal ContDiff
namespace SharpWasserstein.NoiseAverage
universe u v
variable {Ω : Type v} {E F : Type u} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Ω → E) (hξ : StronglyMeasurable ξ)

/-- Every actual iterated Fréchet derivative has a global finite bound. -/
def AllDerivativesBounded (f : E → F) : Prop :=
  ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ C

theorem AllDerivativesBounded.fderiv {f : E → F} (h : AllDerivativesBounded f) :
    AllDerivativesBounded (fderiv ℝ f) := by
  intro n
  obtain ⟨C,hC,hb⟩ := h (n+1)
  exact ⟨C,hC,fun x => by rw [norm_iteratedFDeriv_fderiv]; exact hb x⟩

theorem AllDerivativesBounded.bounded {f : E → F} (h : AllDerivativesBounded f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C := by
  simpa only [norm_iteratedFDeriv_zero] using h 0

theorem AllDerivativesBounded.lipschitz {f : E → F} (h : AllDerivativesBounded f)
    (hf : Differentiable ℝ f) : ∃ L : ℝ≥0, LipschitzWith L f := by
  obtain ⟨C,hC,hb⟩ := h.fderiv.bounded
  exact ⟨⟨C,hC⟩, lipschitzWith_of_nnnorm_fderiv_le hf (fun x => by exact_mod_cast hb x)⟩

include hξ in
/-- Finite-order induction for the actual probability integral, including a
bound on that derivative. The induction differentiates the real integrand. -/
theorem contDiff_nat_average_bounded (n : ℕ) {f : E → F}
    (hf : ContDiff ℝ ∞ f) (hB : AllDerivativesBounded f) :
    ContDiff ℝ (n : ℕ) (average μ ξ f) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ n (average μ ξ f) x‖ ≤ C := by
  induction n generalizing F with
  | zero =>
    obtain ⟨C,hC,hb⟩ := hB.bounded
    exact ⟨contDiff_zero.mpr (continuous_average μ ξ hξ hf.continuous hb), C,hC,
      fun x => by rw [norm_iteratedFDeriv_zero]; exact norm_average_le μ ξ hb x⟩
  | succ n ih =>
    obtain ⟨C,hC,hb⟩ := hB.bounded
    obtain ⟨L,hL⟩ := hB.lipschitz (hf.differentiable (by simp))
    have hf₁ : ContDiff ℝ 1 f := hf.of_le (by simp)
    have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := (contDiff_infty_iff_fderiv.mp hf).2
    obtain ⟨havgDf,D,hD,hDb⟩ := ih hdf hB.fderiv
    have heq := fderiv_average μ ξ hξ hf₁ hL hb
    constructor
    · have hc : ContDiff ℝ ((n : WithTop ℕ∞)+1) (average μ ξ f) := by
        apply contDiff_succ_iff_fderiv.mpr
        refine ⟨fun x => (hasFDerivAt_average μ ξ hξ hf₁ hL hb x).differentiableAt, ?_, ?_⟩
        · simp
        · rw [heq]
          exact havgDf
      simpa only [Nat.cast_add, Nat.cast_one] using hc
    · refine ⟨D,hD,fun x => ?_⟩
      rw [← norm_iteratedFDeriv_fderiv, heq]
      exact hDb x

include hξ in
theorem contDiff_infty_average {f : E → F}
    (hf : ContDiff ℝ ∞ f) (hB : AllDerivativesBounded f) :
    ContDiff ℝ ∞ (average μ ξ f) :=
  contDiff_infty.mpr fun n => (contDiff_nat_average_bounded μ ξ hξ n hf hB).1

include hξ in
theorem allDerivativesBounded_average {f : E → F}
    (hf : ContDiff ℝ ∞ f) (hB : AllDerivativesBounded f) :
    AllDerivativesBounded (average μ ξ f) :=
  fun n => (contDiff_nat_average_bounded μ ξ hξ n hf hB).2

end SharpWasserstein.NoiseAverage
