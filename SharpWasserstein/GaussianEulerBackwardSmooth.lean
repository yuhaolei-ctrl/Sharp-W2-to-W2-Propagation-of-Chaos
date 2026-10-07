module

public import SharpWasserstein.Compat
public import SharpWasserstein.GaussianEulerBackwardSecond
public import SharpWasserstein.BoundedDerivativeComposition

@[expose] public section

/-! Every finite Gaussian Euler backward test is genuinely C∞ with bounded
iterated derivatives when the drift and terminal test have that regularity. -/
noncomputable section
open MeasureTheory
open scoped Topology NNReal ContDiff
namespace SharpWasserstein.BackwardEuler
open GaussianSharpness NoiseAverage
variable {d N : ℕ}
local instance standardLabels_probability_smooth (k : ℕ) : IsProbabilityMeasure (standardLabels k) :=
  standardLabels_probability k

theorem allDerivativesBounded_fderiv_mean {b : Configuration d N → Configuration d N}
    (hb : ContDiff ℝ ∞ b) (hB : AllDerivativesBounded b) (δ : ℝ≥0) :
    AllDerivativesBounded (fderiv ℝ (mean b δ)) := by
  have hdf := (contDiff_infty_iff_fderiv.mp hb).2
  have he : fderiv ℝ (mean b δ) = fun x => ContinuousLinearMap.id ℝ (Configuration d N) +
      (δ:ℝ) • fderiv ℝ b x := funext (fderiv_mean (hb.differentiable (by simp)) δ)
  rw [he]
  exact AllDerivativesBounded.add contDiff_const (hdf.const_smul (δ:ℝ))
    (allDerivativesBounded_const _) (hB.fderiv.const_smul hdf (δ:ℝ))

theorem smooth_step {b : Configuration d N → Configuration d N}
    (hb : ContDiff ℝ ∞ b) (hB : AllDerivativesBounded b) (δ : ℝ≥0)
    {φ : Configuration d N → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφB : AllDerivativesBounded φ) :
    ContDiff ℝ ∞ (step b δ φ) ∧ AllDerivativesBounded (step b δ φ) := by
  have hA := NoiseAverage.contDiff_infty_average (standardLabels (N*d+1)) (noise δ)
    (noise_stronglyMeasurable δ) hφ hφB
  have hAB := NoiseAverage.allDerivativesBounded_average (standardLabels (N*d+1)) (noise δ)
    (noise_stronglyMeasurable δ) hφ hφB
  have hm : ContDiff ℝ ∞ (mean b δ) := contDiff_id.add (hb.const_smul (δ:ℝ))
  exact ⟨hA.comp hm, hAB.comp_of_fderiv hA hm (allDerivativesBounded_fderiv_mean hb hB δ)⟩

/-- All smoothness and derivative boundedness required to use backward Euler
tests in the actual weak equation is derived for the constructed integral. -/
theorem smooth_backward {b : Configuration d N → Configuration d N}
    (hb : ContDiff ℝ ∞ b) (hB : AllDerivativesBounded b) (δ : ℝ≥0)
    {φ : Configuration d N → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφB : AllDerivativesBounded φ) (n : ℕ) :
    ContDiff ℝ ∞ (backward b δ φ n) ∧ AllDerivativesBounded (backward b δ φ n) := by
  induction n with
  | zero => exact ⟨hφ,hφB⟩
  | succ n ih => exact smooth_step hb hB δ ih.1 ih.2

end SharpWasserstein.BackwardEuler
