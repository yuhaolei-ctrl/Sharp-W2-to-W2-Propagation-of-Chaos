/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
Adapted for Mathlib v4.35.0-rc3 in Sharp-W2-to-W2-Propagation-of-Chaos.
-/
module

public import KolmogorovExtension4.KolmogorovExtension
public import Mathlib.Probability.BrownianMotion.GaussianProjectiveFamily
public import Mathlib.Probability.HasLaw

/-!
# Pre-Brownian motion as a projective limit

The finite-dimensional distributions of the Brownian motion, together with their basic
properties (`brownianCovMatrix`, `gaussianProjectiveFamily`, its projectivity, the laws of its
evaluations and increments, its covariances...) have been upstreamed to Mathlib as
`ProbabilityTheory.BrownianReal.covMatrix` and `ProbabilityTheory.BrownianReal.projectiveFamily`
(`Mathlib.Probability.BrownianMotion.GaussianProjectiveFamily`). We use Mathlib's version here,
and only define the projective limit `gaussianLimit` of that family, which requires the
Kolmogorov extension theorem (not yet in Mathlib).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

open BrownianReal

@[deprecated BrownianReal.covMatrix (since := "2026-10-06")]
alias brownianCovMatrix := BrownianReal.covMatrix

@[deprecated BrownianReal.projectiveFamily (since := "2026-10-06")]
alias gaussianProjectiveFamily := BrownianReal.projectiveFamily

@[deprecated BrownianReal.isProjectiveMeasureFamily_projectiveFamily (since := "2026-10-06")]
alias isProjectiveMeasureFamily_gaussianProjectiveFamily :=
  BrownianReal.isProjectiveMeasureFamily_projectiveFamily

@[deprecated BrownianReal.measurePreserving_restrict_projectiveFamily (since := "2026-10-06")]
alias measurePreserving_restrict_gaussianProjectiveFamily :=
  BrownianReal.measurePreserving_restrict_projectiveFamily

/-- The law of the (pre-)Brownian motion on `ℝ≥0 → ℝ`: the projective limit of the
finite-dimensional distributions `BrownianReal.projectiveFamily`. -/
noncomputable
def gaussianLimit : Measure (ℝ≥0 → ℝ) :=
  projectiveLimit projectiveFamily isProjectiveMeasureFamily_projectiveFamily

instance IsProbabilityMeasure_gaussianLimit :
    IsProbabilityMeasure gaussianLimit :=
  isProbabilityMeasure_projectiveLimit isProjectiveMeasureFamily_projectiveFamily

lemma isProjectiveLimit_gaussianLimit :
    IsProjectiveLimit gaussianLimit projectiveFamily :=
  isProjectiveLimit_projectiveLimit isProjectiveMeasureFamily_projectiveFamily

lemma _root_.MeasureTheory.IsProjectiveLimit.hasLaw_restrict {ι : Type*} {X : ι → Type*}
    {mX : ∀ i, MeasurableSpace (X i)} {μ : Measure (Π i, X i)}
    {P : (I : Finset ι) → Measure (Π i : I, X i)} (h : IsProjectiveLimit μ P) {I : Finset ι} :
    HasLaw I.restrict (P I) μ where
  map_eq := h I

lemma hasLaw_restrict_gaussianLimit {I : Finset ℝ≥0} :
    HasLaw I.restrict (projectiveFamily I) gaussianLimit :=
  isProjectiveLimit_gaussianLimit.hasLaw_restrict

lemma hasLaw_eval_gaussianLimit {t : ℝ≥0} :
    HasLaw (fun x ↦ x t) (gaussianReal 0 t) gaussianLimit :=
  (measurePreserving_eval_projectiveFamily (⟨t, by simp⟩ : ({t} : Finset ℝ≥0))).hasLaw.comp
    hasLaw_restrict_gaussianLimit

lemma covariance_eval_gaussianLimit {s t : ℝ≥0} :
    cov[fun x ↦ x s, fun x ↦ x t; gaussianLimit] = min s t := by
  convert (hasLaw_restrict_gaussianLimit (I := {s, t})).covariance_fun_comp
    (f := Function.eval ⟨s, by simp⟩) (g := Function.eval ⟨t, by simp⟩) ?_ ?_
  · rfl
  · rfl
  · rw [covariance_eval_projectiveFamily]
  all_goals exact Measurable.aemeasurable (by fun_prop)

end ProbabilityTheory
