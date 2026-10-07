/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Bounds for convolutions with smooth bump functions

This file collects the analytic facts about mollification used in the smooth approximation lemma
(Lemma 7.1, `lem:mollify`) of the paper *Sharp Wasserstein propagation of chaos from
correlated initial data*.

## Main results

* `SharpWasserstein.Sharp.norm_iteratedFDeriv_convolution_left_le`: if `f` is smooth with compact
  support and `‖g‖ ≤ C`, then `‖Dᵏ (f ⋆[L, μ] g) x‖ ≤ ‖L‖ * (∫ ‖Dᵏ f‖ dμ) * C`. In particular,
  the convolution of a bounded function with a test function has bounded derivatives of all
  orders (`SharpWasserstein.Sharp.exists_bound_iteratedFDeriv_convolution_left`).
* `SharpWasserstein.Sharp.norm_integral_smul_le`: Jensen's inequality for the norm, i.e. averaging
  against a probability density preserves pointwise norm bounds.
* `SharpWasserstein.Sharp.norm_normed_convolution_le` and
  `SharpWasserstein.Sharp.norm_normed_convolution_sub_le`: the convolution with a normalized
  bump function `φ.normed μ` preserves norm bounds and Lipschitz-type inequalities.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Function ContinuousLinearMap
open scoped Convolution ContDiff

namespace SharpWasserstein.Sharp

universe u

section DerivBounds

variable {G E F : Type u} {E' : Type*}
  [NormedAddCommGroup G] [NormedSpace ℝ G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure G} [SFinite μ] [μ.IsAddLeftInvariant] [μ.IsNegInvariant]
  [IsFiniteMeasureOnCompacts μ]

/-- **Derivatives of a convolution.** If `f` is smooth with compact support and `g` is locally
integrable with `‖g‖ ≤ C`, then every iterated derivative of `f ⋆[L, μ] g` is bounded:
`‖Dᵏ (f ⋆[L, μ] g) x‖ ≤ ‖L‖ * (∫ ‖Dᵏ f‖ dμ) * C`.

The spaces `G`, `E` and `F` live in the same universe since the proof is an induction on `k`
which replaces `E`, `F` and `L` by `G →L[ℝ] E`, `G →L[ℝ] F` and `L.precompL G`. -/
theorem norm_iteratedFDeriv_convolution_left_le (L : E →L[ℝ] E' →L[ℝ] F) {f : G → E}
    {g : G → E'} {C : ℝ} (hcf : HasCompactSupport f) (hf : ContDiff ℝ ∞ f)
    (hg : LocallyIntegrable g μ) (hgC : ∀ x, ‖g x‖ ≤ C) (k : ℕ) (x : G) :
    ‖iteratedFDeriv ℝ k (f ⋆[L, μ] g) x‖ ≤ ‖L‖ * (∫ t, ‖iteratedFDeriv ℝ k f t‖ ∂μ) * C := by
  induction k generalizing E F with
  | zero =>
    simp only [norm_iteratedFDeriv_zero]
    calc ‖(f ⋆[L, μ] g) x‖ ≤ ∫ t, ‖L‖ * ‖f t‖ * C ∂μ := by
          rw [convolution_def]
          refine norm_integral_le_of_norm_le
            (((hf.continuous.integrable_of_hasCompactSupport hcf).norm.const_mul _).mul_const _)
            (ae_of_all _ fun t => (L.le_opNorm₂ _ _).trans ?_)
          gcongr
          exact hgC _
      _ = ‖L‖ * (∫ t, ‖f t‖ ∂μ) * C := by rw [integral_mul_const, integral_const_mul]
  | succ k ih =>
    have hC : 0 ≤ C := (norm_nonneg _).trans (hgC 0)
    have hderiv : fderiv ℝ (f ⋆[L, μ] g) = fderiv ℝ f ⋆[L.precompL G, μ] g := by
      funext y
      exact (hcf.hasFDerivAt_convolution_left L (hf.of_le (by simp)) hg y).fderiv
    rw [← norm_iteratedFDeriv_fderiv, hderiv]
    -- The norm of `L.precompL G` is only accessed through `ih` and `norm_precompL_le`, since
    -- elaborating `‖L.precompL G‖` directly runs into an instance mismatch.
    refine (ih (L.precompL G) (hcf.fderiv ℝ) (hf.fderiv_right (by simp))).trans ?_
    simp_rw [norm_iteratedFDeriv_fderiv]
    have hI : 0 ≤ ∫ t, ‖iteratedFDeriv ℝ (k + 1) f t‖ ∂μ := integral_nonneg fun _ => norm_nonneg _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (norm_precompL_le G L) hI) hC

/-- If `f` is smooth with compact support and `g` is bounded and locally integrable, then every
iterated derivative of `f ⋆[L, μ] g` is bounded. -/
theorem exists_bound_iteratedFDeriv_convolution_left (L : E →L[ℝ] E' →L[ℝ] F) {f : G → E}
    {g : G → E'} (hcf : HasCompactSupport f) (hf : ContDiff ℝ ∞ f) (hg : LocallyIntegrable g μ)
    (hgb : ∃ C, ∀ x, ‖g x‖ ≤ C) (k : ℕ) :
    ∃ C, ∀ x, ‖iteratedFDeriv ℝ k (f ⋆[L, μ] g) x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hgb
  exact ⟨_, norm_iteratedFDeriv_convolution_left_le L hcf hf hg hC k⟩

end DerivBounds

section Jensen

variable {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure α}

/-- **Jensen's inequality for the norm.** If `ρ` is a probability density supported in `s` and
`‖h t‖ ≤ c` for all `t ∈ s`, then `‖∫ ρ t • h t dμ‖ ≤ c`. -/
theorem norm_integral_smul_le {ρ : α → ℝ} {h : α → F} {s : Set α} {c : ℝ}
    (hρ : ∀ t, 0 ≤ ρ t) (hρi : Integrable ρ μ) (hρ1 : ∫ t, ρ t ∂μ = 1) (hs : support ρ ⊆ s)
    (hc : ∀ t ∈ s, ‖h t‖ ≤ c) : ‖∫ t, ρ t • h t ∂μ‖ ≤ c := by
  calc ‖∫ t, ρ t • h t ∂μ‖ ≤ ∫ t, ρ t * c ∂μ :=
        norm_integral_le_of_norm_le (hρi.mul_const c) (ae_of_all _ fun t => ?_)
    _ = c := by rw [integral_mul_const, hρ1, one_mul]
  rw [norm_smul, Real.norm_of_nonneg (hρ t)]
  by_cases ht : ρ t = 0
  · simp [ht]
  · exact mul_le_mul_of_nonneg_left (hc t (hs ht)) (hρ t)

end Jensen

section Bump

variable {G F : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasurableSpace G] [BorelSpace G] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure G} [μ.IsAddHaarMeasure] (φ : ContDiffBump (0 : G))

/-- The convolution with a normalized bump function `φ` preserves norm bounds: if
`‖g (x - t)‖ ≤ c` whenever `‖t‖ < φ.rOut`, then `‖(φ.normed μ ⋆ g) x‖ ≤ c`. -/
theorem norm_normed_convolution_le {g : G → F} {x : G} {c : ℝ}
    (hg : ∀ t ∈ ball (0 : G) φ.rOut, ‖g (x - t)‖ ≤ c) :
    ‖(φ.normed μ ⋆[lsmul ℝ ℝ, μ] g) x‖ ≤ c := by
  rw [convolution_lsmul]
  exact norm_integral_smul_le φ.nonneg_normed φ.integrable_normed (φ.integral_normed (μ := μ))
    φ.support_normed_eq.subset hg

/-- The convolution with a normalized bump function `φ` preserves Lipschitz-type inequalities:
if `‖g₁ (x - t) - g₂ (x' - t)‖ ≤ c` whenever `‖t‖ < φ.rOut`, then
`‖(φ.normed μ ⋆ g₁) x - (φ.normed μ ⋆ g₂) x'‖ ≤ c`. -/
theorem norm_normed_convolution_sub_le {g₁ g₂ : G → F} (hg₁ : LocallyIntegrable g₁ μ)
    (hg₂ : LocallyIntegrable g₂ μ) {x x' : G} {c : ℝ}
    (hg : ∀ t ∈ ball (0 : G) φ.rOut, ‖g₁ (x - t) - g₂ (x' - t)‖ ≤ c) :
    ‖(φ.normed μ ⋆[lsmul ℝ ℝ, μ] g₁) x - (φ.normed μ ⋆[lsmul ℝ ℝ, μ] g₂) x'‖ ≤ c := by
  have h₁ := ((φ.hasCompactSupport_normed (μ := μ)).convolutionExists_left (lsmul ℝ ℝ)
    φ.continuous_normed hg₁ x).integrable
  have h₂ := ((φ.hasCompactSupport_normed (μ := μ)).convolutionExists_left (lsmul ℝ ℝ)
    φ.continuous_normed hg₂ x').integrable
  simp only [lsmul_apply] at h₁ h₂
  rw [convolution_lsmul, convolution_lsmul, ← integral_sub h₁ h₂]
  simp_rw [← smul_sub]
  exact norm_integral_smul_le φ.nonneg_normed φ.integrable_normed (φ.integral_normed (μ := μ))
    φ.support_normed_eq.subset hg

/-- The convolution of a locally integrable function with a normalized bump function is
smooth. -/
theorem contDiff_normed_convolution {g : G → F} (hg : LocallyIntegrable g μ) :
    ContDiff ℝ ∞ (φ.normed μ ⋆[lsmul ℝ ℝ, μ] g) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ) φ.contDiff_normed hg

end Bump

section BumpDeriv

variable {G F : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasurableSpace G] [BorelSpace G] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure G} [μ.IsAddHaarMeasure] (φ : ContDiffBump (0 : G))

/-- The convolution of a bounded locally integrable function with a normalized bump function has
bounded derivatives of all orders. -/
theorem exists_bound_iteratedFDeriv_normed_convolution {g : G → F} (hg : LocallyIntegrable g μ)
    (hgb : ∃ C, ∀ x, ‖g x‖ ≤ C) (k : ℕ) :
    ∃ C, ∀ x, ‖iteratedFDeriv ℝ k (φ.normed μ ⋆[lsmul ℝ ℝ, μ] g) x‖ ≤ C :=
  exists_bound_iteratedFDeriv_convolution_left (lsmul ℝ ℝ) φ.hasCompactSupport_normed
    φ.contDiff_normed hg hgb k

end BumpDeriv

end SharpWasserstein.Sharp
