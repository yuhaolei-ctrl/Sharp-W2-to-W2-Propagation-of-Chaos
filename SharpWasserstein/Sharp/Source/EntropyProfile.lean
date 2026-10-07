/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import SharpWasserstein.Sharp.Source.ReferenceDrift
public import SharpWasserstein.PrescribedEntropyProfile

/-!
# Entropy of the reference evolution (Lemma 4.3)

Lemma 4.3 (`lem:reference-H`) of the paper: for `0 < s ≤ T` and `1 ≤ m ≤ N`,
`h_m(s) = H(R^{(m)}_s | μ_s^{⊗m}) ≤ C₀ β_L(s) m²/N² ≤ (C₀ D_T / s) m²/N²`, where
`β_L(s) = (1 + Ls + L²s²/3)/(4s)` is the entropy–cost coefficient of Lemma 4.1
(`lem:entropy-cost`, `RegularizationRates.bridgeCost`) and `L = L_a + L₁`.

The development proves the entropy–cost inequality for a drift whose Euclidean conjugate is
`L`-Lipschitz (`DecoupledFlow.regularized_marginal_klDiv_le`). The older instance
`PrescribedReference.marginal_klDiv_le_initial_profile` feeds it the sup-norm Lipschitz constant
of the drift multiplied by `√d`; here it is fed the Euclidean Lipschitz constant `L = L_a + L₁`
of the reference drift (`IsSmoothCoefficients.lipschitzWith_euclideanDrift_singleDrift`), which
is the constant of the paper.

## Main statements

* `marginal_klDiv_le_sharp`: `H(R^{(m)}_t | μ_t^{⊗m}) ≤ β_L(t) C₀ m²/N²`.
* `marginalEntropy_le_sharp`: the same for the real-valued entropy sequence used by the source
  estimates.
* `marginalEntropy_le_horizon`: `h_m(t) ≤ (D_T / t) C₀ m²/N²` for `0 < t ≤ T`.
* `klDiv_ne_top`: the full entropy `H(R^N_t | μ_t^{⊗N})` is finite.
-/

@[expose] public section

noncomputable section

open MeasureTheory InformationTheory
open scoped NNReal ENNReal

namespace SharpWasserstein.Sharp.Source

variable {d : ℕ} {a : Position d → Position d} {K : Position d → Position d → Position d}
  {La L₁ L₂ M Mb Lb₁ Lb₂ : ℝ} (hS : IsSmoothCoefficients a K La L₁ L₂ M)
  (hb : BoundedSmoothKernel (kernelOf a K)) (hbound : KernelBounds (kernelOf a K) Mb Lb₁ Lb₂)
  (hMb : 0 ≤ Mb) (hLb₁ : 0 ≤ Lb₁)
  {μ : ℝ → Measure (Position d)} (hμ : IsLimitEvolution (kernelOf a K) μ)
  {N : ℕ} (P : Measure (Configuration d N)) [IsProbabilityMeasure P]

include hS in
/-- **Lemma 4.3 (`lem:reference-H`), entropy form.** For `t > 0`, every marginal of the reference
evolution satisfies `H(R^{(m)}_t | μ_t^{⊗m}) ≤ β_L(t) C₀ m²/N²`, with `L = L_a + L₁`. -/
theorem marginal_klDiv_le_sharp (hP : HasSecondMoment P) {t : ℝ} (ht : 0 < t) {C₀ : ℝ}
    (hC₀ : 0 ≤ C₀)
    (hinit : ∀ m, ∀ hm : m ≤ N, wassersteinSq (marginal hm P) (tensorLaw (μ 0) m) ≤
      ENNReal.ofReal (C₀ * (m : ℝ) ^ 2 / (N : ℝ) ^ 2)) (m : ℕ) (hm : m ≤ N) :
    klDiv (marginal hm (PrescribedReference.law hb hbound hMb hLb₁ hμ N P t))
        (tensorLaw (μ t) m) ≤
      ENNReal.ofReal ((RegularizationRates.bridgeCost (lipL La L₁) t * C₀) *
        (m : ℝ) ^ 2 / (N : ℝ) ^ 2) := by
  have := hμ.1 0 le_rfl
  have hh := DecoupledFlow.regularized_marginal_klDiv_le
    (PrescribedReference.singleDrift_continuous hb hbound hLb₁ hμ)
    (PrescribedReference.singleDrift_bound hbound hMb hμ)
    (PrescribedReference.singleDrift_lipschitz hb hbound hLb₁ hμ) P (μ 0) hP
    (IsLimitEvolution.initial_integrable_positionSq hμ)
    (IsSmoothCoefficients.lipschitzWith_euclideanDrift_singleDrift hS hμ) ht hC₀ hinit m hm
  rw [PrescribedReference.singleBrownianLaw_eq_supplied hb hbound hMb hLb₁ hμ ht,
    coe_lipLNN hS.assumptionA.La_nonneg hS.assumptionA.L₁_nonneg] at hh
  rw [PrescribedReference.law_eq_decoupled hb hbound hMb hLb₁ hμ N P ht]
  exact hh

/-- `β_L(t) ≥ 0` for `L ≥ 0` and `t ≥ 0`. -/
theorem bridgeCost_nonneg {L t : ℝ} (hL : 0 ≤ L) (ht : 0 ≤ t) :
    0 ≤ RegularizationRates.bridgeCost L t := by
  unfold RegularizationRates.bridgeCost
  positivity

include hS in
/-- **Lemma 4.3 (`lem:reference-H`).** The real-valued marginal entropies
`h_m(t) = H(R^{(m)}_t | μ_t^{⊗m})` of the reference evolution satisfy
`h_m(t) ≤ β_L(t) C₀ m²/N²` for every `m ≤ N`. -/
theorem marginalEntropy_le_sharp (hP : HasSecondMoment P) {t : ℝ} (ht : 0 < t) {C₀ : ℝ}
    (hC₀ : 0 ≤ C₀)
    (hinit : ∀ m, ∀ hm : m ≤ N, wassersteinSq (marginal hm P) (tensorLaw (μ 0) m) ≤
      ENNReal.ofReal (C₀ * (m : ℝ) ^ 2 / (N : ℝ) ^ 2)) (m : ℕ) (hm : m ≤ N) :
    marginalEntropy (PrescribedReference.law hb hbound hMb hLb₁ hμ N P t) (μ t) m ≤
      (RegularizationRates.bridgeCost (lipL La L₁) t * C₀) * (m : ℝ) ^ 2 / (N : ℝ) ^ 2 := by
  rw [marginalEntropy_eq hm]
  have hL := lipL_nonneg hS.assumptionA.La_nonneg hS.assumptionA.L₁_nonneg
  have := bridgeCost_nonneg hL ht.le
  exact ENNReal.toReal_le_of_le_ofReal (by positivity)
    (marginal_klDiv_le_sharp hS hb hbound hMb hLb₁ hμ P hP ht hC₀ hinit m hm)

include hS in
/-- **Lemma 4.3 (`eq:ref-H`), second inequality.** For `0 < t ≤ T`,
`h_m(t) ≤ (D_T / t) C₀ m²/N²`. -/
theorem marginalEntropy_le_horizon (hP : HasSecondMoment P) {t T : ℝ} (ht : 0 < t) (htT : t ≤ T)
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hinit : ∀ m, ∀ hm : m ≤ N, wassersteinSq (marginal hm P) (tensorLaw (μ 0) m) ≤
      ENNReal.ofReal (C₀ * (m : ℝ) ^ 2 / (N : ℝ) ^ 2)) (m : ℕ) (hm : m ≤ N) :
    marginalEntropy (PrescribedReference.law hb hbound hMb hLb₁ hμ N P t) (μ t) m ≤
      (horizonFactor T La L₁ / t * C₀) * (m : ℝ) ^ 2 / (N : ℝ) ^ 2 := by
  refine (marginalEntropy_le_sharp hS hb hbound hMb hLb₁ hμ P hP ht hC₀ hinit m hm).trans ?_
  have hβ := bridgeCost_le_horizonFactor_div hS.assumptionA.La_nonneg hS.assumptionA.L₁_nonneg
    ht htT
  have hβ' : RegularizationRates.bridgeCost (lipL La L₁) t ≤ horizonFactor T La L₁ / t := hβ
  gcongr

include hS in
/-- The full entropy `H(R^N_t | μ_t^{⊗N})` of the reference evolution is finite for `t > 0`,
even when `H(P_{N,0} | μ_0^{⊗N}) = ∞`. -/
theorem klDiv_ne_top (hP : HasSecondMoment P) {t : ℝ} (ht : 0 < t) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hinit : ∀ m, ∀ hm : m ≤ N, wassersteinSq (marginal hm P) (tensorLaw (μ 0) m) ≤
      ENNReal.ofReal (C₀ * (m : ℝ) ^ 2 / (N : ℝ) ^ 2)) :
    klDiv (PrescribedReference.law hb hbound hMb hLb₁ hμ N P t) (tensorLaw (μ t) N) ≠ ∞ := by
  have h := marginal_klDiv_le_sharp hS hb hbound hMb hLb₁ hμ P hP ht hC₀ hinit N le_rfl
  rw [marginal_self] at h
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h

end SharpWasserstein.Sharp.Source
