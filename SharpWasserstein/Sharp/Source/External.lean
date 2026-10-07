/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import SharpWasserstein.Sharp.Source.EntropyProfile
public import SharpWasserstein.ExchangeableConditionalSource

/-!
# The external part of the source (Lemma 4.6)

For `m < N` let `γ_x` be the conditional law of `X_{m+1}` given `X_{1:m} = x` under the reference
evolution `R^N_s`. Since `c_s(xᵢ, ·)` has mean zero under `μ_s`, the conditional expectation
`E[c_s(xᵢ, X_{m+1}) | X_{1:m} = x]` is `∫ K(xᵢ, y) (γ_x - μ_s)(dy)`. Lemma 4.6 (`lem:external`)
of the paper bounds
`X_m(s) = α_m² ∑ᵢ E|E[c_s(Xᵢ, X_{m+1}) | X_{1:m}]|²`, `α_m = 1 - m/N`, by
`X_m(s) ≤ 8 M² C₀ β_L(s) m²/N² ≤ (A₁² / s) m²/N²`.

The proof combines Pinsker's inequality for vector observables bounded by `M` (`eq:pinsker`),
the chain rule (`eq:chain`), the monotonicity of the entropy increments of an exchangeable law
(Lemma 4.2, `lem:increments`) and Lemma 4.3. The development provides this combination for an
arbitrary Hilbert space of values (`exchangeable_conditional_source_quadratic_bound`); here it is
applied with values in `EuclideanSpace ℝ (Fin d)`, so that Pinsker's inequality is used once for
the Euclidean vector `K(xᵢ, y)` (bounded by `M`) and not coordinatewise.

## Main definitions

* `externalField hm R q K x i = ∫ K(xᵢ, y) γ_x(dy) - ∫ K(xᵢ, y) q(dy)`.

## Main statements

* `external_le`: the bound for an arbitrary exchangeable law with an entropy profile.
* `external_le_sharp`: **Lemma 4.6**, `X_m(s) ≤ 8 M² C₀ β_L(s) m²/N²`.
* `external_le_horizon`: `X_m(s) ≤ (A₁² / s) m²/N²` for `0 < s ≤ T`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace SharpWasserstein.Sharp.Source

variable {d m N : ℕ} {a : Position d → Position d} {K : Position d → Position d → Position d}
  {La L₁ L₂ M : ℝ}

/-- The external discrepancy `∫ K(xᵢ, y) γ_x(dy) - ∫ K(xᵢ, y) q(dy)` of Lemma 4.6, where `γ_x` is
the conditional law of the `(m+1)`-st particle of `R` given the first `m` particles `x`. With
`q = μ_s` it is the conditional expectation `E[c_s(xᵢ, X_{m+1}) | X_{1:m} = x]`. -/
def externalField (hm : m < N) (R : Measure (Configuration d N)) [IsProbabilityMeasure R]
    (q : Measure (Position d)) (K : Position d → Position d → Position d)
    (x : Configuration d m) (i : Fin m) : EuclideanSpace ℝ (Fin d) :=
  ∫ y, WithLp.toLp 2 (K (x i) y) ∂(nextParticleJoint hm R).condKernel x -
    ∫ y, WithLp.toLp 2 (K (x i) y) ∂q

/-- The sections `(x, y) ↦ toLp (K (x i) y)` are jointly strongly measurable. -/
theorem stronglyMeasurable_toLp_K_apply (hS : IsSmoothCoefficients a K La L₁ L₂ M) (i : Fin m) :
    StronglyMeasurable (Function.uncurry fun (x : Configuration d m) (y : Position d) =>
      WithLp.toLp 2 (K (x i) y)) := by
  have h := (IsSmoothCoefficients.measurable_toLp_K hS).comp
    (((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd :
      Measurable fun p : Configuration d m × Position d => (p.1 i, p.2))
  exact h.stronglyMeasurable

/-- Each component of the external discrepancy is measurable. -/
theorem measurable_externalField (hS : IsSmoothCoefficients a K La L₁ L₂ M) (hm : m < N)
    (R : Measure (Configuration d N)) [IsProbabilityMeasure R] (q : Measure (Position d))
    [IsProbabilityMeasure q] (i : Fin m) :
    Measurable fun x => externalField hm R q K x i := by
  have hF := stronglyMeasurable_toLp_K_apply hS i
  exact (hF.integral_kernel_prod_right.sub hF.integral_prod_right).measurable

/-- `|∫ K(xᵢ, y) (γ_x - q)(dy)| ≤ 2M`. -/
theorem norm_externalField_le (hS : IsSmoothCoefficients a K La L₁ L₂ M) (hm : m < N)
    (R : Measure (Configuration d N)) [IsProbabilityMeasure R] (q : Measure (Position d))
    [IsProbabilityMeasure q] (x : Configuration d m) (i : Fin m) :
    ‖externalField hm R q K x i‖ ≤ 2 * M := by
  have hK := IsSmoothCoefficients.norm_toLp_K_le hS (x i)
  have h₁ : ‖∫ y, WithLp.toLp 2 (K (x i) y) ∂(nextParticleJoint hm R).condKernel x‖ ≤ M := by
    simpa using norm_integral_le_of_norm_le_const
      (μ := (nextParticleJoint hm R).condKernel x) (ae_of_all _ hK)
  have h₂ : ‖∫ y, WithLp.toLp 2 (K (x i) y) ∂q‖ ≤ M := by
    simpa using norm_integral_le_of_norm_le_const (μ := q) (ae_of_all _ hK)
  calc _ ≤ _ := norm_sub_le _ _
    _ ≤ M + M := add_le_add h₁ h₂
    _ = 2 * M := by ring

/-- **Lemma 4.6 for an abstract exchangeable law.** If `R` is exchangeable, `H(R | q^{⊗N}) < ∞`
and the marginal entropies satisfy `h_j ≤ A j²/N²`, then for `0 < m < N`,
`(1 - m/N)² ∫ ∑ᵢ |∫ K(xᵢ, y) (γ_x - q)(dy)|² dR^{(m)} ≤ 8 M² A m²/N²`. -/
theorem external_le (hS : IsSmoothCoefficients a K La L₁ L₂ M) {R : Measure (Configuration d N)}
    [IsProbabilityMeasure R] {q : Measure (Position d)} [IsProbabilityMeasure q]
    (hex : Exchangeable R) (hfinite : klDiv R (tensorLaw q N) ≠ ∞) {A : ℝ} (hA : 0 ≤ A)
    (hprofile : ∀ j, j ≤ N → marginalEntropy R q j ≤ A * (j : ℝ) ^ 2 / (N : ℝ) ^ 2)
    (hm0 : 0 < m) (hm : m < N) :
    (((N : ℝ) - m) / N) ^ 2 * ∫ x, ∑ i, ‖externalField hm R q K x i‖ ^ 2 ∂marginal hm.le R ≤
      8 * M ^ 2 * A * (m : ℝ) ^ 2 / (N : ℝ) ^ 2 :=
  exchangeable_conditional_source_quadratic_bound (E := EuclideanSpace ℝ (Fin d)) hm0 hm hex
    hfinite hA hS.assumptionA.M_nonneg hprofile
    (F := fun i x y => WithLp.toLp 2 (K (x i) y)) (stronglyMeasurable_toLp_K_apply hS)
    (fun i => ae_of_all _ fun x => ae_of_all _ fun y =>
      IsSmoothCoefficients.norm_toLp_K_le hS (x i) y)

section Reference

variable {Mb Lb₁ Lb₂ : ℝ}
  (hb : BoundedSmoothKernel (kernelOf a K)) (hbound : KernelBounds (kernelOf a K) Mb Lb₁ Lb₂)
  (hMb : 0 ≤ Mb) (hLb₁ : 0 ≤ Lb₁)
  {μ : ℝ → Measure (Position d)} (hμ : IsLimitEvolution (kernelOf a K) μ)
  (P : Measure (Configuration d N)) [IsProbabilityMeasure P]

/-- The reference evolution of an exchangeable initial law is exchangeable. -/
theorem law_exchangeable (hex : Exchangeable P) {s : ℝ} (hs : 0 < s) :
    Exchangeable (PrescribedReference.law hb hbound hMb hLb₁ hμ N P s) := by
  rw [PrescribedReference.law_eq_decoupled hb hbound hMb hLb₁ hμ N P hs]
  exact DecoupledFlow.brownianLaw_exchangeable _ _ _ hs.le P hex

/-- The reference evolution is a probability law for `s > 0`. -/
theorem law_isProbabilityMeasure_of_pos {s : ℝ} (hs : 0 < s) :
    IsProbabilityMeasure (PrescribedReference.law hb hbound hMb hLb₁ hμ N P s) := by
  rw [PrescribedReference.law_eq_decoupled hb hbound hMb hLb₁ hμ N P hs]
  exact DecoupledFlow.brownianLaw_isProbability _ _ _ hs.le P

/-- **Lemma 4.6 (`lem:external`).** Let `R^N_s` be the reference evolution started from an
exchangeable `P` with `W²(P^{(j)}, μ_0^{⊗j}) ≤ C₀ j²/N²` for all `j ≤ N`. For `s > 0` and
`0 < m < N`, the external part of the source satisfies
`X_m(s) = (1 - m/N)² ∫ ∑ᵢ |∫ K(xᵢ, y) (γ_x - μ_s)(dy)|² dR^{(m)}_s ≤ 8 M² C₀ β_L(s) m²/N²`,
where `β_L(s)` is the entropy–cost coefficient with `L = L_a + L₁`. -/
theorem external_le_sharp (hS : IsSmoothCoefficients a K La L₁ L₂ M) (hP : HasSecondMoment P)
    (hex : Exchangeable P) {C₀ s : ℝ} (hC₀ : 0 ≤ C₀) (hs : 0 < s)
    (hinit : ∀ j, ∀ hj : j ≤ N, wassersteinSq (marginal hj P) (tensorLaw (μ 0) j) ≤
      ENNReal.ofReal (C₀ * (j : ℝ) ^ 2 / (N : ℝ) ^ 2)) (hm0 : 0 < m) (hm : m < N) :
    haveI := law_isProbabilityMeasure_of_pos hb hbound hMb hLb₁ hμ P hs
    (((N : ℝ) - m) / N) ^ 2 * ∫ x, ∑ i,
        ‖externalField hm (PrescribedReference.law hb hbound hMb hLb₁ hμ N P s) (μ s) K x i‖ ^ 2
        ∂marginal hm.le (PrescribedReference.law hb hbound hMb hLb₁ hμ N P s) ≤
      8 * M ^ 2 * C₀ * RegularizationRates.bridgeCost (lipL La L₁) s * (m : ℝ) ^ 2 /
        (N : ℝ) ^ 2 := by
  have := law_isProbabilityMeasure_of_pos hb hbound hMb hLb₁ hμ P hs
  have := hμ.1 s hs.le
  have hL := lipL_nonneg hS.assumptionA.La_nonneg hS.assumptionA.L₁_nonneg
  have hβ := bridgeCost_nonneg hL hs.le
  have h := external_le hS (law_exchangeable hb hbound hMb hLb₁ hμ P hex hs)
    (klDiv_ne_top hS hb hbound hMb hLb₁ hμ P hP hs hC₀ hinit) (by positivity)
    (fun j hj => marginalEntropy_le_sharp hS hb hbound hMb hLb₁ hμ P hP hs hC₀ hinit j hj) hm0 hm
  refine h.trans (le_of_eq ?_)
  ring

/-- **Lemma 4.6, second inequality.** For `0 < s ≤ T` and `0 < m < N`,
`X_m(s) ≤ (A₁² / s) m²/N²`, where `A₁ = √8 M √(C₀ D_T)`. -/
theorem external_le_horizon (hS : IsSmoothCoefficients a K La L₁ L₂ M) (hP : HasSecondMoment P)
    (hex : Exchangeable P) {C₀ s T : ℝ} (hC₀ : 0 ≤ C₀) (hs : 0 < s) (hsT : s ≤ T)
    (hinit : ∀ j, ∀ hj : j ≤ N, wassersteinSq (marginal hj P) (tensorLaw (μ 0) j) ≤
      ENNReal.ofReal (C₀ * (j : ℝ) ^ 2 / (N : ℝ) ^ 2)) (hm0 : 0 < m) (hm : m < N) :
    haveI := law_isProbabilityMeasure_of_pos hb hbound hMb hLb₁ hμ P hs
    (((N : ℝ) - m) / N) ^ 2 * ∫ x, ∑ i,
        ‖externalField hm (PrescribedReference.law hb hbound hMb hLb₁ hμ N P s) (μ s) K x i‖ ^ 2
        ∂marginal hm.le (PrescribedReference.law hb hbound hMb hLb₁ hμ N P s) ≤
      sourceA₁ C₀ T La L₁ M ^ 2 / s * (m : ℝ) ^ 2 / (N : ℝ) ^ 2 := by
  refine (external_le_sharp hb hbound hMb hLb₁ hμ P hS hP hex hC₀ hs hinit hm0 hm).trans ?_
  have hβ := bridgeCost_le_horizonFactor_div hS.assumptionA.La_nonneg hS.assumptionA.L₁_nonneg
    hs hsT
  have hβ' : RegularizationRates.bridgeCost (lipL La L₁) s ≤ horizonFactor T La L₁ / s := hβ
  have hD := horizonFactor_nonneg T La L₁
  have hA₁ : sourceA₁ C₀ T La L₁ M ^ 2 = 8 * M ^ 2 * C₀ * horizonFactor T La L₁ := by
    unfold sourceA₁
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (by positivity)]
    ring
  rw [hA₁]
  have : 0 ≤ 8 * M ^ 2 * C₀ := by positivity
  calc 8 * M ^ 2 * C₀ * RegularizationRates.bridgeCost (lipL La L₁) s * (m : ℝ) ^ 2 / (N : ℝ) ^ 2
      ≤ 8 * M ^ 2 * C₀ * (horizonFactor T La L₁ / s) * (m : ℝ) ^ 2 / (N : ℝ) ^ 2 := by gcongr
    _ = _ := by ring

end Reference

end SharpWasserstein.Sharp.Source
