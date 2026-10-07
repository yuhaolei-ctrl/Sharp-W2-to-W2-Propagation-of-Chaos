/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# The internal interaction sum: second moment and Lipschitz bound

This file contains the measure-theoretic and Lipschitz ingredients of Lemma 4.5 (`lem:internal`)
of *Sharp Wasserstein propagation of chaos from correlated initial data*. For a centred
interaction `c` (Section 3.3 of the paper, `c_s(x, y) = K(x, y) - ∫ K(x, y') μ_s(dy')`) and `m`
particles, the paper considers the internal interaction sum `Ξ(x)ᵢ = ∑ⱼ c(xᵢ, xⱼ)` and proves

* under the product law `μ^{⊗m}`, `E |Ξ(Y)ᵢ|² ≤ 4M² + (m - 1) M²`, hence
  `E |Ξ(Y)|² ≤ m (m + 3) M² ≤ 4 M² m²`;
* `|Ξ(x) - Ξ(y)| ≤ m L_c |x - y|` for the Euclidean norms on `(ℝᵈ)ᵐ`, where `L_c = 2L₁ + L₂`.

All results are stated for a general measurable space `α` (respectively a seminormed group `V`)
and a general real inner product space `H` (respectively a normed space `E`), and do not refer to
the particle system.

## Main definitions

* `SharpWasserstein.Sharp.centredKernel μ K`: the kernel `K` centred in its second variable
  with respect to `μ`, `c(x, y) = K(x, y) - ∫ K(x, y') dμ(y')`.

## Main statements

* `SharpWasserstein.Sharp.integral_pi_eq_integral_integral_insertNth`: Fubini's theorem
  integrating out a single coordinate of a product measure on `Fin (n + 1) → α`.
* `SharpWasserstein.Sharp.integral_inner_eq_zero_of_centred`: the cross terms
  `E ⟪c(Yᵢ, Yⱼ), c(Yᵢ, Yₖ)⟫` vanish for `j ≠ i, k`.
* `SharpWasserstein.Sharp.integral_norm_sq_sum_eq_of_centred`: the second moment of
  `∑ⱼ c(Yᵢ, Yⱼ)` is the sum of the second moments of its terms.
* `SharpWasserstein.Sharp.integral_norm_sq_sum_le_of_centred`: the bound `B² + (m - 1) V`.
* `SharpWasserstein.Sharp.sum_integral_norm_sq_sum_centredKernel_le` and
  `SharpWasserstein.Sharp.integral_sum_norm_sq_sum_centredKernel_le`: the bound `4 M² m²` for
  the centred kernel of a bounded measurable `K`.
* `SharpWasserstein.Sharp.sqrt_sum_norm_sq_sum_sub_le`: the Lipschitz bound for `Ξ`.
* `SharpWasserstein.Sharp.norm_centredKernel_sub_le`: centring a kernel that is `L₁`-Lipschitz in
  `x` and `L₂`-Lipschitz in `y` yields a kernel that is `2L₁`-Lipschitz in `x` and
  `L₂`-Lipschitz in `y`.
* `SharpWasserstein.Sharp.sqrt_sum_norm_sq_sum_centredKernel_sub_le`: the Lipschitz bound for
  `Ξ` built from a centred kernel, with constant `m (2L₁ + L₂)`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Finset
open scoped RealInnerProductSpace

namespace SharpWasserstein.Sharp

variable {α : Type*} [MeasurableSpace α]

/-! ### Integrating out one coordinate -/

/-- **Fubini's theorem in one coordinate.** For an integrable function `F` on
`Fin (n + 1) → α` with the product measure `μ^{⊗(n+1)}`, the integral of `F` is obtained by
first integrating out the coordinate `j` and then integrating over the remaining `n`
coordinates. -/
theorem integral_pi_eq_integral_integral_insertNth {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {n : ℕ} (μ : Measure α) [SigmaFinite μ] (j : Fin (n + 1))
    {F : (Fin (n + 1) → α) → E} (hF : Integrable F (Measure.pi fun _ => μ)) :
    ∫ y, F y ∂(Measure.pi fun _ => μ) =
      ∫ z, ∫ t, F (j.insertNth t z) ∂μ ∂(Measure.pi fun _ : Fin n => μ) := by
  have hmp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) j).symm
  rw [← hmp.integral_comp' F]
  have hint := (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hF
  rw [integral_prod_symm (fun p => F ((MeasurableEquiv.piFinSuccAbove (fun _ => α) j).symm p))
    hint]
  rfl

/-! ### Measurability and integrability of kernels -/

/-- The map `y ↦ c (y i) (y j)` is measurable when `c` is jointly measurable. -/
private lemma measurable_apply_apply {β : Type*} [MeasurableSpace β] {c : α → α → β}
    (hc : Measurable (Function.uncurry c)) {m : ℕ} (i j : Fin m) :
    Measurable fun y : Fin m → α => c (y i) (y j) :=
  hc.comp (f := fun y : Fin m → α => (y i, y j)) (by fun_prop)

/-- A section `K x` of a jointly measurable kernel bounded by `M` is integrable for a finite
measure. -/
theorem integrable_apply_of_norm_le {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [OpensMeasurableSpace E] [SecondCountableTopology E] {μ : Measure α} [IsFiniteMeasure μ]
    {K : α → α → E} (hK : Measurable (Function.uncurry K)) {M : ℝ} (hKM : ∀ x y, ‖K x y‖ ≤ M)
    (x : α) : Integrable (K x) μ :=
  Integrable.of_bound (hK.comp measurable_prodMk_left).aestronglyMeasurable M
    (ae_of_all _ (hKM x))

/-- The squared norms `‖∑ⱼ c (y i) (y j)‖²` of a bounded jointly measurable kernel are integrable
under a product of probability measures. -/
private lemma integrable_norm_sq_sum_apply {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] (μ : Measure α) [IsProbabilityMeasure μ]
    {c : α → α → E} (hc : Measurable (Function.uncurry c)) {B : ℝ} (hB : ∀ x y, ‖c x y‖ ≤ B)
    {m : ℕ} (i : Fin m) :
    Integrable (fun y : Fin m → α => ‖∑ j, c (y i) (y j)‖ ^ 2) (Measure.pi fun _ => μ) := by
  have hmeas : Measurable fun y : Fin m → α => ∑ j, c (y i) (y j) :=
    Finset.measurable_sum _ fun j _ => measurable_apply_apply hc i j
  refine Integrable.of_bound (hmeas.norm.pow_const 2).aestronglyMeasurable ((m * B) ^ 2)
    (ae_of_all _ fun y => ?_)
  rw [norm_pow, norm_norm]
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  calc ‖∑ j, c (y i) (y j)‖ ≤ ∑ j, ‖c (y i) (y j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin m, B := sum_le_sum fun j _ => hB _ _
    _ = m * B := by simp

/-! ### The second moment of a centred sum under a product measure -/

section SecondMoment

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [BorelSpace H] [SecondCountableTopology H]

/-- The inner products `⟪c (y i) (y j), c (y k) (y l)⟫` of a bounded jointly measurable kernel
are integrable under a product of probability measures. -/
private lemma integrable_inner_apply (μ : Measure α) [IsProbabilityMeasure μ] {c : α → α → H}
    (hc : Measurable (Function.uncurry c)) {B : ℝ} (hB : ∀ x y, ‖c x y‖ ≤ B) {m : ℕ}
    (i j k l : Fin m) :
    Integrable (fun y : Fin m → α => ⟪c (y i) (y j), c (y k) (y l)⟫)
      (Measure.pi fun _ => μ) := by
  refine Integrable.of_bound ((measurable_apply_apply hc i j).inner
    (measurable_apply_apply hc k l)).aestronglyMeasurable (B * B) (ae_of_all _ fun y => ?_)
  rw [Real.norm_eq_abs]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul (hB _ _) (hB _ _) (norm_nonneg _) ((norm_nonneg _).trans (hB (y i) (y j))))

/-- The squared norms `‖c (y i) (y j)‖²` of a bounded jointly measurable kernel are integrable
under a product of probability measures. -/
private lemma integrable_norm_sq_apply (μ : Measure α) [IsProbabilityMeasure μ]
    {c : α → α → H} (hc : Measurable (Function.uncurry c)) {B : ℝ} (hB : ∀ x y, ‖c x y‖ ≤ B)
    {m : ℕ} (i j : Fin m) :
    Integrable (fun y : Fin m → α => ‖c (y i) (y j)‖ ^ 2) (Measure.pi fun _ => μ) := by
  simpa only [real_inner_self_eq_norm_sq] using integrable_inner_apply μ hc hB i j i j

/-- **Vanishing of the cross terms.** Let `c` be a bounded jointly measurable kernel which is
centred in its second variable, `∫ c x y dμ(y) = 0`. If `j ≠ i` and `j ≠ k`, then under
`μ^{⊗m}` the cross term `⟪c(Yᵢ, Yⱼ), c(Yᵢ, Yₖ)⟫` has mean zero: integrating out `Yⱼ` first, the
second factor is fixed and the first one has mean zero. -/
theorem integral_inner_eq_zero_of_centred [CompleteSpace H] (μ : Measure α)
    [IsProbabilityMeasure μ] {c : α → α → H} (hc : Measurable (Function.uncurry c)) {B : ℝ}
    (hB : ∀ x y, ‖c x y‖ ≤ B) (hcen : ∀ x, ∫ y, c x y ∂μ = 0) {m : ℕ} {i j k : Fin m}
    (hji : j ≠ i) (hjk : j ≠ k) :
    ∫ y, ⟪c (y i) (y j), c (y i) (y k)⟫ ∂(Measure.pi fun _ : Fin m => μ) = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by have := i.pos; omega⟩
  rw [integral_pi_eq_integral_integral_insertNth μ j (integrable_inner_apply μ hc hB i j i k)]
  obtain ⟨i', rfl⟩ := Fin.exists_succAbove_eq hji.symm
  obtain ⟨k', rfl⟩ := Fin.exists_succAbove_eq hjk.symm
  have h : ∀ z : Fin n → α, ∫ t, ⟪c (z i') t, c (z i') (z k')⟫ ∂μ = 0 := by
    intro z
    calc ∫ t, ⟪c (z i') t, c (z i') (z k')⟫ ∂μ
        = ∫ t, ⟪c (z i') (z k'), c (z i') t⟫ ∂μ := by
          congr 1
          ext t
          exact real_inner_comm _ _
      _ = 0 := by rw [integral_inner (integrable_apply_of_norm_le hc hB _), hcen, inner_zero_right]
  simp [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_same, h]

/-- **Second moment of a centred sum.** Let `c` be a bounded jointly measurable kernel which is
centred in its second variable. Under `μ^{⊗m}`, the second moment of `∑ⱼ c(Yᵢ, Yⱼ)` is the sum of
the second moments of its terms: all cross terms vanish by
`integral_inner_eq_zero_of_centred`. -/
theorem integral_norm_sq_sum_eq_of_centred [CompleteSpace H] (μ : Measure α)
    [IsProbabilityMeasure μ] {c : α → α → H} (hc : Measurable (Function.uncurry c)) {B : ℝ}
    (hB : ∀ x y, ‖c x y‖ ≤ B) (hcen : ∀ x, ∫ y, c x y ∂μ = 0) {m : ℕ} (i : Fin m) :
    ∫ y, ‖∑ j, c (y i) (y j)‖ ^ 2 ∂(Measure.pi fun _ : Fin m => μ) =
      ∫ y, ‖c (y i) (y i)‖ ^ 2 ∂(Measure.pi fun _ : Fin m => μ) +
        ∑ j ∈ univ.erase i, ∫ y, ‖c (y i) (y j)‖ ^ 2 ∂(Measure.pi fun _ : Fin m => μ) := by
  have hexp : ∀ y : Fin m → α,
      ‖∑ j, c (y i) (y j)‖ ^ 2 = ∑ j, ∑ k, ⟪c (y i) (y j), c (y i) (y k)⟫ := by
    intro y
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    simp only [inner_sum]
  have hdiag : ∀ j, ∫ y, ∑ k, ⟪c (y i) (y j), c (y i) (y k)⟫ ∂(Measure.pi fun _ => μ) =
      ∫ y, ‖c (y i) (y j)‖ ^ 2 ∂(Measure.pi fun _ => μ) := by
    intro j
    rw [integral_finsetSum _ fun k _ => integrable_inner_apply μ hc hB i j i k,
      sum_eq_single j]
    · simp only [real_inner_self_eq_norm_sq]
    · intro k _ hkj
      by_cases hji : j = i
      · subst hji
        calc ∫ y, ⟪c (y j) (y j), c (y j) (y k)⟫ ∂(Measure.pi fun _ => μ)
            = ∫ y, ⟪c (y j) (y k), c (y j) (y j)⟫ ∂(Measure.pi fun _ => μ) := by
              congr 1
              ext y
              exact real_inner_comm _ _
          _ = 0 := integral_inner_eq_zero_of_centred μ hc hB hcen hkj hkj
      · exact integral_inner_eq_zero_of_centred μ hc hB hcen hji (Ne.symm hkj)
    · simp
  simp_rw [hexp]
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
      integrable_inner_apply μ hc hB i j i k, sum_congr rfl fun j _ => hdiag j,
    ← add_sum_erase _ _ (mem_univ i)]

/-- **Off-diagonal second moments.** If `j ≠ i` and `∫ ‖c x y‖² dμ(y) ≤ V` for every `x`, then
`E ‖c(Yᵢ, Yⱼ)‖² ≤ V` under `μ^{⊗m}`. -/
theorem integral_norm_sq_apply_le_of_ne (μ : Measure α) [IsProbabilityMeasure μ]
    {c : α → α → H} (hc : Measurable (Function.uncurry c)) {B V : ℝ} (hB : ∀ x y, ‖c x y‖ ≤ B)
    (hV : ∀ x, ∫ y, ‖c x y‖ ^ 2 ∂μ ≤ V) {m : ℕ} {i j : Fin m} (hji : j ≠ i) :
    ∫ y, ‖c (y i) (y j)‖ ^ 2 ∂(Measure.pi fun _ : Fin m => μ) ≤ V := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by have := i.pos; omega⟩
  rw [integral_pi_eq_integral_integral_insertNth μ j (integrable_norm_sq_apply μ hc hB i j)]
  obtain ⟨i', rfl⟩ := Fin.exists_succAbove_eq hji.symm
  simp only [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_same]
  calc ∫ z, ∫ t, ‖c (z i') t‖ ^ 2 ∂μ ∂(Measure.pi fun _ : Fin n => μ)
      ≤ ∫ _z, V ∂(Measure.pi fun _ : Fin n => μ) :=
        integral_mono_of_nonneg (ae_of_all _ fun _ => integral_nonneg fun _ => sq_nonneg _)
          (integrable_const V) (ae_of_all _ fun z => hV (z i'))
    _ = V := by simp

/-- **Second moment bound for a centred sum.** Let `c` be a jointly measurable kernel with
`‖c x y‖ ≤ B`, centred in its second variable, and with `∫ ‖c x y‖² dμ(y) ≤ V` for every `x`.
Then under `μ^{⊗m}`, `E ‖∑ⱼ c(Yᵢ, Yⱼ)‖² ≤ B² + (m - 1) V` (proof of Lemma 4.5, with `B = 2M`
and `V = M²`). -/
theorem integral_norm_sq_sum_le_of_centred [CompleteSpace H] (μ : Measure α)
    [IsProbabilityMeasure μ] {c : α → α → H} (hc : Measurable (Function.uncurry c)) {B V : ℝ}
    (hB : ∀ x y, ‖c x y‖ ≤ B) (hcen : ∀ x, ∫ y, c x y ∂μ = 0)
    (hV : ∀ x, ∫ y, ‖c x y‖ ^ 2 ∂μ ≤ V) {m : ℕ} (i : Fin m) :
    ∫ y, ‖∑ j, c (y i) (y j)‖ ^ 2 ∂(Measure.pi fun _ : Fin m => μ) ≤
      B ^ 2 + ((m : ℝ) - 1) * V := by
  rw [integral_norm_sq_sum_eq_of_centred μ hc hB hcen i]
  gcongr ?_ + ?_
  · calc ∫ y, ‖c (y i) (y i)‖ ^ 2 ∂(Measure.pi fun _ : Fin m => μ)
        ≤ ∫ _y, B ^ 2 ∂(Measure.pi fun _ : Fin m => μ) :=
          integral_mono_of_nonneg (ae_of_all _ fun _ => sq_nonneg _) (integrable_const _)
            (ae_of_all _ fun _ => pow_le_pow_left₀ (norm_nonneg _) (hB _ _) 2)
      _ = B ^ 2 := by simp
  · calc ∑ j ∈ univ.erase i, ∫ y, ‖c (y i) (y j)‖ ^ 2 ∂(Measure.pi fun _ : Fin m => μ)
        ≤ ∑ _j ∈ univ.erase i, V :=
          sum_le_sum fun j hj => integral_norm_sq_apply_le_of_ne μ hc hB hV (ne_of_mem_erase hj)
      _ = ((m : ℝ) - 1) * V := by
          rw [sum_const, card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin,
            nsmul_eq_mul, Nat.cast_pred i.pos]

end SecondMoment

/-! ### The centred kernel -/

section CentredKernel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The kernel `K` centred in its second variable with respect to `μ`:
`centredKernel μ K x y = K x y - ∫ K x y' dμ(y')`. With `μ = μ_s` this is the centred interaction
`c_s = K - K̄_s` of Section 3.3 of the paper. -/
def centredKernel (μ : Measure α) (K : α → α → E) (x y : α) : E :=
  K x y - ∫ y', K x y' ∂μ

/-- The centred kernel of a jointly measurable kernel is jointly measurable. -/
theorem measurable_centredKernel [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure α) [SFinite μ] {K : α → α → E} (hK : Measurable (Function.uncurry K)) :
    Measurable (Function.uncurry (centredKernel μ K)) := by
  have hmean : Measurable fun x => ∫ y, K x y ∂μ :=
    hK.stronglyMeasurable.integral_prod_right.measurable
  exact hK.sub (hmean.comp measurable_fst)

/-- If `‖K x y‖ ≤ M`, then the centred kernel satisfies `‖c x y‖ ≤ 2M`. -/
theorem norm_centredKernel_le (μ : Measure α) [IsProbabilityMeasure μ] {K : α → α → E} {M : ℝ}
    (hKM : ∀ x y, ‖K x y‖ ≤ M) (x y : α) : ‖centredKernel μ K x y‖ ≤ 2 * M := by
  have hmean : ‖∫ y', K x y' ∂μ‖ ≤ M := by
    simpa using norm_integral_le_of_norm_le_const (μ := μ) (ae_of_all _ (hKM x))
  calc ‖centredKernel μ K x y‖ ≤ ‖K x y‖ + ‖∫ y', K x y' ∂μ‖ := norm_sub_le _ _
    _ ≤ M + M := add_le_add (hKM x y) hmean
    _ = 2 * M := by ring

/-- The centred kernel has mean zero in its second variable. -/
theorem integral_centredKernel [CompleteSpace E] (μ : Measure α) [IsProbabilityMeasure μ]
    {K : α → α → E} {x : α} (hK : Integrable (K x) μ) : ∫ y, centredKernel μ K x y ∂μ = 0 := by
  simp only [centredKernel]
  rw [integral_sub hK (integrable_const _), integral_const, probReal_univ, one_smul, sub_self]

/-- **Variance is at most the second moment.** If `‖K x y‖ ≤ M` for all `y`, then
`∫ ‖c x y‖² dμ(y) ≤ M²`, where `c` is the centred kernel. -/
theorem integral_norm_sq_centredKernel_le {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (μ : Measure α) [IsProbabilityMeasure μ]
    {K : α → α → H} {M : ℝ} {x : α} (hK : Integrable (K x) μ) (hKM : ∀ y, ‖K x y‖ ≤ M) :
    ∫ y, ‖centredKernel μ K x y‖ ^ 2 ∂μ ≤ M ^ 2 := by
  set a := ∫ y', K x y' ∂μ with ha
  have hsq : Integrable (fun y => ‖K x y‖ ^ 2) μ :=
    Integrable.of_bound (hK.aestronglyMeasurable.norm.pow 2) (M ^ 2)
      (ae_of_all _ fun y => by
        simpa using pow_le_pow_left₀ (norm_nonneg _) (hKM y) 2)
  have hin : Integrable (fun y => ⟪K x y, a⟫) μ := hK.inner_const a
  have hdiff : Integrable (fun y => ‖K x y‖ ^ 2 - 2 * ⟪K x y, a⟫) μ := hsq.sub (hin.const_mul 2)
  have hmean : ∫ y, ⟪K x y, a⟫ ∂μ = ‖a‖ ^ 2 := by
    calc ∫ y, ⟪K x y, a⟫ ∂μ = ∫ y, ⟪a, K x y⟫ ∂μ := by
          congr 1
          ext y
          exact real_inner_comm _ _
      _ = ‖a‖ ^ 2 := by rw [integral_inner hK, ← ha, real_inner_self_eq_norm_sq]
  calc ∫ y, ‖centredKernel μ K x y‖ ^ 2 ∂μ
      = ∫ y, (‖K x y‖ ^ 2 - 2 * ⟪K x y, a⟫ + ‖a‖ ^ 2) ∂μ := by
        simp only [centredKernel, ← ha, norm_sub_sq_real]
    _ = ∫ y, ‖K x y‖ ^ 2 ∂μ - 2 * ‖a‖ ^ 2 + ‖a‖ ^ 2 := by
        rw [integral_add hdiff (integrable_const _),
          integral_sub hsq (hin.const_mul 2), integral_const_mul, hmean]
        simp
    _ ≤ ∫ y, ‖K x y‖ ^ 2 ∂μ := by nlinarith [sq_nonneg ‖a‖]
    _ ≤ ∫ _y, M ^ 2 ∂μ :=
        integral_mono hsq (integrable_const _) fun y => pow_le_pow_left₀ (norm_nonneg _) (hKM y) 2
    _ = M ^ 2 := by simp

/-- **Second moment of the internal interaction sum** (first half of the proof of Lemma 4.5).
Let `K` be a jointly measurable kernel with `‖K x y‖ ≤ M` and let `c` be its centred kernel with
respect to the probability measure `μ`. Then under `μ^{⊗m}`,
`∑ᵢ E ‖∑ⱼ c(Yᵢ, Yⱼ)‖² ≤ m (m + 3) M² ≤ 4 M² m²`. -/
theorem sum_integral_norm_sq_sum_centredKernel_le {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]
    [SecondCountableTopology H] (μ : Measure α) [IsProbabilityMeasure μ] {K : α → α → H}
    (hK : Measurable (Function.uncurry K)) {M : ℝ} (hKM : ∀ x y, ‖K x y‖ ≤ M) (m : ℕ) :
    ∑ i : Fin m, ∫ y, ‖∑ j, centredKernel μ K (y i) (y j)‖ ^ 2 ∂(Measure.pi fun _ => μ) ≤
      4 * M ^ 2 * m ^ 2 := by
  have hKi : ∀ x, Integrable (K x) μ := integrable_apply_of_norm_le hK hKM
  have hterm : ∀ i : Fin m,
      ∫ y, ‖∑ j, centredKernel μ K (y i) (y j)‖ ^ 2 ∂(Measure.pi fun _ => μ) ≤
        (2 * M) ^ 2 + ((m : ℝ) - 1) * M ^ 2 := fun i =>
    integral_norm_sq_sum_le_of_centred μ (measurable_centredKernel μ hK)
      (norm_centredKernel_le μ hKM) (fun x => integral_centredKernel μ (hKi x))
      (fun x => integral_norm_sq_centredKernel_le μ (hKi x) (hKM x)) i
  calc ∑ i : Fin m, ∫ y, ‖∑ j, centredKernel μ K (y i) (y j)‖ ^ 2 ∂(Measure.pi fun _ => μ)
      ≤ ∑ _i : Fin m, ((2 * M) ^ 2 + ((m : ℝ) - 1) * M ^ 2) := sum_le_sum fun i _ => hterm i
    _ = m * (m + 3) * M ^ 2 := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
    _ ≤ 4 * M ^ 2 * m ^ 2 := by
        rcases Nat.eq_zero_or_pos m with rfl | hm
        · simp
        · have h1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
          have h2 : 0 ≤ M ^ 2 * m * (m - 1) :=
            mul_nonneg (mul_nonneg (sq_nonneg M) (by positivity)) (sub_nonneg.2 h1)
          nlinarith [h2]

/-- **Second moment of the internal interaction sum**, in the form `E |Ξ(Y)|² ≤ 4 M² m²` used in
the proof of Lemma 4.5: the squared `ℓ²` norm of `Ξ(Y)ᵢ = ∑ⱼ c(Yᵢ, Yⱼ)` is summed inside the
integral. See `sum_integral_norm_sq_sum_centredKernel_le`. -/
theorem integral_sum_norm_sq_sum_centredKernel_le {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]
    [SecondCountableTopology H] (μ : Measure α) [IsProbabilityMeasure μ] {K : α → α → H}
    (hK : Measurable (Function.uncurry K)) {M : ℝ} (hKM : ∀ x y, ‖K x y‖ ≤ M) (m : ℕ) :
    ∫ y, ∑ i : Fin m, ‖∑ j, centredKernel μ K (y i) (y j)‖ ^ 2 ∂(Measure.pi fun _ => μ) ≤
      4 * M ^ 2 * m ^ 2 := by
  rw [integral_finsetSum _ fun i _ => integrable_norm_sq_sum_apply μ
    (measurable_centredKernel μ hK) (norm_centredKernel_le μ hKM) i]
  exact sum_integral_norm_sq_sum_centredKernel_le μ hK hKM m

end CentredKernel

/-! ### The Lipschitz bound -/

section Lipschitz

variable {V E : Type*} [SeminormedAddCommGroup V]

/-- **Lipschitz bound for the internal interaction sum** (second half of the proof of
Lemma 4.5). If `‖c x y - c x' y'‖ ≤ ℓ₁ ‖x - x'‖ + ℓ₂ ‖y - y'‖`, then the map
`Ξ(x)ᵢ = ∑ⱼ c(xᵢ, xⱼ)` on `Fin m → V` is `m (ℓ₁ + ℓ₂)`-Lipschitz for the `ℓ²` norms.
The proof bounds `‖Ξ(x)ᵢ - Ξ(y)ᵢ‖ ≤ m ℓ₁ ‖uᵢ‖ + ℓ₂ ∑ⱼ ‖uⱼ‖` with `u = x - y` and uses
`(∑ⱼ ‖uⱼ‖)² ≤ m ∑ⱼ ‖uⱼ‖²`. -/
theorem sqrt_sum_norm_sq_sum_sub_le [SeminormedAddCommGroup E] {c : V → V → E} {ℓ₁ ℓ₂ : ℝ}
    (hℓ₁ : 0 ≤ ℓ₁) (hℓ₂ : 0 ≤ ℓ₂)
    (hc : ∀ x x' y y', ‖c x y - c x' y'‖ ≤ ℓ₁ * ‖x - x'‖ + ℓ₂ * ‖y - y'‖) {m : ℕ}
    (x y : Fin m → V) :
    √(∑ i, ‖∑ j, c (x i) (x j) - ∑ j, c (y i) (y j)‖ ^ 2) ≤
      m * (ℓ₁ + ℓ₂) * √(∑ i, ‖x i - y i‖ ^ 2) := by
  set u : Fin m → ℝ := fun i => ‖x i - y i‖ with hu
  set S := ∑ j, u j with hS
  set U := ∑ i, u i ^ 2 with hU
  have hpt : ∀ i, ‖∑ j, c (x i) (x j) - ∑ j, c (y i) (y j)‖ ≤ m * ℓ₁ * u i + ℓ₂ * S := by
    intro i
    rw [← sum_sub_distrib]
    calc ‖∑ j, (c (x i) (x j) - c (y i) (y j))‖
        ≤ ∑ j, ‖c (x i) (x j) - c (y i) (y j)‖ := norm_sum_le _ _
      _ ≤ ∑ j, (ℓ₁ * u i + ℓ₂ * u j) := sum_le_sum fun j _ => hc _ _ _ _
      _ = m * ℓ₁ * u i + ℓ₂ * S := by
          rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_sum]
          ring
  have hCS : S ^ 2 ≤ m * U := by
    simpa using sq_sum_le_card_mul_sum_sq (s := univ) (f := u)
  have hexp : ∑ i, (m * ℓ₁ * u i + ℓ₂ * S) ^ 2 =
      m ^ 2 * ℓ₁ ^ 2 * U + 2 * m * ℓ₁ * ℓ₂ * S ^ 2 + m * ℓ₂ ^ 2 * S ^ 2 := by
    have h : ∀ i, (m * ℓ₁ * u i + ℓ₂ * S) ^ 2 =
        m ^ 2 * ℓ₁ ^ 2 * u i ^ 2 + 2 * m * ℓ₁ * ℓ₂ * S * u i + ℓ₂ ^ 2 * S ^ 2 := fun i => by
      ring
    rw [sum_congr rfl fun i _ => h i, sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum,
      ← hS, ← hU, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hsq : ∑ i, ‖∑ j, c (x i) (x j) - ∑ j, c (y i) (y j)‖ ^ 2 ≤ (m * (ℓ₁ + ℓ₂)) ^ 2 * U := by
    have h1 := mul_le_mul_of_nonneg_left hCS
      (by positivity : (0 : ℝ) ≤ 2 * m * ℓ₁ * ℓ₂)
    have h2 := mul_le_mul_of_nonneg_left hCS (by positivity : (0 : ℝ) ≤ m * ℓ₂ ^ 2)
    calc ∑ i, ‖∑ j, c (x i) (x j) - ∑ j, c (y i) (y j)‖ ^ 2
        ≤ ∑ i, (m * ℓ₁ * u i + ℓ₂ * S) ^ 2 :=
          sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hpt i) 2
      _ = m ^ 2 * ℓ₁ ^ 2 * U + 2 * m * ℓ₁ * ℓ₂ * S ^ 2 + m * ℓ₂ ^ 2 * S ^ 2 := hexp
      _ ≤ (m * (ℓ₁ + ℓ₂)) ^ 2 * U := by nlinarith [h1, h2]
  calc √(∑ i, ‖∑ j, c (x i) (x j) - ∑ j, c (y i) (y j)‖ ^ 2)
      ≤ √((m * (ℓ₁ + ℓ₂)) ^ 2 * U) := Real.sqrt_le_sqrt hsq
    _ = m * (ℓ₁ + ℓ₂) * √U := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace V]

/-- **Lipschitz bound for the centred kernel.** If `K` is `L₁`-Lipschitz in `x` and `L₂`-Lipschitz
in `y`, in the sense `‖K x y - K x' y'‖ ≤ L₁ ‖x - x'‖ + L₂ ‖y - y'‖`, and its sections are
integrable, then the centred kernel satisfies the same bound with `L₁` replaced by `2L₁`, since
`x ↦ ∫ K x y dμ(y)` is `L₁`-Lipschitz (Section 3.3 of the paper). -/
theorem norm_centredKernel_sub_le (μ : Measure V) [IsProbabilityMeasure μ] {K : V → V → E}
    (hK : ∀ x, Integrable (K x) μ) {L₁ L₂ : ℝ}
    (hKL : ∀ x x' y y', ‖K x y - K x' y'‖ ≤ L₁ * ‖x - x'‖ + L₂ * ‖y - y'‖) (x x' y y' : V) :
    ‖centredKernel μ K x y - centredKernel μ K x' y'‖ ≤ 2 * L₁ * ‖x - x'‖ + L₂ * ‖y - y'‖ := by
  have hmean : ‖∫ t, K x t ∂μ - ∫ t, K x' t ∂μ‖ ≤ L₁ * ‖x - x'‖ := by
    rw [← integral_sub (hK x) (hK x')]
    simpa using norm_integral_le_of_norm_le_const (μ := μ) (C := L₁ * ‖x - x'‖)
      (ae_of_all _ fun t => by simpa using hKL x x' t t)
  have hsplit : centredKernel μ K x y - centredKernel μ K x' y' =
      (K x y - K x' y') - (∫ t, K x t ∂μ - ∫ t, K x' t ∂μ) := by
    simp only [centredKernel]
    abel
  rw [hsplit]
  calc ‖(K x y - K x' y') - (∫ t, K x t ∂μ - ∫ t, K x' t ∂μ)‖
      ≤ ‖K x y - K x' y'‖ + ‖∫ t, K x t ∂μ - ∫ t, K x' t ∂μ‖ := norm_sub_le _ _
    _ ≤ (L₁ * ‖x - x'‖ + L₂ * ‖y - y'‖) + L₁ * ‖x - x'‖ := add_le_add (hKL _ _ _ _) hmean
    _ = 2 * L₁ * ‖x - x'‖ + L₂ * ‖y - y'‖ := by ring

/-- **Lipschitz bound for `Ξ` built from a centred kernel** (Lemma 4.5). If `K` satisfies
`‖K x y - K x' y'‖ ≤ L₁ ‖x - x'‖ + L₂ ‖y - y'‖` with `L₁, L₂ ≥ 0` and has integrable sections,
then `Ξ(x)ᵢ = ∑ⱼ c(xᵢ, xⱼ)`, with `c` the centred kernel, satisfies
`|Ξ(x) - Ξ(y)| ≤ m L_c |x - y|` with `L_c = 2L₁ + L₂`. -/
theorem sqrt_sum_norm_sq_sum_centredKernel_sub_le (μ : Measure V) [IsProbabilityMeasure μ]
    {K : V → V → E} (hK : ∀ x, Integrable (K x) μ) {L₁ L₂ : ℝ} (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hKL : ∀ x x' y y', ‖K x y - K x' y'‖ ≤ L₁ * ‖x - x'‖ + L₂ * ‖y - y'‖) {m : ℕ}
    (x y : Fin m → V) :
    √(∑ i, ‖∑ j, centredKernel μ K (x i) (x j) - ∑ j, centredKernel μ K (y i) (y j)‖ ^ 2) ≤
      m * (2 * L₁ + L₂) * √(∑ i, ‖x i - y i‖ ^ 2) :=
  sqrt_sum_norm_sq_sum_sub_le (by positivity) hL₂ (norm_centredKernel_sub_le μ hK hKL) x y

end Lipschitz

end SharpWasserstein.Sharp
