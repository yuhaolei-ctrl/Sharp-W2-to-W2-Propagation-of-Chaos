/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import SharpWasserstein.Sharp.Source.ReferenceTransport
public import SharpWasserstein.Sharp.Source.Minkowski
public import SharpWasserstein.Sharp.InternalMoment
public import SharpWasserstein.TransportTriangle
public import SharpWasserstein.TransportMoments

/-!
# The internal part of the source (Lemma 4.5)

Let `c_s(x, y) = K(x, y) - ∫ K(x, y') μ_s(dy')` be the centred interaction of Section 3.3 and,
for `x ∈ (ℝᵈ)^m`, let `Ξ_s(x)ᵢ = ∑ⱼ c_s(xᵢ, xⱼ)` be the internal interaction sum. Lemma 4.5
(`lem:internal`) of the paper states that `I_m(s) = N⁻² ∫ |Ξ_s|² dR^{(m)}_s` satisfies
`√I_m(s) ≤ A₀ m/N` for `1 ≤ m ≤ N` and `0 ≤ s ≤ T`, where `A₀ = 2M + L_c e^{LT} √C₀`.

The proof has three ingredients.
* Under `μ_s^{⊗m}` the second moment satisfies `∫ |Ξ_s|² ≤ 4M²m²`
  (`integral_sum_norm_sq_sum_centredKernel_le`).
* `Ξ_s` is `m L_c`-Lipschitz for the unnormalized Euclidean norm on `(ℝᵈ)^m`, `L_c = 2L₁ + L₂`
  (`sqrt_sum_norm_sq_sum_sub_le`).
* For every coupling of `R^{(m)}_s` and `μ_s^{⊗m}`, Minkowski's inequality in `L²` gives
  `√(∫ |Ξ_s|² dR^{(m)}_s) ≤ 2Mm + m L_c (cost)^{1/2}`; taking the infimum over couplings
  (no optimal coupling is needed) and using Lemma 3.5 gives the claim.

All norms are Euclidean: the interaction enters through `y ↦ toLp (K x y)`, whose bounds are
exactly those of Assumption A.

## Main definitions

* `internalField q K x i = ∑ⱼ c(xᵢ, xⱼ)`, with `c` the centred Euclidean interaction.

## Main statements

* `ofReal_sqrt_integral_internalField_le`: the coupling estimate, for an arbitrary law `ρ`.
* `sqrt_integral_internalField_le`: the same under a Wasserstein bound `W²(ρ, q^{⊗m}) ≤ B`.
* `sqrt_internal_le`: **Lemma 4.5**, `√I_m(s) ≤ A₀ m/N`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SharpWasserstein.Sharp.Source

variable {d m : ℕ} {a : Position d → Position d} {K : Position d → Position d → Position d}
  {La L₁ L₂ M : ℝ}

/-- The centred Euclidean interaction `c(x, y) = K(x, y) - ∫ K(x, y') q(dy')`. With `q = μ_s`
this is the centred interaction `c_s` of Section 3.3. -/
abbrev centred (q : Measure (Position d)) (K : Position d → Position d → Position d) :
    Position d → Position d → EuclideanSpace ℝ (Fin d) :=
  centredKernel q fun u v => WithLp.toLp 2 (K u v)

/-- The internal interaction sum `Ξ(x)ᵢ = ∑ⱼ c(xᵢ, xⱼ)` of Lemma 4.5, diagonal term included. -/
def internalField (q : Measure (Position d)) (K : Position d → Position d → Position d)
    (x : Configuration d m) (i : Fin m) : EuclideanSpace ℝ (Fin d) :=
  ∑ j, centred q K (x i) (x j)

/-- The centred interaction is jointly measurable. -/
theorem measurable_centred (hS : IsSmoothCoefficients a K La L₁ L₂ M) (q : Measure (Position d))
    [IsProbabilityMeasure q] : Measurable (Function.uncurry (centred q K)) :=
  measurable_centredKernel q (IsSmoothCoefficients.measurable_toLp_K hS)

/-- Each component of the internal interaction sum is measurable. -/
theorem measurable_internalField (hS : IsSmoothCoefficients a K La L₁ L₂ M)
    (q : Measure (Position d)) [IsProbabilityMeasure q] (i : Fin m) :
    Measurable fun x : Configuration d m => internalField q K x i := by
  unfold internalField
  refine Finset.measurable_sum _ fun j _ => ?_
  have h := (measurable_centred hS q).comp ((measurable_pi_apply (X := fun _ : Fin m =>
    Position d) i).prodMk (measurable_pi_apply j))
  exact h

/-- `|Ξ(x)ᵢ| ≤ 2Mm`. -/
theorem norm_internalField_le (hS : IsSmoothCoefficients a K La L₁ L₂ M)
    (q : Measure (Position d)) [IsProbabilityMeasure q] (x : Configuration d m) (i : Fin m) :
    ‖internalField q K x i‖ ≤ m * (2 * M) := by
  unfold internalField
  refine (norm_sum_le _ _).trans ?_
  have h := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) =>
    norm_centredKernel_le q (IsSmoothCoefficients.norm_toLp_K_le hS) (x i) (x j)
  simpa using h

/-- **Second moment** (first half of the proof of Lemma 4.5): under `q^{⊗m}`,
`∫ ∑ᵢ |Ξ(y)ᵢ|² ≤ 4M²m²`. -/
theorem integral_internalField_tensor_le (hS : IsSmoothCoefficients a K La L₁ L₂ M)
    (q : Measure (Position d)) [IsProbabilityMeasure q] :
    ∫ y, ∑ i, ‖internalField q K y i‖ ^ 2 ∂tensorLaw q m ≤ 4 * M ^ 2 * m ^ 2 :=
  integral_sum_norm_sq_sum_centredKernel_le q (IsSmoothCoefficients.measurable_toLp_K hS)
    (IsSmoothCoefficients.norm_toLp_K_le hS) m

/-- The centred interaction is `2L₁`-Lipschitz in `x` and `L₂`-Lipschitz in `y`, for the
Euclidean norm (Section 3.3). -/
theorem norm_centred_sub_le (hS : IsSmoothCoefficients a K La L₁ L₂ M) (q : Measure (Position d))
    [IsProbabilityMeasure q] (x x' y y' : Position d) :
    ‖centred q K x y - centred q K x' y'‖ ≤
      2 * L₁ * ‖WithLp.toLp 2 x - WithLp.toLp 2 x'‖ +
        L₂ * ‖WithLp.toLp 2 y - WithLp.toLp 2 y'‖ := by
  have hmean : ‖∫ t, WithLp.toLp 2 (K x t) ∂q - ∫ t, WithLp.toLp 2 (K x' t) ∂q‖ ≤
      L₁ * ‖WithLp.toLp 2 x - WithLp.toLp 2 x'‖ := by
    rw [← integral_sub (IsSmoothCoefficients.integrable_toLp_K hS q x)
      (IsSmoothCoefficients.integrable_toLp_K hS q x')]
    simpa using norm_integral_le_of_norm_le_const (μ := q)
      (C := L₁ * ‖WithLp.toLp 2 x - WithLp.toLp 2 x'‖)
      (ae_of_all _ fun t => by simpa using IsSmoothCoefficients.norm_toLp_K_sub_le hS x x' t t)
  have hsplit : centred q K x y - centred q K x' y' =
      (WithLp.toLp 2 (K x y) - WithLp.toLp 2 (K x' y')) -
        (∫ t, WithLp.toLp 2 (K x t) ∂q - ∫ t, WithLp.toLp 2 (K x' t) ∂q) := by
    simp only [centred, centredKernel]
    abel
  rw [hsplit]
  calc _ ≤ ‖WithLp.toLp 2 (K x y) - WithLp.toLp 2 (K x' y')‖ +
        ‖∫ t, WithLp.toLp 2 (K x t) ∂q - ∫ t, WithLp.toLp 2 (K x' t) ∂q‖ := norm_sub_le _ _
    _ ≤ (L₁ * ‖WithLp.toLp 2 x - WithLp.toLp 2 x'‖ + L₂ * ‖WithLp.toLp 2 y - WithLp.toLp 2 y'‖) +
        L₁ * ‖WithLp.toLp 2 x - WithLp.toLp 2 x'‖ :=
      add_le_add (IsSmoothCoefficients.norm_toLp_K_sub_le hS x x' y y') hmean
    _ = _ := by ring

/-- **Lipschitz bound** (second half of the proof of Lemma 4.5): `Ξ` is `m L_c`-Lipschitz for the
unnormalized Euclidean norm on `(ℝᵈ)^m`, where `L_c = 2L₁ + L₂` and the squared distance is
`productCost`. -/
theorem sqrt_sum_norm_internalField_sub_le (hS : IsSmoothCoefficients a K La L₁ L₂ M)
    (q : Measure (Position d)) [IsProbabilityMeasure q] (x y : Configuration d m) :
    √(∑ i, ‖internalField q K x i - internalField q K y i‖ ^ 2) ≤
      m * lipC L₁ L₂ * √(productCost x y) := by
  have hA := hS.assumptionA
  have hc : ∀ u u' v v' : EuclideanSpace ℝ (Fin d),
      ‖centred q K (WithLp.ofLp u) (WithLp.ofLp v) - centred q K (WithLp.ofLp u') (WithLp.ofLp v')‖
        ≤ 2 * L₁ * ‖u - u'‖ + L₂ * ‖v - v'‖ := fun u u' v v' => by
    simpa using norm_centred_sub_le hS q (WithLp.ofLp u) (WithLp.ofLp u') (WithLp.ofLp v)
      (WithLp.ofLp v')
  have h := sqrt_sum_norm_sq_sum_sub_le (V := EuclideanSpace ℝ (Fin d))
    (c := fun u v => centred q K (WithLp.ofLp u) (WithLp.ofLp v))
    (mul_nonneg zero_le_two hA.L₁_nonneg) hA.L₂_nonneg hc
    (fun i => WithLp.toLp 2 (x i)) (fun i => WithLp.toLp 2 (y i))
  have hcost : ∑ i, ‖WithLp.toLp 2 (x i) - WithLp.toLp 2 (y i)‖ ^ 2 = productCost x y := by
    rw [productCost_eq_sum_positionSq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [positionSq_eq_norm_toLp_sq, WithLp.toLp_sub]
  rw [hcost] at h
  simpa [internalField, lipC] using h

/-- The internal interaction sum as a single vector of `ℓ²((ℝᵈ)^m)`. -/
abbrev internalVector (q : Measure (Position d)) (K : Position d → Position d → Position d)
    (x : Configuration d m) : PiLp 2 (fun _ : Fin m => EuclideanSpace ℝ (Fin d)) :=
  WithLp.toLp 2 (internalField q K x)

/-- The second moment bound in `L²` form: `‖Ξ‖_{L²(q^{⊗m})} ≤ 2Mm`. -/
theorem eLpNorm_internalVector_tensor_le (hS : IsSmoothCoefficients a K La L₁ L₂ M)
    (q : Measure (Position d)) [IsProbabilityMeasure q] :
    eLpNorm (internalVector q K) 2 (tensorLaw q m) ≤ ENNReal.ofReal (2 * M * m) := by
  have hA := hS.assumptionA
  rw [eLpNorm_toLp_eq (measurable_internalField hS q) (norm_internalField_le hS q)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Real.sqrt_le_left (by have := hA.M_nonneg; positivity)]
  calc _ ≤ 4 * M ^ 2 * m ^ 2 := integral_internalField_tensor_le hS q
    _ = _ := by ring

/-- The internal interaction vector is measurable. -/
theorem measurable_internalVector (hS : IsSmoothCoefficients a K La L₁ L₂ M)
    (q : Measure (Position d)) [IsProbabilityMeasure q] :
    Measurable (internalVector q K (m := m)) :=
  (PiLp.continuous_toLp 2 _).measurable.comp (Measurable.of_eval (measurable_internalField hS q))

/-- The Lipschitz bound in `L²(γ)`: `‖Ξ(x) - Ξ(y)‖_{L²(γ)} ≤ m L_c (∫ |x - y|² dγ)^{1/2}`. -/
theorem eLpNorm_internalVector_sub_le (hS : IsSmoothCoefficients a K La L₁ L₂ M)
    (q : Measure (Position d)) [IsProbabilityMeasure q]
    (γ : Measure (Configuration d m × Configuration d m)) :
    eLpNorm (fun z => internalVector q K z.1 - internalVector q K z.2) 2 γ ≤
      ENNReal.ofReal (m * lipC L₁ L₂) * transportCost γ ^ (1 / 2 : ℝ) := by
  have hA := hS.assumptionA
  have hF := measurable_internalVector (m := m) hS q
  rw [transportCost_root_eq_eLpNorm]
  have hc : 0 ≤ (m : ℝ) * lipC L₁ L₂ := by
    have := lipC_nonneg hA.L₁_nonneg hA.L₂_nonneg
    positivity
  have hpt : ∀ z : Configuration d m × Configuration d m,
      ‖internalVector q K z.1 - internalVector q K z.2‖ ≤
        ‖((m : ℝ) * lipC L₁ L₂) • transportDisplacement z‖ := fun z => by
    rw [norm_smul, Real.norm_of_nonneg hc, ← WithLp.toLp_sub, PiLp.norm_eq_of_L2,
      ← Real.sqrt_sq (norm_nonneg (transportDisplacement z)),
      ← productCost_eq_displacement_norm_sq]
    exact sqrt_sum_norm_internalField_sub_le hS q z.1 z.2
  calc _ ≤ eLpNorm (fun z => ((m : ℝ) * lipC L₁ L₂) • transportDisplacement z) 2 γ :=
        eLpNorm_mono ((hF.comp measurable_fst).sub
          (hF.comp measurable_snd)).aestronglyMeasurable hpt
    _ = _ := by
        rw [show (fun z => ((m : ℝ) * lipC L₁ L₂) • transportDisplacement z) =
          ((m : ℝ) * lipC L₁ L₂) • transportDisplacement from rfl, eLpNorm_const_smul,
          Real.enorm_of_nonneg hc]

/-- **Minkowski's inequality along one coupling** (proof of Lemma 4.5): for every coupling `γ` of
`ρ` and `q^{⊗m}`, `‖Ξ‖_{L²(ρ)} ≤ 2Mm + m L_c (∫ |x - y|² dγ)^{1/2}`. -/
theorem eLpNorm_internalVector_le_of_coupling (hS : IsSmoothCoefficients a K La L₁ L₂ M)
    (q : Measure (Position d)) [IsProbabilityMeasure q] {ρ : Measure (Configuration d m)}
    {γ : Measure (Configuration d m × Configuration d m)} (hγ : IsCoupling ρ (tensorLaw q m) γ) :
    eLpNorm (internalVector q K) 2 ρ ≤ ENNReal.ofReal (2 * M * m) +
      ENNReal.ofReal (m * lipC L₁ L₂) * transportCost γ ^ (1 / 2 : ℝ) := by
  have hF := measurable_internalVector (m := m) hS q
  obtain ⟨hγp, hγ₁, hγ₂⟩ := hγ
  have hfst : eLpNorm (internalVector q K) 2 ρ =
      eLpNorm (fun z => internalVector q K z.1) 2 γ := by
    rw [← hγ₁, eLpNorm_map_measure hF.aestronglyMeasurable measurable_fst.aemeasurable]
    rfl
  have hsnd : eLpNorm (fun z => internalVector q K z.2) 2 γ =
      eLpNorm (internalVector q K) 2 (tensorLaw q m) := by
    rw [← hγ₂, eLpNorm_map_measure hF.aestronglyMeasurable measurable_snd.aemeasurable]
    rfl
  have hsplit : (fun z : Configuration d m × Configuration d m => internalVector q K z.1) =
      (fun z => internalVector q K z.2) +
        fun z => internalVector q K z.1 - internalVector q K z.2 := by
    funext z
    exact (add_sub_cancel _ _).symm
  rw [hfst, hsplit]
  refine (eLpNorm_add_le one_le_two).trans ?_
  rw [hsnd]
  exact add_le_add (eLpNorm_internalVector_tensor_le hS q) (eLpNorm_internalVector_sub_le hS q γ)

/-- **The coupling estimate of Lemma 4.5.** For every probability law `ρ` on `(ℝᵈ)^m`,
`√(∫ ∑ᵢ |Ξ(x)ᵢ|² dρ) ≤ 2Mm + m L_c W(ρ, q^{⊗m})`, in `ℝ≥0∞`. The infimum over couplings is
taken directly; no optimal coupling is needed. -/
theorem ofReal_sqrt_integral_internalField_le (hS : IsSmoothCoefficients a K La L₁ L₂ M)
    (q : Measure (Position d)) [IsProbabilityMeasure q] (ρ : Measure (Configuration d m))
    [IsProbabilityMeasure ρ] :
    ENNReal.ofReal (√(∫ x, ∑ i, ‖internalField q K x i‖ ^ 2 ∂ρ)) ≤
      ENNReal.ofReal (2 * M * m) +
        ENNReal.ofReal (m * lipC L₁ L₂) * wassersteinSq ρ (tensorLaw q m) ^ (1 / 2 : ℝ) := by
  rw [← eLpNorm_toLp_eq (measurable_internalField hS q) (norm_internalField_le hS q)]
  have : Nonempty {γ // IsCoupling ρ (tensorLaw q m) γ} :=
    ⟨⟨ρ.prod (tensorLaw q m), product_isCoupling _ _⟩⟩
  rw [wassersteinSq_eq_iInf_coupling, ennreal_rpow_iInf _ (by norm_num),
    ENNReal.mul_iInf fun h => absurd h ENNReal.ofReal_ne_top, ENNReal.add_iInf]
  exact le_iInf fun γ => eLpNorm_internalVector_le_of_coupling hS q γ.2

/-- **The coupling estimate of Lemma 4.5, real form.** If `W²(ρ, q^{⊗m}) ≤ B`, then
`√(∫ ∑ᵢ |Ξ(x)ᵢ|² dρ) ≤ 2Mm + m L_c √B`. -/
theorem sqrt_integral_internalField_le (hS : IsSmoothCoefficients a K La L₁ L₂ M)
    (q : Measure (Position d)) [IsProbabilityMeasure q] (ρ : Measure (Configuration d m))
    [IsProbabilityMeasure ρ] {B : ℝ} (hB : wassersteinSq ρ (tensorLaw q m) ≤ ENNReal.ofReal B) :
    √(∫ x, ∑ i, ‖internalField q K x i‖ ^ 2 ∂ρ) ≤ 2 * M * m + m * lipC L₁ L₂ * √B := by
  have hA := hS.assumptionA
  have hc : 0 ≤ (m : ℝ) * lipC L₁ L₂ := by
    have := lipC_nonneg hA.L₁_nonneg hA.L₂_nonneg
    positivity
  have h := ofReal_sqrt_integral_internalField_le hS q ρ
  have hW : wassersteinSq ρ (tensorLaw q m) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (√B) := by
    calc _ ≤ ENNReal.ofReal B ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hB (by norm_num)
      _ = _ := by
        rcases le_total B 0 with hB0 | hB0
        · rw [ENNReal.ofReal_of_nonpos hB0, Real.sqrt_eq_zero'.2 hB0, ENNReal.ofReal_zero,
            ENNReal.zero_rpow_of_pos (by norm_num)]
        · rw [Real.sqrt_eq_rpow, ENNReal.ofReal_rpow_of_nonneg hB0 (by norm_num)]
  have h2 := h.trans (add_le_add le_rfl (mul_le_mul_right hW _))
  rw [← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_add (by have := hA.M_nonneg; positivity)
    (by positivity)] at h2
  exact (ENNReal.ofReal_le_ofReal_iff (by have := hA.M_nonneg; positivity)).1 h2

section Reference

variable {Mb Lb₁ Lb₂ : ℝ}
  (hb : BoundedSmoothKernel (kernelOf a K)) (hbound : KernelBounds (kernelOf a K) Mb Lb₁ Lb₂)
  (hMb : 0 ≤ Mb) (hLb₁ : 0 ≤ Lb₁)
  {μ : ℝ → Measure (Position d)} (hμ : IsLimitEvolution (kernelOf a K) μ)
  {N : ℕ} (P : Measure (Configuration d N)) [IsProbabilityMeasure P]

/-- The reference evolution `R^N_s` is a probability law for `s ≥ 0`. -/
theorem law_isProbabilityMeasure (hP : HasSecondMoment P) {s : ℝ} (hs : 0 ≤ s) :
    IsProbabilityMeasure (PrescribedReference.law hb hbound hMb hLb₁ hμ N P s) :=
  (PrescribedReference.law_weakEvolution hb hbound hMb hLb₁ hμ N P hP).probability s hs

/-- **Lemma 4.5 (`lem:internal`).** Let `R^N_s` be the reference evolution started from `P` with
`W²(P^{(m)}, μ_0^{⊗m}) ≤ C₀ m²/N²`. For `0 ≤ s ≤ T` and `m ≤ N`, the internal part
`I_m(s) = N⁻² ∫ ∑ᵢ |Ξ_s(x)ᵢ|² dR^{(m)}_s` of the source satisfies `√I_m(s) ≤ A₀ m/N`, with
`A₀ = 2M + L_c e^{LT} √C₀`. -/
theorem sqrt_internal_le (hS : IsSmoothCoefficients a K La L₁ L₂ M) (hP : HasSecondMoment P)
    {C₀ s T : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T) (hm : m ≤ N)
    (hinit : wassersteinSq (marginal hm P) (tensorLaw (μ 0) m) ≤
      ENNReal.ofReal (C₀ * (m : ℝ) ^ 2 / (N : ℝ) ^ 2)) :
    √(((N : ℝ) ^ 2)⁻¹ * ∫ x, ∑ i, ‖internalField (μ s) K x i‖ ^ 2
        ∂marginal hm (PrescribedReference.law hb hbound hMb hLb₁ hμ N P s)) ≤
      sourceA₀ C₀ T La L₁ L₂ M * m / N := by
  have hA := hS.assumptionA
  have := hμ.1 s hs
  have := law_isProbabilityMeasure hb hbound hMb hLb₁ hμ P hP hs
  have : IsProbabilityMeasure
      (marginal hm (PrescribedReference.law hb hbound hMb hLb₁ hμ N P s)) :=
    Measure.isProbabilityMeasure_map (measurable_restrictCoordinates hm).aemeasurable
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · simp
  have hN : (0 : ℝ) < N := by exact_mod_cast hm0.trans_le hm
  have hmN : (m : ℝ) / N ≤ 1 := div_le_one_of_le₀ (by exact_mod_cast hm) hN.le
  have hL := lipL_nonneg hA.La_nonneg hA.L₁_nonneg
  have hLc := lipC_nonneg hA.L₁_nonneg hA.L₂_nonneg
  have hW := marginal_wassersteinSq_le_sharp hS hb hbound hMb hLb₁ hμ P hs hm hinit
  have h := sqrt_integral_internalField_le hS (μ s) _ hW
  have hsq : √(Real.exp (lipL La L₁ * s) ^ 2 * C₀ * (m : ℝ) ^ 2 / (N : ℝ) ^ 2) =
      Real.exp (lipL La L₁ * s) * √C₀ * (m / N) := by
    rw [show Real.exp (lipL La L₁ * s) ^ 2 * C₀ * (m : ℝ) ^ 2 / (N : ℝ) ^ 2 =
      (Real.exp (lipL La L₁ * s) * (m / N)) ^ 2 * C₀ by field_simp,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
    ring
  rw [hsq] at h
  have he : Real.exp (lipL La L₁ * s) ≤ Real.exp (lipL La L₁ * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hsT hL)
  rw [Real.sqrt_mul (by positivity), Real.sqrt_inv, Real.sqrt_sq hN.le]
  calc (N : ℝ)⁻¹ * √(∫ x, ∑ i, ‖internalField (μ s) K x i‖ ^ 2
        ∂marginal hm (PrescribedReference.law hb hbound hMb hLb₁ hμ N P s)) ≤
      (N : ℝ)⁻¹ * (2 * M * m + m * lipC L₁ L₂ * (Real.exp (lipL La L₁ * s) * √C₀ * (m / N))) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ ≤ (N : ℝ)⁻¹ * (2 * M * m + m * lipC L₁ L₂ * (Real.exp (lipL La L₁ * T) * √C₀ * 1)) := by
        have := hA.M_nonneg
        gcongr
    _ = _ := by
        unfold sourceA₀
        field_simp

end Reference

end SharpWasserstein.Sharp.Source
