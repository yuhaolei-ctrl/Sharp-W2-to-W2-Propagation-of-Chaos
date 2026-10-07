/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import SharpWasserstein.Sharp.Mollify
public import SharpWasserstein.Sharp.SmoothCoefficients

/-!
# Smooth approximating coefficients in coordinates

The smooth approximations `aⁿ, Kⁿ` of Lemma 7.1 (`SharpWasserstein.Sharp.exists_smooth_approx`)
live on `EuclideanSpace ℝ (Fin d)`, while the smooth case of Theorem 2.1
(`SharpWasserstein.Sharp.SmoothSharpCase`) is stated for coefficients on coordinates satisfying
`IsSmoothCoefficients`. This file shows that the coordinate forms `coordMap aⁿ` and
`coordMap₂ Kⁿ` satisfy `IsSmoothCoefficients` with the same constants: smoothness and bounds on
all derivatives transfer through the continuous linear equivalence `PiLp.continuousLinearEquiv`
between `EuclideanSpace ℝ (Fin d)` and `Fin d → ℝ`.

## Main statements

* `norm_iteratedFDeriv_conj_le`: the iterated derivatives of `eL ∘ f ∘ eR` for continuous linear
  equivalences `eL`, `eR` are controlled by those of `f`.
* `isSmoothCoefficients_coordMap`: the coordinate forms of smooth bounded coefficients satisfying
  Assumption A satisfy `IsSmoothCoefficients`.
-/

@[expose] public section

noncomputable section

open scoped ContDiff

namespace SharpWasserstein.Sharp.Final

/-- The iterated derivatives of a function conjugated by continuous linear equivalences:
`‖Dⁿ (eL ∘ f ∘ eR) x‖ ≤ ‖eL‖ ‖Dⁿ f (eR x)‖ ‖eR‖ⁿ`. No smoothness of `f` is needed. -/
theorem norm_iteratedFDeriv_conj_le {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H] (eL : F ≃L[ℝ] G) (eR : H ≃L[ℝ] E) (f : E → F)
    (n : ℕ) (x : H) :
    ‖iteratedFDeriv ℝ n (eL ∘ f ∘ eR) x‖ ≤
      ‖(eL : F →L[ℝ] G)‖ * (‖iteratedFDeriv ℝ n f (eR x)‖ * ‖(eR : H →L[ℝ] E)‖ ^ n) := by
  rw [eL.iteratedFDeriv_comp_left]
  refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
  gcongr
  have h : iteratedFDeriv ℝ n (f ∘ eR) x =
      (iteratedFDeriv ℝ n f (eR x)).compContinuousLinearMap fun _ => (eR : H →L[ℝ] E) := by
    simp only [← iteratedFDerivWithin_univ]
    simpa using eR.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (Set.mem_univ _) n
  rw [h]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans_eq ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

variable {d : ℕ}

/-- The coordinate map of `ℝᵈ` as a continuous linear equivalence. -/
abbrev coordCLE (d : ℕ) : EuclideanSpace ℝ (Fin d) ≃L[ℝ] Position d :=
  PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin d => ℝ

/-- The coordinate form of a map is its conjugate by the coordinate equivalence. -/
theorem coordMap_eq_comp (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :
    coordMap f = coordCLE d ∘ f ∘ (coordCLE d).symm :=
  rfl

/-- The coordinate form of an interaction, uncurried, is the conjugate of the uncurried
interaction by the coordinate equivalences. -/
theorem uncurry_coordMap₂_eq_comp
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :
    Function.uncurry (coordMap₂ K) =
      coordCLE d ∘ Function.uncurry K ∘ ((coordCLE d).symm.prodCongr (coordCLE d).symm) :=
  rfl

/-- **Smooth coefficients in coordinates.** If `a, K` satisfy Assumption A, are smooth, `a` is
bounded, and all derivatives of `a` and of `K` are bounded (the conclusions of Lemma 7.1,
`exists_smooth_approx`), then their coordinate forms satisfy `IsSmoothCoefficients` with the same
constants. -/
theorem isSmoothCoefficients_coordMap
    {a : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {La L₁ L₂ M : ℝ} (hA : SharpChaos.AssumptionA a K La L₁ L₂ M) (ha : ContDiff ℝ ∞ a)
    (hK : ContDiff ℝ ∞ (Function.uncurry K)) (hab : ∃ C, ∀ x, ‖a x‖ ≤ C)
    (hda : ∀ n : ℕ, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n a x‖ ≤ C)
    (hdK : ∀ n : ℕ, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (Function.uncurry K) z‖ ≤ C) :
    IsSmoothCoefficients (coordMap a) (coordMap₂ K) La L₁ L₂ M where
  assumptionA := hA
  contDiff_a := by
    rw [coordMap_eq_comp]
    exact (coordCLE d).contDiff.comp (ha.comp (coordCLE d).symm.contDiff)
  contDiff_K := by
    rw [uncurry_coordMap₂_eq_comp]
    exact (coordCLE d).contDiff.comp
      (hK.comp ((coordCLE d).symm.prodCongr (coordCLE d).symm).contDiff)
  bounded_a := by
    obtain ⟨C, hC⟩ := hab
    refine ⟨C, fun x => ?_⟩
    refine (norm_le_norm_toLp _).trans ?_
    simpa [coordMap] using hC (WithLp.toLp 2 x)
  iteratedFDeriv_a_le n := by
    obtain ⟨C, hC⟩ := hda n
    refine ⟨‖((coordCLE d : EuclideanSpace ℝ (Fin d) ≃L[ℝ] Position d) :
      EuclideanSpace ℝ (Fin d) →L[ℝ] Position d)‖ * (C *
        ‖(((coordCLE d).symm : Position d ≃L[ℝ] EuclideanSpace ℝ (Fin d)) :
          Position d →L[ℝ] EuclideanSpace ℝ (Fin d))‖ ^ n), fun x => ?_⟩
    rw [coordMap_eq_comp]
    exact (norm_iteratedFDeriv_conj_le _ _ a n x).trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (hC _) (by positivity)) (norm_nonneg _))
  iteratedFDeriv_K_le n := by
    obtain ⟨C, hC⟩ := hdK n
    refine ⟨‖((coordCLE d : EuclideanSpace ℝ (Fin d) ≃L[ℝ] Position d) :
      EuclideanSpace ℝ (Fin d) →L[ℝ] Position d)‖ * (C *
        ‖(((coordCLE d).symm.prodCongr (coordCLE d).symm :
          (Position d × Position d) ≃L[ℝ] (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) :
          (Position d × Position d) →L[ℝ] (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)))‖ ^
            n), fun z => ?_⟩
    rw [uncurry_coordMap₂_eq_comp]
    exact (norm_iteratedFDeriv_conj_le _ _ _ n z).trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (hC _) (by positivity)) (norm_nonneg _))

end SharpWasserstein.Sharp.Final
