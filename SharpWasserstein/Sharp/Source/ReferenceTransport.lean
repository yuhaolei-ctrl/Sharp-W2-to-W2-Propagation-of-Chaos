/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import SharpWasserstein.Sharp.Source.ReferenceDrift
public import SharpWasserstein.PrescribedEntropyProfile
public import SharpWasserstein.EuclideanFlow

/-!
# The reference evolution in Wasserstein distance (Lemma 3.5)

Lemma 3.5 (`lem:reference-W`) of the paper states that the reference evolution
`R^N_s = P_{N,0} Q_{0,s}^{⊗N}` of Section 3.3 (`N` independent solutions of the linear equation
`dY = B_s(Y) ds + √2 dW` started from `P_{N,0}`) satisfies
`W(R^{(m)}_s, μ_s^{⊗m}) ≤ e^{Ls} √C₀ m/N`, where `L = L_a + L₁`.

The proof runs an arbitrary coupling of the initial laws through the reference dynamics, with
the same Brownian path in each pair of coupled coordinates: the difference of two coupled
coordinates solves `d(Y - Y')/dr = B_r(Y) - B_r(Y')`, and the Euclidean Lipschitz bound
`Lip(B_r) ≤ L` (Lemma 3.1, `eq:lip`) gives `|Y_s - Y'_s| ≤ e^{Ls} |Y_0 - Y'_0|`. Here the
stability estimate of the development (`FiniteAdditiveTrajectory.stability`) is transported to
`EuclideanSpace ℝ (Fin d)`, so that no dimension-dependent conversion between the sup norm and
the Euclidean norm enters (the older `DecoupledFlow.law_wassersteinSq_le` costs a factor `d`).

## Main statements

* `positionSq_sub_le_of_trajectory`: Euclidean synchronous stability of one trajectory.
* `solution_productCost_le`, `law_wassersteinSq_le`: synchronous stability of the decoupled
  flow, with factor `e^{2Lt}`.
* `marginal_wassersteinSq_le_exp`: the same for the reference evolution `R^N_s`.
* `marginal_wassersteinSq_le_sharp`: **Lemma 3.5**,
  `W²(R^{(k)}_s, μ_s^{⊗k}) ≤ e^{2Ls} C₀ k²/N²`.
* `marginal_profile_uniform_sharp`: the same bound, uniformly for `s ∈ [0, T]`, with `e^{2LT}`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace SharpWasserstein.Sharp.Source

variable {d : ℕ}

/-- The coordinate sum of squares `positionSq x` is the square of the Euclidean norm. -/
theorem positionSq_eq_norm_toLp_sq (x : Position d) :
    positionSq x = ‖WithLp.toLp 2 x‖ ^ 2 := by
  rw [norm_toLp_sq]
  rfl

/-- **Euclidean synchronous stability.** Two solutions of `X_t = x₀ + ∫₀ᵗ v_s(X_s) ds + w_t`
driven by the same forcing `w`, where the Euclidean conjugate of each `v_s` is `L`-Lipschitz,
satisfy `|X_t - Y_t|² ≤ e^{2Lt} |x₀ - y₀|²` for the Euclidean norm. -/
theorem positionSq_sub_le_of_trajectory {v : ℝ → Position d → Position d} {L : ℝ≥0}
    (he : ∀ t, LipschitzWith L (GaussianBridge.euclideanDrift v t))
    {w X Y : ℝ → Position d} {x₀ y₀ : Position d} {T t : ℝ}
    (hX : FiniteAdditiveTrajectory v w x₀ T X) (hY : FiniteAdditiveTrajectory v w y₀ T Y)
    (ht : t ∈ Icc 0 T) :
    positionSq (X t - Y t) ≤ Real.exp ((L : ℝ) * t) ^ 2 * positionSq (x₀ - y₀) := by
  have hs := (hX.map_equiv (toEuclid d)).stability (K := L) (fun s _ => he s)
    (hY.map_equiv (toEuclid d)) ht
  simp only [← map_sub] at hs
  have hs₂ := (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hs
  rw [positionSq_eq_norm_toLp_sq, positionSq_eq_norm_toLp_sq]
  simpa only [toEuclid_apply, mul_pow, mul_comm] using hs₂

section DecoupledFlow

variable {v : ℝ → Position d → Position d} {Mv Kv L : ℝ≥0}
  (hv : Continuous (Function.uncurry v)) (hb : ∀ t x, ‖v t x‖ ≤ Mv)
  (hl : ∀ t, LipschitzWith Kv (v t))

/-- Synchronous stability of the decoupled flow for the unnormalized Euclidean cost, with the
Euclidean Lipschitz constant `L` of the one-particle drift. -/
theorem solution_productCost_le (he : ∀ t, LipschitzWith L (GaussianBridge.euclideanDrift v t))
    {N : ℕ} {T : ℝ} (hT : 0 ≤ T) (x y : Configuration d N)
    (w : Fin N → C(Icc 0 T, Position d)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    productCost (DecoupledFlow.solution hv hb hl hT (x, w) t)
        (DecoupledFlow.solution hv hb hl hT (y, w) t) ≤
      Real.exp ((L : ℝ) * t) ^ 2 * productCost x y := by
  rw [productCost_eq_sum_positionSq, productCost_eq_sum_positionSq, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => positionSq_sub_le_of_trajectory he
    (DecoupledFlow.solution_coordinate_trajectory hv hb hl hT (x, w) i)
    (DecoupledFlow.solution_coordinate_trajectory hv hb hl hT (y, w) i) ht

variable {N : ℕ} {T : ℝ} [MeasurableSpace C(Icc 0 T, Position d)]
  [BorelSpace C(Icc 0 T, Position d)]

/-- Synchronous coupling of the decoupled flow: `W²` is multiplied by at most `e^{2Lt}`,
uniformly in the number of particles and in the dimension. -/
theorem law_wassersteinSq_le (he : ∀ t, LipschitzWith L (GaussianBridge.euclideanDrift v t))
    (hT : 0 ≤ T) (P Q : Measure (Configuration d N)) (ξ : Measure C(Icc 0 T, Position d))
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure ξ]
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    wassersteinSq (DecoupledFlow.law hv hb hl hT P ξ t) (DecoupledFlow.law hv hb hl hT Q ξ t) ≤
      ENNReal.ofReal (Real.exp ((L : ℝ) * t) ^ 2) * wassersteinSq P Q :=
  wassersteinSq_randomMapLaw_le _ (DecoupledFlow.solution_measurable hv hb hl hT ht) _ P Q
    (by positivity) (fun x y w => solution_productCost_le hv hb hl he hT x y w ht)

end DecoupledFlow

section Reference

variable {a : Position d → Position d} {K : Position d → Position d → Position d}
  {La L₁ L₂ M Mb Lb₁ Lb₂ : ℝ} (hS : IsSmoothCoefficients a K La L₁ L₂ M)
  (hb : BoundedSmoothKernel (kernelOf a K)) (hbound : KernelBounds (kernelOf a K) Mb Lb₁ Lb₂)
  (hMb : 0 ≤ Mb) (hLb₁ : 0 ≤ Lb₁)
  {μ : ℝ → Measure (Position d)} (hμ : IsLimitEvolution (kernelOf a K) μ)
  {N : ℕ} (P : Measure (Configuration d N)) [IsProbabilityMeasure P]

include hS in
/-- Synchronous stability of the reference evolution relative to the limit law: for `t > 0`,
`W²(R^{(k)}_t, μ_t^{⊗k}) ≤ e^{2Lt} W²(P^{(k)}_{N,0}, μ_0^{⊗k})` with `L = L_a + L₁`. -/
theorem marginal_wassersteinSq_le_exp {k : ℕ} (hk : k ≤ N) {t : ℝ} (ht : 0 < t) :
    wassersteinSq (marginal hk (PrescribedReference.law hb hbound hMb hLb₁ hμ N P t))
      (tensorLaw (μ t) k) ≤
    ENNReal.ofReal (Real.exp (lipL La L₁ * t) ^ 2) *
      wassersteinSq (marginal hk P) (tensorLaw (μ 0) k) := by
  have := hμ.1 0 le_rfl
  have he := IsSmoothCoefficients.lipschitzWith_euclideanDrift_singleDrift hS hμ
  have hh := law_wassersteinSq_le
    (PrescribedReference.singleDrift_continuous hb hbound hLb₁ hμ)
    (PrescribedReference.singleDrift_bound hbound hMb hμ)
    (PrescribedReference.singleDrift_lipschitz hb hbound hLb₁ hμ) he
    ht.le (marginal hk P) (tensorLaw (μ 0) k) (BrownianNoise.positionLaw d t)
    (show t ∈ Icc 0 t from ⟨ht.le, le_rfl⟩)
  change wassersteinSq (DecoupledFlow.brownianLaw _ _ _ ht.le (marginal hk P))
    (DecoupledFlow.brownianLaw _ _ _ ht.le (tensorLaw (μ 0) k)) ≤ _ at hh
  rw [DecoupledFlow.brownianLaw_tensor,
    PrescribedReference.singleBrownianLaw_eq_supplied hb hbound hMb hLb₁ hμ ht,
    coe_lipLNN hS.assumptionA.La_nonneg hS.assumptionA.L₁_nonneg] at hh
  rw [PrescribedReference.law_eq_decoupled hb hbound hMb hLb₁ hμ N P ht]
  change wassersteinSq (marginal hk (DecoupledFlow.brownianLaw _ _ _ ht.le P)) _ ≤ _
  rw [DecoupledFlow.brownianLaw_marginal]
  exact hh

include hS in
/-- **Lemma 3.5 (`lem:reference-W`).** If the initial law satisfies
`W²(P^{(k)}_{N,0}, μ_0^{⊗k}) ≤ C₀ k²/N²`, then for every `s ≥ 0` the reference evolution
satisfies `W²(R^{(k)}_s, μ_s^{⊗k}) ≤ e^{2Ls} C₀ k²/N²`, `L = L_a + L₁`. -/
theorem marginal_wassersteinSq_le_sharp {C₀ s : ℝ} (hs : 0 ≤ s) {k : ℕ} (hk : k ≤ N)
    (hinit : wassersteinSq (marginal hk P) (tensorLaw (μ 0) k) ≤
      ENNReal.ofReal (C₀ * (k : ℝ) ^ 2 / (N : ℝ) ^ 2)) :
    wassersteinSq (marginal hk (PrescribedReference.law hb hbound hMb hLb₁ hμ N P s))
      (tensorLaw (μ s) k) ≤
      ENNReal.ofReal (Real.exp (lipL La L₁ * s) ^ 2 * C₀ * (k : ℝ) ^ 2 / (N : ℝ) ^ 2) := by
  rcases hs.eq_or_lt with rfl | hs
  · rw [PrescribedReference.law_initial]
    simpa using hinit
  refine (marginal_wassersteinSq_le_exp hS hb hbound hMb hLb₁ hμ P hk hs).trans ?_
  calc _ ≤ ENNReal.ofReal (Real.exp (lipL La L₁ * s) ^ 2) *
        ENNReal.ofReal (C₀ * (k : ℝ) ^ 2 / (N : ℝ) ^ 2) := mul_le_mul_right hinit _
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      ring_nf

include hS in
/-- **Lemma 3.5, uniformly on `[0, T]`.** Under the initial bound of
`marginal_wassersteinSq_le_sharp`, `W²(R^{(k)}_s, μ_s^{⊗k}) ≤ e^{2LT} C₀ k²/N²` for
`0 ≤ s ≤ T`. -/
theorem marginal_profile_uniform_sharp {C₀ T : ℝ} (hC₀ : 0 ≤ C₀) {k : ℕ} (hk : k ≤ N)
    (hinit : wassersteinSq (marginal hk P) (tensorLaw (μ 0) k) ≤
      ENNReal.ofReal (C₀ * (k : ℝ) ^ 2 / (N : ℝ) ^ 2)) {s : ℝ} (hs : s ∈ Icc 0 T) :
    wassersteinSq (marginal hk (PrescribedReference.law hb hbound hMb hLb₁ hμ N P s))
      (tensorLaw (μ s) k) ≤
      ENNReal.ofReal (Real.exp (lipL La L₁ * T) ^ 2 * C₀ * (k : ℝ) ^ 2 / (N : ℝ) ^ 2) := by
  refine (marginal_wassersteinSq_le_sharp hS hb hbound hMb hLb₁ hμ P hs.1 hk hinit).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have hL := lipL_nonneg hS.assumptionA.La_nonneg hS.assumptionA.L₁_nonneg
  have he : Real.exp (lipL La L₁ * s) ≤ Real.exp (lipL La L₁ * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hs.2 hL)
  gcongr

end Reference

end SharpWasserstein.Sharp.Source
