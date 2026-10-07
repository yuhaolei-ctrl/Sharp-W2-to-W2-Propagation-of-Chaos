/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import SharpWasserstein.Sharp.Constants
public import SharpWasserstein.Sharp.Hierarchy.SplitKernel
public import SharpWasserstein.InternalDriftFiniteBounds

/-!
# The drift of level `m` of the tangent hierarchy

For `1 ≤ m ≤ N` the paper sets (`eq:Bm-Phi`)
`b^{[m]}_i(x) = a(xᵢ) + N⁻¹ ∑_{j ≤ m} K(xᵢ, xⱼ)`, so that all of the one-body drift sits in the
level-`m` generator `𝓛_m = Δ + b^{[m]} · ∇`. This file defines this drift on Euclidean
configurations of `m` particles (`splitDrift`), proves that it is smooth with bounded
derivatives, inherits the period of `a` and `K`, and has Euclidean Lipschitz constant
`Λ = L_a + L₁ + L₂` uniformly in `m ≤ N` (the bound `‖Db^{[m]}‖_op ≤ Λ` used in
`eq:drift-id`, proved by Minkowski's inequality as for `Lip(b_N)` in Lemma 3.1).

It also records the algebraic identity relating `splitDrift` to the development's internal
drift `internalDrift N (kernelOf a K)` of the combined kernel `a(x) + K(x, y)`, in which only
the fraction `m/N` of `a` is internal.

## Main definitions

* `oneBody a`: the field `x ↦ (a(xᵢ))ᵢ`.
* `splitDrift N a K`: the drift `b^{[m]}`.

## Main statements

* `splitDrift_lipschitz`, `norm_fderiv_splitDrift_le`: the Euclidean bound `Λ`.
* `splitDrift_smooth`, `splitDrift_allDerivativesBounded`, `splitDrift_lattice`.
* `internalDrift_kernelOf_add`: `internalDrift N (kernelOf a K) + ((N - m)/N) • oneBody a =
  splitDrift N a K`.
-/

@[expose] public section

noncomputable section

open scoped ContDiff InnerProductSpace BigOperators

namespace SharpWasserstein.Sharp.Hierarchy

open WeightedTangent NoiseAverage ExternalInteractionPeriodic PropagatedSourceEquation

variable {d m : ℕ}

/-- The squared Euclidean norm of a configuration is the sum of the squared Euclidean norms of
its particles. -/
theorem norm_sq_configurationEuclidean (z : Configuration d m) :
    ‖configurationEuclidean d m z‖ ^ 2 = ∑ i, ‖WithLp.toLp 2 (z i)‖ ^ 2 := by
  rw [configurationEuclidean_norm_sq]
  apply Finset.sum_congr rfl
  intro i _
  rw [EuclideanSpace.real_norm_sq_eq]

/-- Configurations of zero particles are all equal. -/
theorem point_zero_eq (x y : Point (0*d)) : x = y := by
  ext i
  have := i.isLt
  simp at this

/-- The one-body field `x ↦ (a(xᵢ))ᵢ` on Euclidean configurations of `m` particles. -/
def oneBody (a : Position d → Position d) (x : Point (m*d)) : Point (m*d) :=
  configurationEuclidean d m (fun i => a ((configurationEuclidean d m).symm x i))

/-- The drift `b^{[m]}_i(x) = a(xᵢ) + N⁻¹ ∑_{j ≤ m} K(xᵢ, xⱼ)` of level `m` (`eq:Bm-Phi`). -/
def splitDrift (N : ℕ) (a : Position d → Position d) (K : Position d → Position d → Position d)
    (x : Point (m*d)) : Point (m*d) :=
  oneBody a x + internalDrift N K x

/-- For `m > 0` the one-body field is the internal drift of the one-body kernel at
normalization `m`. -/
theorem oneBody_eq_internalDrift (hm : 0 < m) (a : Position d → Position d) :
    oneBody (m := m) a = internalDrift m (oneBodyKernel a) := by
  funext x
  unfold oneBody internalDrift oneBodyKernel
  congr 1
  funext i
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul, inv_mul_cancel₀ hm', one_smul]

/-- The internal drift of the combined kernel `a(x) + K(x, y)` contains the fraction `m/N` of
the one-body drift. -/
theorem internalDrift_kernelOf (N : ℕ) (a : Position d → Position d)
    (K : Position d → Position d → Position d) (x : Point (m*d)) :
    internalDrift N (kernelOf a K) x = ((m : ℝ) / N) • oneBody a x + internalDrift N K x := by
  unfold internalDrift oneBody kernelOf
  rw [← map_smul, ← map_add]
  congr 1
  funext i
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_add, Pi.add_apply, Pi.smul_apply]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, div_eq_inv_mul]

/-- Adding the external fraction `(N - m)/N` of the one-body drift to the internal drift of the
combined kernel gives the drift `b^{[m]}` of the paper. -/
theorem internalDrift_kernelOf_add {N : ℕ} (hN : 0 < N) (a : Position d → Position d)
    (K : Position d → Position d → Position d) (x : Point (m*d)) :
    internalDrift N (kernelOf a K) x + (((N : ℝ) - m) / N) • oneBody a x =
      splitDrift N a K x := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  rw [internalDrift_kernelOf, splitDrift, add_comm (((m : ℝ) / N) • oneBody a x), add_assoc,
    ← add_smul]
  have h1 : (m : ℝ) / N + ((N : ℝ) - m) / N = 1 := by field_simp; ring
  rw [h1, one_smul, add_comm]

/-- At the top level `m = N` the internal drift of the combined kernel is `b^{[N]} = b_N`. -/
theorem internalDrift_kernelOf_self {N : ℕ} (a : Position d → Position d)
    (K : Position d → Position d → Position d) (x : Point (N*d)) :
    internalDrift N (kernelOf a K) x = splitDrift N a K x := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    exact point_zero_eq _ _
  · have h := internalDrift_kernelOf_add hN a K x
    rwa [sub_self, zero_div, zero_smul, add_zero] at h

variable {N : ℕ} {a : Position d → Position d} {K : Position d → Position d → Position d}
  {La L₁ L₂ M : ℝ}

/-- The one-body field is smooth. -/
theorem oneBody_smooth (h : SplitKernel a K La L₁ L₂ M) : ContDiff ℝ ∞ (oneBody (m := m) a) := by
  apply (configurationEuclidean d m).contDiff.comp
  apply contDiff_pi.mpr
  intro i
  exact h.contDiff_a.comp ((contDiff_pi.mp (configurationEuclidean d m).symm.contDiff) i)

/-- The drift `b^{[m]}` is smooth. -/
theorem splitDrift_smooth (h : SplitKernel a K La L₁ L₂ M) (N : ℕ) :
    ContDiff ℝ ∞ (splitDrift (m := m) N a K) :=
  (oneBody_smooth h).add (internalDrift_smooth h.smooth_K N)

/-- A sum of smooth maps with bounded derivatives has bounded derivatives. -/
theorem allDerivativesBounded_add {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f g : E → F} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (hBf : AllDerivativesBounded f) (hBg : AllDerivativesBounded g) :
    AllDerivativesBounded (fun x => f x + g x) := by
  intro n
  obtain ⟨C, hC, hf'⟩ := hBf n
  obtain ⟨D, hD, hg'⟩ := hBg n
  refine ⟨C + D, add_nonneg hC hD, fun x => ?_⟩
  have hn : ((n : ℕ∞) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have he : (fun x => f x + g x) = f + g := rfl
  rw [he, iteratedFDeriv_add_apply (hf.contDiffAt.of_le hn) (hg.contDiffAt.of_le hn)]
  exact (norm_add_le _ _).trans (add_le_add (hf' x) (hg' x))

/-- The drift `b^{[m]}` has bounded derivatives of all orders (for `m > 0`). -/
theorem splitDrift_allDerivativesBounded (h : SplitKernel a K La L₁ L₂ M) (N : ℕ)
    (hm : 0 < m) : AllDerivativesBounded (splitDrift (m := m) N a K) := by
  have h1 : AllDerivativesBounded (oneBody (m := m) a) := by
    rw [oneBody_eq_internalDrift hm]
    exact internalDrift_allDerivativesBounded h.smooth_a hm
  exact allDerivativesBounded_add (oneBody_smooth h) (internalDrift_smooth h.smooth_K N) h1
    (internalDrift_allDerivativesBounded h.smooth_K hm)

/-- The Euclidean Minkowski estimate behind `Lip(b^{[m]}) ≤ Λ`: if `cᵢ ≤ α uᵢ + β S/N` with
`S = ∑ⱼ uⱼ` and `m ≤ N`, then `∑ᵢ cᵢ² ≤ (α + β)² ∑ᵢ uᵢ²`. -/
theorem sum_sq_le_of_le_minkowski {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hmN : m ≤ N)
    (u c : Fin m → ℝ) (hu : ∀ i, 0 ≤ u i) (hc0 : ∀ i, 0 ≤ c i)
    (hc : ∀ i, c i ≤ α * u i + β * (∑ j, u j) / N) :
    ∑ i, c i ^ 2 ≤ (α + β) ^ 2 * ∑ i, u i ^ 2 := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp
  have hN : (0 : ℝ) < N := Nat.cast_pos.2 (lt_of_lt_of_le hm hmN)
  set S := ∑ j, u j
  set U := ∑ i, u i ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ => hu j
  have hCS : S ^ 2 ≤ m * U := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin m => (1 : ℝ)) u
    simpa [S, U] using this
  have hmN' : (m : ℝ) ≤ N := Nat.cast_le.2 hmN
  set γ := β * S / N
  have hγ : 0 ≤ γ := by positivity
  have h1 : ∑ i, c i ^ 2 ≤ ∑ i, (α * u i + γ) ^ 2 :=
    Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (hc0 i) (hc i) 2
  have h2 : ∑ i, (α * u i + γ) ^ 2 = α ^ 2 * U + 2 * α * γ * S + m * γ ^ 2 := by
    simp only [add_sq, Finset.sum_add_distrib, mul_pow, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, U, S]
    have : ∑ i, 2 * (α * u i) * γ = 2 * α * γ * ∑ i, u i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]
  -- `2αγS ≤ 2αβU` and `mγ² ≤ β²U`
  have h3 : γ * S ≤ β * U := by
    have : γ * S = β * S ^ 2 / N := by simp only [γ]; ring
    rw [this, div_le_iff₀ hN]
    calc β * S ^ 2 ≤ β * (m * U) := mul_le_mul_of_nonneg_left hCS hβ
      _ ≤ β * (N * U) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hmN' (Finset.sum_nonneg fun i _ => sq_nonneg _)) hβ
      _ = β * U * N := by ring
  have h4 : m * γ ^ 2 ≤ β ^ 2 * U := by
    have : (m : ℝ) * γ ^ 2 = β ^ 2 * (m * S ^ 2) / N ^ 2 := by simp only [γ]; field_simp
    rw [this, div_le_iff₀ (by positivity)]
    have hU : 0 ≤ U := Finset.sum_nonneg fun i _ => sq_nonneg _
    calc β ^ 2 * (m * S ^ 2) ≤ β ^ 2 * (m * (m * U)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hCS (Nat.cast_nonneg m))
            (sq_nonneg β)
      _ ≤ β ^ 2 * (N * (N * U)) := by gcongr
      _ = β ^ 2 * U * N ^ 2 := by ring
  rw [h2] at h1
  nlinarith [mul_le_mul_of_nonneg_left h3 (show 0 ≤ 2 * α by positivity)]

/-- `b^{[m]}` is `Λ`-Lipschitz for the Euclidean norm, uniformly in `m ≤ N` (Lemma 3.1 and
`eq:drift-id`). -/
theorem splitDrift_norm_sub_le (h : SplitKernel a K La L₁ L₂ M) (hmN : m ≤ N)
    (x x' : Point (m*d)) :
    ‖splitDrift N a K x - splitDrift N a K x'‖ ≤ lipΛ La L₁ L₂ * ‖x - x'‖ := by
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    have : m = 0 := Nat.le_zero.1 hmN
    subst this
    rw [point_zero_eq x x', sub_self, sub_self, norm_zero, mul_zero]
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hNpos
  set z := (configurationEuclidean d m).symm x
  set z' := (configurationEuclidean d m).symm x'
  let u : Fin m → ℝ := fun i => ‖WithLp.toLp 2 (z i) - WithLp.toLp 2 (z' i)‖
  let D : Configuration d m := fun i =>
    (a (z i) + (N : ℝ)⁻¹ • ∑ j, K (z i) (z j)) - (a (z' i) + (N : ℝ)⁻¹ • ∑ j, K (z' i) (z' j))
  have hdiff : splitDrift N a K x - splitDrift N a K x' = configurationEuclidean d m D := by
    have hD : D = ((fun i => a (z i)) + fun i => (N : ℝ)⁻¹ • ∑ j, K (z i) (z j)) -
        ((fun i => a (z' i)) + fun i => (N : ℝ)⁻¹ • ∑ j, K (z' i) (z' j)) := rfl
    rw [hD, map_sub, map_add, map_add]
    rfl
  have hxx : x - x' = configurationEuclidean d m (z - z') := by
    simp only [z, z', map_sub, ContinuousLinearEquiv.apply_symm_apply]
  have hU : ‖x - x'‖ ^ 2 = ∑ i, u i ^ 2 := by
    rw [hxx, norm_sq_configurationEuclidean]
    rfl
  have hblock (i : Fin m) : ‖WithLp.toLp 2 (D i)‖ ≤
      (La + L₁) * u i + L₂ * (∑ j, u j) / N := by
    have hD : WithLp.toLp 2 (D i) =
        (WithLp.toLp 2 (a (z i)) - WithLp.toLp 2 (a (z' i))) +
          (N : ℝ)⁻¹ • ∑ j, (WithLp.toLp 2 (K (z i) (z j)) - WithLp.toLp 2 (K (z' i) (z' j))) := by
      simp only [D, WithLp.toLp_sub, WithLp.toLp_add, WithLp.toLp_smul, WithLp.toLp_sum,
        Finset.sum_sub_distrib, smul_sub]
      abel
    rw [hD]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hNr)]
    have hs : ‖∑ j, (WithLp.toLp 2 (K (z i) (z j)) - WithLp.toLp 2 (K (z' i) (z' j)))‖ ≤
        m * L₁ * u i + L₂ * ∑ j, u j := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ j, ‖WithLp.toLp 2 (K (z i) (z j)) - WithLp.toLp 2 (K (z' i) (z' j))‖
          ≤ ∑ j, (L₁ * u i + L₂ * u j) :=
            Finset.sum_le_sum fun j _ => h.norm_sub_K_le _ _ _ _
        _ = m * L₁ * u i + L₂ * ∑ j, u j := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul, Finset.mul_sum]; ring
    have hmN' : (m : ℝ) / N ≤ 1 := (div_le_one hNr).2 (Nat.cast_le.2 hmN)
    have hui : 0 ≤ u i := norm_nonneg _
    calc ‖WithLp.toLp 2 (a (z i)) - WithLp.toLp 2 (a (z' i))‖ +
          (N : ℝ)⁻¹ * ‖∑ j, (WithLp.toLp 2 (K (z i) (z j)) - WithLp.toLp 2 (K (z' i) (z' j)))‖
        ≤ La * u i + (N : ℝ)⁻¹ * (m * L₁ * u i + L₂ * ∑ j, u j) :=
          add_le_add (h.norm_sub_a_le _ _) (mul_le_mul_of_nonneg_left hs (by positivity))
      _ = La * u i + ((m : ℝ) / N) * L₁ * u i + L₂ * (∑ j, u j) / N := by ring
      _ ≤ La * u i + 1 * L₁ * u i + L₂ * (∑ j, u j) / N := by
          gcongr
          exact h.L₁_nonneg
      _ = _ := by ring
  have hsum := sum_sq_le_of_le_minkowski (add_nonneg h.La_nonneg h.L₁_nonneg) h.L₂_nonneg hmN
    u (fun i => ‖WithLp.toLp 2 (D i)‖) (fun i => norm_nonneg _) (fun i => norm_nonneg _) hblock
  have hsq : ‖splitDrift N a K x - splitDrift N a K x'‖ ^ 2 ≤
      (lipΛ La L₁ L₂ * ‖x - x'‖) ^ 2 := by
    rw [hdiff, norm_sq_configurationEuclidean, mul_pow, hU]
    simpa only [lipΛ] using hsum
  have hΛ : 0 ≤ lipΛ La L₁ L₂ := lipΛ_nonneg h.La_nonneg h.L₁_nonneg h.L₂_nonneg
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 hsq

/-- `b^{[m]}` is `Λ`-Lipschitz. -/
theorem splitDrift_lipschitz (h : SplitKernel a K La L₁ L₂ M) (hmN : m ≤ N) :
    LipschitzWith ⟨lipΛ La L₁ L₂, lipΛ_nonneg h.La_nonneg h.L₁_nonneg h.L₂_nonneg⟩
      (splitDrift (m := m) N a K) :=
  LipschitzWith.of_dist_le_mul fun x x' => by
    rw [dist_eq_norm, dist_eq_norm]
    exact splitDrift_norm_sub_le h hmN x x'

/-- `‖Db^{[m]}‖_op ≤ Λ` (`eq:drift-id`). -/
theorem norm_fderiv_splitDrift_le (h : SplitKernel a K La L₁ L₂ M) (hmN : m ≤ N)
    (x : Point (m*d)) : ‖fderiv ℝ (splitDrift (m := m) N a K) x‖ ≤ lipΛ La L₁ L₂ :=
  norm_fderiv_le_of_lipschitz ℝ (splitDrift_lipschitz h hmN)

/-- The drift `b^{[m]}` inherits a common coordinate period `P` of `a` and `K`. -/
theorem splitDrift_lattice {P : ℝ} (hm : 0 < m)
    (ha : ∀ i x, a (x + Pi.single i P) = a x)
    (hx : ∀ i x y, K (x + Pi.single i P) y = K x y)
    (hy : ∀ i x y, K x (y + Pi.single i P) = K x y)
    (N : ℕ) (k : Fin (m*d) → ℤ) (z : Point (m*d)) :
    splitDrift N a K (z + euclideanLattice P k) = splitDrift N a K z := by
  unfold splitDrift
  rw [oneBody_eq_internalDrift hm,
    internalDrift_lattice (b := oneBodyKernel a) (fun i x y => ha i x) (fun _ _ _ => rfl),
    internalDrift_lattice hx hy]

end SharpWasserstein.Sharp.Hierarchy
