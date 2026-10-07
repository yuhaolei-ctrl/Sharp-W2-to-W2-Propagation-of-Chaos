/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import SharpWasserstein.Sharp.Hierarchy.SplitDrift
public import SharpWasserstein.ExternalInteractionGradientCancellation

/-!
# Sharp pointwise bounds for the external operator `Φ`

For a smooth `f` on `m` particles, the external operator of Section 5.1 is
`Φf(x, y) = ∑ᵢ K(xᵢ, y) · ∇ᵢ f(x)`; in the development it is
`ExternalInteraction.interaction K f` on configurations of `m + 1` particles. This file proves
the two estimates of Lemma 5.2 (`lem:pointwise`) involving `Φ`, with the Euclidean constants of
Assumption A and no dependence on the dimension `d`:

* (`eq:cancel`) the diagonal term left after the Hessian cancellation satisfies
  `∑ᵢ ∇ᵢf · (D_xK(xᵢ, y))ᵀ ∇ᵢf ≤ L₁ |∇f|²`;
* (`eq:Phi-grad`) `|∇_{(x,y)} Φf|² ≤ m G (|∇f|² + |D²f|²_HS)`, `G = 2L₁² + L₂² + 2M²`.

The proof of the gradient bound follows the paper: the `x`-block of `∇Φf` is
`(D_xK)ᵀ∇f + D²f K` and is bounded by `L₁|∇f| + √m M |D²f|`, while the `y`-block is
`∑ₖ (D_yK(xₖ, y))ᵀ ∇ₖf` and is bounded by `√m L₂ |∇f|`. Each block is computed by pairing
`∇Φf` with its own projection.

## Main statements

* `diagonalEnergy_le_sharp`: `eq:cancel`.
* `lifted_hessian_cancellation_le_sharp`: the cancellation identity combined with `eq:cancel`.
* `interaction_gradient_norm_sq_le_sharp`: `eq:Phi-grad`.
-/

@[expose] public section

noncomputable section

open scoped ContDiff InnerProductSpace BigOperators

namespace SharpWasserstein.Sharp.Hierarchy

open WeightedTangent WeightedMarginal BochnerIdentity ExternalInteraction

variable {d m : ℕ}

/-! ### Euclidean block calculus -/

/-- The Euclidean inner product of two configurations is the sum of the particle inner
products. -/
theorem inner_configurationEuclidean (X Y : Configuration d m) :
    ⟪configurationEuclidean d m X, configurationEuclidean d m Y⟫_ℝ =
      ∑ i, ⟪WithLp.toLp 2 (X i), WithLp.toLp 2 (Y i)⟫_ℝ := by
  rw [PiLp.inner_apply]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  calc
    _ = ∑ p : Fin m × Fin d, Y p.1 p.2 * X p.1 p.2 := by
      symm
      apply Fintype.sum_equiv finProdFinEquiv
      rintro ⟨i, a⟩
      simp only [configurationEuclidean_apply_coordinate]
    _ = _ := Fintype.sum_prod_type _

/-- The sum of the particle norms of a configuration is at most `√m` times its Euclidean norm,
in squared form. -/
theorem sq_sum_norm_le (Y : Configuration d m) :
    (∑ i, ‖WithLp.toLp 2 (Y i)‖) ^ 2 ≤ m * ‖configurationEuclidean d m Y‖ ^ 2 := by
  rw [norm_sq_configurationEuclidean]
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin m => (1 : ℝ))
    (fun i => ‖WithLp.toLp 2 (Y i)‖)
  simpa using this

/-- Embedding of the extra particle into the configuration of `n + k` coordinates. -/
def suffixEmbedding (n k : ℕ) : Point k →L[ℝ] Point (n + k) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (Fin.addCases (fun _ => (0 : ℝ)) (fun i => v i))
      map_add' := fun v w => by ext k; cases k using Fin.addCases <;> simp
      map_smul' := fun c v => by ext k; cases k using Fin.addCases <;> simp }

theorem suffixEmbedding_apply (n k : ℕ) (v : Point k) :
    suffixEmbedding n k v = WithLp.toLp 2 (Fin.addCases (fun _ => (0 : ℝ)) (fun i => v i)) :=
  rfl

theorem inner_suffixEmbedding (n k : ℕ) (v : Point k) (x : Point (n + k)) :
    ⟪suffixEmbedding n k v, x⟫_ℝ = ⟪v, suffixProjection n k x⟫_ℝ := by
  simp [suffixEmbedding_apply, suffixProjection_apply, PiLp.inner_apply, Fin.sum_univ_add]

@[simp] theorem prefixProjection_suffixEmbedding (n k : ℕ) (v : Point k) :
    prefixProjection n k (suffixEmbedding n k v) = 0 := by
  ext i
  simp [prefixProjection_apply, suffixEmbedding_apply]

@[simp] theorem suffixProjection_suffixEmbedding (n k : ℕ) (v : Point k) :
    suffixProjection n k (suffixEmbedding n k v) = v := by
  ext i
  simp [suffixProjection_apply, suffixEmbedding_apply]

/-- Holding the first argument fixed identifies the true second partial derivative. -/
theorem uncurry_fderiv_second {b : Position d → Position d → Position d}
    (hb : BoundedSmoothKernel b) (x y u : Position d) :
    fderiv ℝ (Function.uncurry b) (x, y) (0, u) = fderiv ℝ (b x) y u := by
  have hq : HasFDerivAt (fun q : Position d => (x, q))
      ((0 : Position d →L[ℝ] Position d).prod (ContinuousLinearMap.id ℝ (Position d))) y :=
    (hasFDerivAt_const x y).prodMk (hasFDerivAt_id y)
  have hh := ((hb.smooth.differentiable (by simp) (x, y)).hasFDerivAt.comp y hq).fderiv
  have hv := congrArg (fun A : Position d →L[ℝ] Position d => A u) hh
  simpa only [Function.comp_def, Function.uncurry, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
    zero_apply] using hv.symm

/-- The derivative of the external force in the direction of the extra particle is the second
partial derivative of the kernel, particle by particle. -/
theorem force_fderiv_suffixEmbedding {b : Position d → Position d → Position d}
    (hb : BoundedSmoothKernel b) (z : Point (m*d+d)) (v : Point d) :
    fderiv ℝ (force b) z (suffixEmbedding (m*d) d v) =
      configurationEuclidean d m (fun i =>
        fderiv ℝ (b (positions z i)) (externalPosition z) (WithLp.ofLp v)) := by
  rw [(force_hasFDerivAt hb z).fderiv]
  simp only [forceDerivative, ContinuousLinearMap.comp_apply]
  apply congrArg (configurationEuclidean d m)
  funext i
  change fderiv ℝ (Function.uncurry b) (positions z i, externalPosition z)
    (positionMap i (suffixEmbedding (m*d) d v), externalMap (suffixEmbedding (m*d) d v)) = _
  have hp : positionMap i (suffixEmbedding (m*d) d v) = 0 := by
    simp [positionMap]
  have he : externalMap (suffixEmbedding (m*d) d v) = WithLp.ofLp v := by
    ext a
    simp [externalMap_apply, externalPosition]
  rw [hp, he, uncurry_fderiv_second hb]

variable {N : ℕ} {a : Position d → Position d} {K : Position d → Position d → Position d}
  {La L₁ L₂ M : ℝ}

/-- `|(K(xᵢ, y))ᵢ|² ≤ m M²` for the Euclidean norm. -/
theorem norm_sq_force_le (h : SplitKernel a K La L₁ L₂ M) (z : Point (m*d+d)) :
    ‖force K z‖ ^ 2 ≤ m * M ^ 2 := by
  rw [force, norm_sq_configurationEuclidean]
  calc ∑ i, ‖WithLp.toLp 2 (K (positions z i) (externalPosition z))‖ ^ 2
      ≤ ∑ _i : Fin m, M ^ 2 := Finset.sum_le_sum fun i _ =>
        pow_le_pow_left₀ (norm_nonneg _) (h.norm_toLp_K_le _ _) 2
    _ = m * M ^ 2 := by simp

/-! ### The cancellation bound (`eq:cancel`) -/

/-- The diagonal energy of the Hessian cancellation is a sum of Euclidean particle pairings. -/
theorem diagonalEnergy_eq_sum_inner (K : Position d → Position d → Position d)
    (z : Point (m*d+d)) (w : Point (m*d)) :
    diagonalEnergy K z w = ∑ i, ⟪WithLp.toLp 2 (fderiv ℝ (fun q => K q (externalPosition z))
      (positions z i) ((configurationEuclidean d m).symm w i)),
        WithLp.toLp 2 ((configurationEuclidean d m).symm w i)⟫_ℝ := by
  unfold diagonalEnergy
  apply Finset.sum_congr rfl
  intro i _
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

/-- `eq:cancel`: the diagonal term is at most `L₁ |w|²`, for the Euclidean constant `L₁` and
uniformly in the number of particles and the dimension. -/
theorem diagonalEnergy_le_sharp (h : SplitKernel a K La L₁ L₂ M) (z : Point (m*d+d))
    (w : Point (m*d)) : diagonalEnergy K z w ≤ L₁ * ‖w‖ ^ 2 := by
  set u := (configurationEuclidean d m).symm w
  have hw : w = configurationEuclidean d m u := by simp [u]
  rw [diagonalEnergy_eq_sum_inner, hw, norm_sq_configurationEuclidean, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  calc _ ≤ ‖WithLp.toLp 2 (fderiv ℝ (fun q => K q (externalPosition z)) (positions z i) (u i))‖ *
        ‖WithLp.toLp 2 (u i)‖ := real_inner_le_norm _ _
    _ ≤ (L₁ * ‖WithLp.toLp 2 (u i)‖) * ‖WithLp.toLp 2 (u i)‖ :=
        mul_le_mul_of_nonneg_right (h.norm_toLp_fderiv_first_le _ _ _) (norm_nonneg _)
    _ = _ := by ring

/-- The lifted Hessian cancellation (`eq:cancel`) with the sharp constant `2L₁`. -/
theorem lifted_hessian_cancellation_le_sharp (h : SplitKernel a K La L₁ L₂ M)
    {f : Point (m*d) → ℝ} (hf : ContDiff ℝ ∞ f) (z : Point (m*d+d)) :
    2 * ⟪prefixEmbedding (m*d) d (gradient f (prefixProjection (m*d) d z)),
      gradient (interaction K f) z⟫_ℝ -
      ⟪liftedForce K z, gradient (fun q => ‖gradient f (prefixProjection (m*d) d q)‖ ^ 2) z⟫_ℝ ≤
      2 * L₁ * ‖gradient f (prefixProjection (m*d) d z)‖ ^ 2 := by
  rw [lifted_hessian_cancellation h.smooth_K hf]
  nlinarith [diagonalEnergy_le_sharp h z (gradient f (prefixProjection (m*d) d z))]

/-! ### The gradient bound (`eq:Phi-grad`) -/

/-- If `t² ≤ c t` with `c ≥ 0` and `t ≥ 0`, then `t ≤ c`. -/
theorem le_of_sq_le_mul {t c : ℝ} (ht : 0 ≤ t) (hc : 0 ≤ c) (h : t ^ 2 ≤ c * t) : t ≤ c := by
  rcases ht.eq_or_lt with h0 | hpos
  · rw [← h0]; exact hc
  · nlinarith

/-- The `x`-block of `∇Φf`: `|∇_xΦf| ≤ L₁ |∇f| + |(K(xᵢ, y))ᵢ| ‖D∇f‖`. -/
theorem norm_prefix_gradient_interaction_le (h : SplitKernel a K La L₁ L₂ M)
    {f : Point (m*d) → ℝ} (hf : ContDiff ℝ ∞ f) (z : Point (m*d+d)) :
    ‖prefixProjection (m*d) d (gradient (interaction K f) z)‖ ≤
      L₁ * ‖gradient f (prefixProjection (m*d) d z)‖ +
        ‖force K z‖ * ‖fderiv ℝ (gradient f) (prefixProjection (m*d) d z)‖ := by
  set w := prefixProjection (m*d) d (gradient (interaction K f) z)
  set G := gradient f (prefixProjection (m*d) d z)
  set u := (configurationEuclidean d m).symm w
  have hw : ‖w‖ ^ 2 = fderiv ℝ (interaction K f) z (prefixEmbedding (m*d) d w) := by
    rw [← inner_gradient_left, real_inner_comm, inner_prefixEmbedding, real_inner_self_eq_norm_sq]
  rw [fderiv_interaction h.smooth_K hf, force_fderiv_prefixEmbedding h.smooth_K,
    prefixProjection_embedding] at hw
  -- the block-diagonal first-argument derivative has norm at most `L₁ |w|`
  have hD : ‖configurationEuclidean d m (fun i =>
      fderiv ℝ (fun q => K q (externalPosition z)) (positions z i) (u i))‖ ≤ L₁ * ‖w‖ := by
    have hw' : w = configurationEuclidean d m u := by simp [u]
    have hsq : ‖configurationEuclidean d m (fun i =>
        fderiv ℝ (fun q => K q (externalPosition z)) (positions z i) (u i))‖ ^ 2 ≤
        (L₁ * ‖w‖) ^ 2 := by
      rw [norm_sq_configurationEuclidean, mul_pow, hw', norm_sq_configurationEuclidean,
        Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (h.norm_toLp_fderiv_first_le _ _ _) 2
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg h.L₁_nonneg (norm_nonneg _))).1 hsq
  have h1 := (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hD (norm_nonneg G))
  have h2 : ⟪force K z, fderiv ℝ (gradient f) (prefixProjection (m*d) d z) w⟫_ℝ ≤
      ‖force K z‖ * (‖fderiv ℝ (gradient f) (prefixProjection (m*d) d z)‖ * ‖w‖) :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
      (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _))
  apply le_of_sq_le_mul (norm_nonneg _) (by have := h.L₁_nonneg; positivity)
  have : ‖w‖ ^ 2 ≤ L₁ * ‖w‖ * ‖G‖ +
      ‖force K z‖ * (‖fderiv ℝ (gradient f) (prefixProjection (m*d) d z)‖ * ‖w‖) := by
    rw [hw]; exact add_le_add h1 h2
  linarith

/-- The `y`-block of `∇Φf`: `|∇_yΦf|² ≤ m L₂² |∇f|²`. -/
theorem norm_sq_suffix_gradient_interaction_le (h : SplitKernel a K La L₁ L₂ M)
    {f : Point (m*d) → ℝ} (hf : ContDiff ℝ ∞ f) (z : Point (m*d+d)) :
    ‖suffixProjection (m*d) d (gradient (interaction K f) z)‖ ^ 2 ≤
      m * L₂ ^ 2 * ‖gradient f (prefixProjection (m*d) d z)‖ ^ 2 := by
  set s := suffixProjection (m*d) d (gradient (interaction K f) z)
  set G := gradient f (prefixProjection (m*d) d z)
  set Gc := (configurationEuclidean d m).symm G
  have hs : ‖s‖ ^ 2 = fderiv ℝ (interaction K f) z (suffixEmbedding (m*d) d s) := by
    rw [← inner_gradient_left, real_inner_comm, inner_suffixEmbedding, real_inner_self_eq_norm_sq]
  rw [fderiv_interaction h.smooth_K hf, force_fderiv_suffixEmbedding h.smooth_K,
    prefixProjection_suffixEmbedding, map_zero, inner_zero_right, add_zero] at hs
  have hG : G = configurationEuclidean d m Gc := by simp [Gc]
  rw [show gradient f (prefixProjection (m*d) d z) = configurationEuclidean d m Gc from hG,
    inner_configurationEuclidean] at hs
  set T := ∑ i, ‖WithLp.toLp 2 (Gc i)‖
  have hT : 0 ≤ T := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hle : ‖s‖ ^ 2 ≤ L₂ * T * ‖s‖ := by
    rw [hs, mul_comm L₂ T, mul_assoc, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    refine (real_inner_le_norm _ _).trans ?_
    have hb := h.norm_toLp_fderiv_second_le (positions z i) (externalPosition z) (WithLp.ofLp s)
    simp only [WithLp.toLp_ofLp] at hb
    calc _ ≤ (L₂ * ‖s‖) * ‖WithLp.toLp 2 (Gc i)‖ :=
          mul_le_mul_of_nonneg_right hb (norm_nonneg _)
      _ = _ := by ring
  have hst := le_of_sq_le_mul (norm_nonneg s) (mul_nonneg h.L₂_nonneg hT) (by linarith)
  have hT2 : T ^ 2 ≤ m * ‖G‖ ^ 2 := by rw [hG]; exact sq_sum_norm_le Gc
  calc ‖s‖ ^ 2 ≤ (L₂ * T) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hst 2
    _ = L₂ ^ 2 * T ^ 2 := by ring
    _ ≤ L₂ ^ 2 * (m * ‖G‖ ^ 2) := mul_le_mul_of_nonneg_left hT2 (sq_nonneg _)
    _ = _ := by ring

/-- `eq:Phi-grad`: `|∇_{(x,y)}Φf|² ≤ m G (|∇f|² + |D²f|²_HS)` with `G = 2L₁² + L₂² + 2M²`. -/
theorem interaction_gradient_norm_sq_le_sharp (h : SplitKernel a K La L₁ L₂ M) (hm : 1 ≤ m)
    {f : Point (m*d) → ℝ} (hf : ContDiff ℝ ∞ f) (z : Point (m*d+d)) :
    ‖gradient (interaction K f) z‖ ^ 2 ≤
      gConst L₁ L₂ M * m * (‖gradient f (prefixProjection (m*d) d z)‖ ^ 2 +
        HierarchyAlgebra.frobeniusSq (hessian f (prefixProjection (m*d) d z))) := by
  set G := gradient f (prefixProjection (m*d) d z)
  set Hs := HierarchyAlgebra.frobeniusSq (hessian f (prefixProjection (m*d) d z))
  set Hn := ‖fderiv ℝ (gradient f) (prefixProjection (m*d) d z)‖
  have hHn : Hn ^ 2 ≤ Hs := fderiv_gradient_norm_sq_le hf _
  have hHs : 0 ≤ Hs := HierarchyAlgebra.frobeniusSq_nonneg _
  have hF := norm_sq_force_le h z
  have hx := norm_prefix_gradient_interaction_le h hf z
  have hy := norm_sq_suffix_gradient_interaction_le h hf z
  have hsplit := prefix_suffix_norm_sq (m*d) d (gradient (interaction K f) z)
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  -- `|∇_xΦf|² ≤ 2 L₁² |∇f|² + 2 m M² |D²f|²`
  have hx2 : ‖prefixProjection (m*d) d (gradient (interaction K f) z)‖ ^ 2 ≤
      2 * L₁ ^ 2 * ‖G‖ ^ 2 + 2 * (m * M ^ 2) * Hs := by
    have h0 : 0 ≤ L₁ * ‖G‖ + ‖force K z‖ * Hn := by
      have := h.L₁_nonneg; positivity
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hx 2
    have hFH : (‖force K z‖ * Hn) ^ 2 ≤ (m * M ^ 2) * Hs := by
      rw [mul_pow]
      exact mul_le_mul hF hHn (sq_nonneg _) (by positivity)
    nlinarith [sq_nonneg (L₁ * ‖G‖ - ‖force K z‖ * Hn)]
  have hG2 : 0 ≤ ‖G‖ ^ 2 := sq_nonneg _
  unfold gConst
  nlinarith [mul_nonneg (sub_nonneg.2 hmR) (mul_nonneg (sq_nonneg L₁) hG2),
    mul_nonneg (mul_nonneg (Nat.cast_nonneg (α := ℝ) m) (add_nonneg (mul_nonneg zero_le_two
      (sq_nonneg L₁)) (sq_nonneg L₂))) hHs,
    mul_nonneg (mul_nonneg (Nat.cast_nonneg (α := ℝ) m) (sq_nonneg M)) hG2]

end SharpWasserstein.Sharp.Hierarchy
