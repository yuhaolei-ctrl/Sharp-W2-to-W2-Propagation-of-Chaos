import SharpWasserstein.PeriodicHessianConvergence
import SharpWasserstein.PeriodicL2Multiplier
import Mathlib.Topology.Order.LiminfLimsup

/-! Weighted lower semicontinuity for the genuine full Galerkin Hessian.
The limiting entries and their weak derivative equations are constructed from
actual gradient convergence; positivity retains every matrix entry's dissipation. -/
noncomputable section
namespace SharpWasserstein.PeriodicHessianDissipation
open MeasureTheory Filter Set PeriodicIntegrationByParts PeriodicFourierTests PeriodicBochner
open PeriodicGalerkin PeriodicGradientClosure PeriodicSmoothGradient PeriodicHessianBounds
open PeriodicTestL2 PeriodicWeakHessian PeriodicHessianConvergence WeightedTangent
open scoped ENNReal Topology BigOperators ContDiff InnerProductSpace BoundedContinuousFunction
variable {n : ℕ} [MeasurableSpace (Point n)] [BorelSpace (Point n)]

theorem inner_multiplier (q : Point n →ᵇ ℝ) (u v : Lp ℝ 2 (cubePoint (n := n))) :
    ⟪u,PeriodicL2Multiplier.operator q v⟫_ℝ = ∫ y,q y*u y*v y ∂cubePoint := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [PeriodicL2Multiplier.operator_ae q v] with y hy
  rw [hy]
  simp only [RCLike.inner_apply,conj_trivial]
  ring

theorem weighted_product_integrable (q : Point n →ᵇ ℝ) (u v : Lp ℝ 2 (cubePoint (n := n))) :
    Integrable (fun y => q y*u y*v y) cubePoint := by
  apply (L2.integrable_inner (𝕜 := ℝ) u (PeriodicL2Multiplier.operator q v)).congr
  filter_upwards [PeriodicL2Multiplier.operator_ae q v] with y hy
  rw [hy]
  simp only [RCLike.inner_apply,conj_trivial]
  ring

theorem inner_multiplier_self (q : Point n →ᵇ ℝ) (u : Lp ℝ 2 (cubePoint (n := n))) :
    ⟪u,PeriodicL2Multiplier.operator q u⟫_ℝ = ∫ y,q y*(u y)^2 ∂cubePoint := by
  rw [inner_multiplier]
  congr 1
  funext y
  ring

theorem inner_multiplier_symmetric (q : Point n →ᵇ ℝ) (u v : Lp ℝ 2 (cubePoint (n := n))) :
    ⟪u,PeriodicL2Multiplier.operator q v⟫_ℝ = ⟪v,PeriodicL2Multiplier.operator q u⟫_ℝ := by
  rw [inner_multiplier,inner_multiplier]
  congr 1
  funext y
  ring

theorem weighted_square_nonneg (q : Point n →ᵇ ℝ) (hq : ∀ y,0 ≤ q y)
    (u : Lp ℝ 2 (cubePoint (n := n))) : 0 ≤ ⟪u,PeriodicL2Multiplier.operator q u⟫_ℝ := by
  rw [inner_multiplier_self]
  exact integral_nonneg fun y => mul_nonneg (hq y) (sq_nonneg _)

/-- Positivity of the actual weighted squared difference gives the affine
lower bound used to retain the Hessian in the weak limit. -/
theorem weighted_square_support (q : Point n →ᵇ ℝ) (hq : ∀ y,0 ≤ q y)
    (u v : Lp ℝ 2 (cubePoint (n := n))) :
    2*⟪u,PeriodicL2Multiplier.operator q v⟫_ℝ-⟪v,PeriodicL2Multiplier.operator q v⟫_ℝ ≤
      ⟪u,PeriodicL2Multiplier.operator q u⟫_ℝ := by
  have hh := weighted_square_nonneg q hq (u-v)
  rw [map_sub,inner_sub_left,inner_sub_right,inner_sub_right,
    inner_multiplier_symmetric q v u] at hh
  linarith

/-- The weighted energy of an actual approximating Hessian entry is its
literal coordinate second-derivative integral. -/
theorem weighted_hessianEntry (q : Point n →ᵇ ℝ) (f : Coordinates n → ℝ)
    (hf : ContDiff ℝ ∞ f) (i j : Fin n) :
    ⟪component i (hessianColumn f hf j),
      PeriodicL2Multiplier.operator q (component i (hessianColumn f hf j))⟫_ℝ =
      ∫ x,q ((coordinateEquiv n).symm x)*(coordinatePartial (coordinatePartial f j) i x)^2 ∂cube n := by
  rw [inner_multiplier_self]
  calc
    _ = ∫ y,q y*(gradient (PDEPairings.directionTest (compactTest f hf)
          (EuclideanSpace.single j 1) : Point n → ℝ) y i)^2 ∂cubePoint := by
      apply integral_congr_ae
      filter_upwards [component_ae i (hessianColumn f hf j),
        testGradient_ae (cubePoint (n := n))
          (PDEPairings.directionTest (compactTest f hf) (EuclideanSpace.single j 1))] with y ha hb
      rw [ha]
      change q y*(testGradient cubePoint
        (PDEPairings.directionTest (compactTest f hf) (EuclideanSpace.single j 1)) y i)^2 = _
      rw [hb]
    _ = _ := by
      rw [integral_cubePoint]
      apply integral_congr_ae
      filter_upwards [cube_ae_mem n] with x hx
      rw [directionGradient_on_cube f hf j hx,← PDEPairings.directionDeriv_eq_gradient_component,
        directionDeriv_pullback,ContinuousLinearEquiv.apply_symm_apply]

/-- Summing every weighted entry gives the genuine full Hessian square,
with no diagonal-only relaxation or dimension loss. -/
theorem weighted_hessianMatrix (q : Point n →ᵇ ℝ) (f : Coordinates n → ℝ)
    (hf : ContDiff ℝ ∞ f) :
    (∑ i : Fin n,∑ j : Fin n,⟪component i (hessianColumn f hf j),
      PeriodicL2Multiplier.operator q (component i (hessianColumn f hf j))⟫_ℝ) =
      ∫ x,q ((coordinateEquiv n).symm x)*hessianSquare f x ∂cube n := by
  simp_rw [weighted_hessianEntry]
  have hi (i j : Fin n) : Integrable (fun x => q ((coordinateEquiv n).symm x)*
      (coordinatePartial (coordinatePartial f j) i x)^2) (cube n) :=
    continuous_integrable_cube ((q.continuous.comp (coordinateEquiv n).symm.continuous).mul
      ((smooth_coordinatePartial (smooth_coordinatePartial hf j) i).continuous.pow 2))
  simp only [hessianSquare,Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  exact (integral_finsetSum _ (fun j _ => hi i j)).symm

/-- The full weighted Galerkin Hessian has an actual uniform bound; this
also excludes an infinite-real `liminf` pathology. -/
theorem weighted_potential_hessian_bound (ρ : Point n →ᵇ ℝ)
    (ℓ : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)
    (s : Finset ((Fin n → ℤ) × Bool)) {σ : Coordinates n → ℝ} {a B : ℝ}
    (ha : 0 < a) (hB : 0 ≤ B) (hp : ∀ y, a ≤ ρ y)
    (hρ : ContDiff ℝ 2 (fun x => ρ ((coordinateEquiv n).symm x)))
    (hpρ : Periodic (fun x => ρ ((coordinateEquiv n).symm x)))
    (hΔρ : ∀ᵐ x ∂cube n, PeriodicIntegrationByParts.laplacian (fun x => ρ ((coordinateEquiv n).symm x)) x ≤ B)
    (hσ : ContDiff ℝ 1 σ) (hpσ : Periodic σ)
    (hsource : ∀ ψ : frequencySpace s,
      ℓ (trialGradient s ψ) = ∫ x, σ x * ψ.val x ∂cube n) :
    (∫ x,ρ ((coordinateEquiv n).symm x)*hessianSquare (potential ρ ℓ s).val x ∂cube n) ≤
      ‖ρ‖ * regularityBound ℓ σ a B := by
  have hf := (frequencySpace_properties s (potential ρ ℓ s).property).1
  have hH := (smooth_hessianSquare hf).continuous
  calc
    _ ≤ ∫ x,‖ρ‖*hessianSquare (potential ρ ℓ s).val x ∂cube n := by
      apply integral_mono
        (continuous_integrable_cube ((ρ.continuous.comp (coordinateEquiv n).symm.continuous).mul hH))
        (continuous_integrable_cube (continuous_const.mul hH))
      intro x
      exact mul_le_mul_of_nonneg_right
        ((le_abs_self _).trans (ρ.norm_coe_le_norm _)) (hessianSquare_nonneg _ x)
    _ = ‖ρ‖ * ∫ x,hessianSquare (potential ρ ℓ s).val x ∂cube n := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (potential_hessian_bound_uniform ρ ℓ s ha hB hp hρ hpρ hΔρ hσ hpσ hsource) (norm_nonneg _)

/-- Every entry of the actual optimizer has a weak derivative, and the full
weighted squared Hessian is lower semicontinuous along its Galerkin potentials.
No weak Hessian, derivative equation, or lower-semicontinuity conclusion is assumed. -/
theorem exists_optimizer_hessian_weighted_liminf (ρ : Point n →ᵇ ℝ)
    (ℓ : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)
    {σ : Coordinates n → ℝ} {a B : ℝ}
    (ha : 0 < a) (hB : 0 ≤ B) (hp : ∀ y, a ≤ ρ y)
    (hρ : ContDiff ℝ ∞ (fun x => ρ ((coordinateEquiv n).symm x)))
    (hpρ : Periodic (fun x => ρ ((coordinateEquiv n).symm x)))
    (hΔρ : ∀ᵐ x ∂cube n, PeriodicIntegrationByParts.laplacian (fun x => ρ ((coordinateEquiv n).symm x)) x ≤ B)
    (hσ : ContDiff ℝ 1 σ) (hpσ : Periodic σ)
    (hsource : ∀ (s : Finset ((Fin n → ℤ) × Bool)) (ψ : frequencySpace s),
      ℓ (trialGradient s ψ) = ∫ x, σ x * ψ.val x ∂cube n) :
    ∃ H : Fin n → Fin n → Lp ℝ 2 (cubePoint (n := n)),
      (∀ i j, H i j ∈ WeakDerivativeLimit.testClosure value) ∧
      (∀ i j, ‖H i j‖ ≤ Real.sqrt (regularityBound ℓ σ a B)) ∧
      (∀ i j (φ : SmoothPeriodicTest n),
        (∫ x,H i j ((coordinateEquiv n).symm x)*φ.val x ∂cube n) =
        -(∫ x,(((optimizer ρ ℓ : gradientClosure (cubePoint (n := n))) :
          Lp (Point n) 2 (cubePoint (n := n))) ((coordinateEquiv n).symm x)) j *
          coordinatePartial φ.val i x ∂cube n)) ∧
      (∀ i j,∀ z ∈ WeakDerivativeLimit.testClosure value,
        Tendsto (fun s => ⟪approximateHessian ρ ℓ i j s,z⟫_ℝ) atTop (𝓝 ⟪H i j,z⟫_ℝ)) ∧
      (∑ i : Fin n,∑ j : Fin n,∫ y,ρ y*(H i j y)^2 ∂cubePoint) ≤
        liminf (fun s : Finset ((Fin n → ℤ) × Bool) =>
          ∫ x,ρ ((coordinateEquiv n).symm x)*hessianSquare (potential ρ ℓ s).val x ∂cube n) atTop := by
  have hρ2 : ContDiff ℝ 2 (fun x => ρ ((coordinateEquiv n).symm x)) :=
    hρ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  choose H hm hn he hc using fun i j =>
    exists_optimizer_hessianEntry_converges ρ ℓ ha hB hp hρ2 hpρ hΔρ hσ hpσ hsource i j
  refine ⟨H, hm, hn, ?_, hc, ?_⟩
  · intro i j φ
    have hh := he i j φ
    change ⟪H i j,value φ⟫_ℝ = -⟪component j
      ((optimizer ρ ℓ : gradientClosure (cubePoint (n := n))) : Lp (Point n) 2 (cubePoint (n := n))),
      value (partialTest φ i)⟫_ℝ at hh
    rw [inner_value,inner_component_value] at hh
    exact hh
  · let E : ℝ := ∑ i : Fin n,∑ j : Fin n,
      ⟪H i j,PeriodicL2Multiplier.operator ρ (H i j)⟫_ℝ
    let A := fun s : Finset ((Fin n → ℤ) × Bool) =>
      ∫ x,ρ ((coordinateEquiv n).symm x)*hessianSquare (potential ρ ℓ s).val x ∂cube n
    let G := fun s : Finset ((Fin n → ℤ) × Bool) =>
      ∑ i : Fin n,∑ j : Fin n,
        (2*⟪approximateHessian ρ ℓ i j s,PeriodicL2Multiplier.operator ρ (H i j)⟫_ℝ -
          ⟪H i j,PeriodicL2Multiplier.operator ρ (H i j)⟫_ℝ)
    have hconv : Tendsto G atTop (𝓝 E) := by
      have ht := tendsto_finsetSum Finset.univ (fun i _ =>
        tendsto_finsetSum Finset.univ (fun j _ =>
          ((hc i j (PeriodicL2Multiplier.operator ρ (H i j))
            (PeriodicL2Multiplier.operator_mem_testClosure ρ hρ hpρ (hm i j))).const_mul 2).sub
            (tendsto_const_nhds (x := ⟪H i j,PeriodicL2Multiplier.operator ρ (H i j)⟫_ℝ))))
      simpa only [G,E,two_mul,add_sub_cancel_right] using ht
    have hGA (s) : G s ≤ A s := by
      have hh := Finset.sum_le_sum (s := Finset.univ) (fun (i : Fin n) _ =>
        Finset.sum_le_sum (s := Finset.univ) (fun (j : Fin n) _ =>
          weighted_square_support ρ (fun y => ha.le.trans (hp y))
            (approximateHessian ρ ℓ i j s) (H i j)))
      change G s ≤ ∑ i : Fin n,∑ j : Fin n,
        ⟪component i (hessianColumn (potential ρ ℓ s).val
          (frequencySpace_properties s (potential ρ ℓ s).property).1 j),
        PeriodicL2Multiplier.operator ρ (component i (hessianColumn (potential ρ ℓ s).val
          (frequencySpace_properties s (potential ρ ℓ s).property).1 j))⟫_ℝ at hh
      rw [weighted_hessianMatrix] at hh
      exact hh
    have hupper (s) : A s ≤ ‖ρ‖ * regularityBound ℓ σ a B :=
      weighted_potential_hessian_bound ρ ℓ s ha hB hp hρ2 hpρ hΔρ hσ hpσ (hsource s)
    have hlim : E ≤ liminf A atTop := by
      rw [← hconv.liminf_eq]
      exact liminf_le_liminf (Eventually.of_forall hGA) hconv.isBoundedUnder_ge
        (isCoboundedUnder_ge_of_le atTop hupper)
    simpa only [E,inner_multiplier_self] using hlim

end SharpWasserstein.PeriodicHessianDissipation
