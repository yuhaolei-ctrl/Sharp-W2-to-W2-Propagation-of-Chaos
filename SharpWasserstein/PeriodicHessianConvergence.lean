import SharpWasserstein.PeriodicWeakHessian
import SharpWasserstein.WeakDerivativeClosure

/-! Weak convergence of the actual Galerkin Hessian entries, derived from
the genuine strong gradient limit and periodic integration by parts. Pairing
convergence extends to the closure of the actual scalar tests, allowing later
products with the Sobolev optimizer. -/

noncomputable section
namespace SharpWasserstein.PeriodicHessianConvergence
open MeasureTheory Filter PeriodicIntegrationByParts PeriodicFourierTests PeriodicBochner
open PeriodicGalerkin PeriodicGradientClosure PeriodicSmoothGradient PeriodicHessianBounds
open PeriodicTestL2 PeriodicWeakHessian WeightedTangent
open scoped ENNReal Topology BigOperators ContDiff InnerProductSpace BoundedContinuousFunction

variable {n : ℕ} [MeasurableSpace (Point n)] [BorelSpace (Point n)]

/-- Actual `L²` Galerkin approximation of one Hessian entry. -/
def approximateHessian (ρ : Point n →ᵇ ℝ)
    (ℓ : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ) (i j : Fin n)
    (s : Finset ((Fin n → ℤ) × Bool)) : Lp ℝ 2 (cubePoint (n := n)) :=
  component i (hessianColumn (potential ρ ℓ s).val
    (frequencySpace_properties s (potential ρ ℓ s).property).1 j)

/-- The constructed weak Hessian can be chosen in the actual closed scalar
periodic test space, and all Galerkin pairings converge to it there. -/
theorem exists_optimizer_hessianEntry_converges (ρ : Point n →ᵇ ℝ)
    (ℓ : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)
    {σ : Coordinates n → ℝ} {a B : ℝ}
    (ha : 0 < a) (hB : 0 ≤ B) (hp : ∀ y, a ≤ ρ y)
    (hρ : ContDiff ℝ 2 (fun x => ρ ((coordinateEquiv n).symm x)))
    (hpρ : Periodic (fun x => ρ ((coordinateEquiv n).symm x)))
    (hΔρ : ∀ᵐ x ∂cube n,
      PeriodicIntegrationByParts.laplacian (fun x => ρ ((coordinateEquiv n).symm x)) x ≤ B)
    (hσ : ContDiff ℝ 1 σ) (hpσ : Periodic σ)
    (hsource : ∀ (s : Finset ((Fin n → ℤ) × Bool)) (ψ : frequencySpace s),
      ℓ (trialGradient s ψ) = ∫ x, σ x * ψ.val x ∂cube n) (i j : Fin n) :
    ∃ H : Lp ℝ 2 (cubePoint (n := n)),
      H ∈ WeakDerivativeLimit.testClosure value ∧
      ‖H‖ ≤ Real.sqrt (regularityBound ℓ σ a B) ∧
      (∀ φ : SmoothPeriodicTest n, ⟪H, value φ⟫_ℝ =
        -⟪component j ((optimizer ρ ℓ : gradientClosure (cubePoint (n := n))) :
            Lp (Point n) 2 (cubePoint (n := n))), derivative i φ⟫_ℝ) ∧
      ∀ z ∈ WeakDerivativeLimit.testClosure value,
        Tendsto (fun s => ⟪approximateHessian ρ ℓ i j s, z⟫_ℝ) atTop (𝓝 ⟪H, z⟫_ℝ) := by
  obtain ⟨H₀, hH₀, he₀⟩ := exists_optimizer_hessianEntry ρ ℓ ha hB hp hρ hpρ hΔρ hσ hpσ hsource i j
  obtain ⟨H, hHmem, hHnorm, hHeq⟩ := WeakDerivativeClosure.exists_representative_in_testClosure value H₀
  have he : ∀ φ : SmoothPeriodicTest n, ⟪H, value φ⟫_ℝ =
      -⟪component j ((optimizer ρ ℓ : gradientClosure (cubePoint (n := n))) :
        Lp (Point n) 2 (cubePoint (n := n))), derivative i φ⟫_ℝ :=
    fun φ => (hHeq φ).trans (he₀ φ)
  refine ⟨H, hHmem, hHnorm.trans hH₀, he, fun z hz => ?_⟩
  have hC := regularityBound_nonneg ℓ σ ha hB
  have hv : ∀ s, ‖approximateHessian ρ ℓ i j s‖ ≤ Real.sqrt (regularityBound ℓ σ a B) := by
    intro s
    have hbound := potential_hessianColumn_norm_sq_le ρ ℓ s ha hB hp hρ hpρ hΔρ hσ hpσ
      (hsource s) j
    change _ ≤ regularityBound ℓ σ a B at hbound
    have hc := component_norm_le i (hessianColumn (potential ρ ℓ s).val
      (frequencySpace_properties s (potential ρ ℓ s).property).1 j)
    change ‖approximateHessian ρ ℓ i j s‖ ≤ _ at hc
    nlinarith [Real.sq_sqrt hC, Real.sqrt_nonneg (regularityBound ℓ σ a B),
      norm_nonneg (hessianColumn (potential ρ ℓ s).val
        (frequencySpace_properties s (potential ρ ℓ s).property).1 j)]
  apply WeakDerivativeClosure.inner_tendsto_of_tests value (Real.sqrt_nonneg _)
    (Filter.Eventually.of_forall hv) _ z hz
  intro φ
  have hvec := (gradientClosure (cubePoint (n := n))).subtypeL.continuous.continuousAt.tendsto.comp
    (vector_tendsto ρ ℓ ha (Filter.Eventually.of_forall hp))
  have hu := (component j).continuous.continuousAt.tendsto.comp hvec
  have ht := (hu.inner (𝕜 := ℝ) (tendsto_const_nhds (x := derivative i φ))).neg
  rw [he φ]
  apply ht.congr'
  apply Filter.Eventually.of_forall
  intro s
  have hf := frequencySpace_properties s (potential ρ ℓ s).property
  have heq := hessian_component_weak_equation (potential ρ ℓ s).val hf.1 hf.2.1 i j φ
  have hg : gradientVector (potential ρ ℓ s).val hf.1 = vector ρ ℓ s := gradient_potential ρ ℓ s
  rw [hg] at heq
  exact heq.symm

end SharpWasserstein.PeriodicHessianConvergence
