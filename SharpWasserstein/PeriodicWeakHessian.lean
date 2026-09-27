import SharpWasserstein.PeriodicTestL2
import SharpWasserstein.WeakDerivativeLimit

/-! Construct actual weak `L²` Hessian entries of the periodic weighted
elliptic optimizer. Uniform Galerkin bounds and strong convergence supply the
weak derivatives; none are assumed for the limiting optimizer. -/

noncomputable section
namespace SharpWasserstein.PeriodicWeakHessian
open MeasureTheory Filter PeriodicIntegrationByParts PeriodicFourierTests PeriodicBochner
open PeriodicGalerkin PeriodicGradientClosure PeriodicSmoothGradient PeriodicHessianBounds
open PeriodicTestL2 WeightedTangent
open scoped ENNReal Topology BigOperators ContDiff InnerProductSpace BoundedContinuousFunction

variable {n : ℕ} [MeasurableSpace (Point n)] [BorelSpace (Point n)]

/-- Data-dependent bound for the genuine Galerkin Hessian square. -/
def regularityBound (ℓ : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)
    (σ : Coordinates n → ℝ) (a B : ℝ) : ℝ :=
  ((B + 1) * (‖ℓ‖ / a) ^ 2 + (∫ x, gradientSquare σ x ∂cube n)) / (2 * a)

theorem regularityBound_nonneg (ℓ : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)
    (σ : Coordinates n → ℝ) {a B : ℝ} (ha : 0 < a) (hB : 0 ≤ B) :
    0 ≤ regularityBound ℓ σ a B := by
  have hσ : 0 ≤ ∫ x, gradientSquare σ x ∂cube n := integral_nonneg (gradientSquare_nonneg σ)
  unfold regularityBound
  positivity

/-- Every Hessian entry of the actual closed-space optimizer exists in `L²`.
The hypotheses are positivity/smoothness of the density and the actual smooth
source pairing. The optimizer's weak second derivatives are conclusions. -/
theorem exists_optimizer_hessianEntry (ρ : Point n →ᵇ ℝ)
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
      ‖H‖ ≤ Real.sqrt (regularityBound ℓ σ a B) ∧
      ∀ φ : SmoothPeriodicTest n, ⟪H, value φ⟫_ℝ =
        -⟪component j ((optimizer ρ ℓ : gradientClosure (cubePoint (n := n))) :
            Lp (Point n) 2 (cubePoint (n := n))), derivative i φ⟫_ℝ := by
  let u := fun s => component j (vector ρ ℓ s : Lp (Point n) 2 (cubePoint (n := n)))
  let v := fun s => component i (hessianColumn (potential ρ ℓ s).val
    (frequencySpace_properties s (potential ρ ℓ s).property).1 j)
  have hvec := (gradientClosure (cubePoint (n := n))).subtypeL.continuous.continuousAt.tendsto.comp
    (vector_tendsto ρ ℓ ha (Filter.Eventually.of_forall hp))
  have hu : Tendsto u atTop (𝓝 (component j ((optimizer ρ ℓ : gradientClosure (cubePoint (n := n))) :
      Lp (Point n) 2 (cubePoint (n := n))))) :=
    (component j).continuous.continuousAt.tendsto.comp hvec
  have hC := regularityBound_nonneg ℓ σ ha hB
  apply WeakDerivativeLimit.exists_weakDerivative_of_strong_limit value (derivative i) hu v
    (Real.sqrt_nonneg _) (Filter.Eventually.of_forall fun s => ?_) (fun φ => ?_)
  · have hbound := potential_hessianColumn_norm_sq_le ρ ℓ s ha hB hp hρ hpρ hΔρ hσ hpσ
      (hsource s) j
    change _ ≤ regularityBound ℓ σ a B at hbound
    have hc := component_norm_le i (hessianColumn (potential ρ ℓ s).val
      (frequencySpace_properties s (potential ρ ℓ s).property).1 j)
    change ‖v s‖ ≤ _ at hc
    have hsq := Real.sq_sqrt hC
    have hn := norm_nonneg (hessianColumn (potential ρ ℓ s).val
      (frequencySpace_properties s (potential ρ ℓ s).property).1 j)
    nlinarith [Real.sqrt_nonneg (regularityBound ℓ σ a B)]
  · apply Filter.Eventually.of_forall
    intro s
    have hf := frequencySpace_properties s (potential ρ ℓ s).property
    have he := hessian_component_weak_equation (potential ρ ℓ s).val hf.1 hf.2.1 i j φ
    have hg : gradientVector (potential ρ ℓ s).val hf.1 = vector ρ ℓ s := gradient_potential ρ ℓ s
    rw [hg] at he
    exact he

/-- Integral form: the optimizer's actual `j`-th coordinate has an actual
square-integrable weak derivative in direction `i`, tested against every
smooth periodic function. -/
theorem exists_optimizer_hessianEntry_integral (ρ : Point n →ᵇ ℝ)
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
      ‖H‖ ≤ Real.sqrt (regularityBound ℓ σ a B) ∧ ∀ φ : SmoothPeriodicTest n,
      (∫ x, H ((coordinateEquiv n).symm x) * φ.val x ∂cube n) =
        -(∫ x, (((optimizer ρ ℓ : gradientClosure (cubePoint (n := n))) :
            Lp (Point n) 2 (cubePoint (n := n))) ((coordinateEquiv n).symm x)) j *
          coordinatePartial φ.val i x ∂cube n) := by
  obtain ⟨H, hH, he⟩ := exists_optimizer_hessianEntry ρ ℓ ha hB hp hρ hpρ hΔρ hσ hpσ hsource i j
  refine ⟨H, hH, fun φ => ?_⟩
  have h := he φ
  change ⟪H, value φ⟫_ℝ =
    -⟪component j ((optimizer ρ ℓ : gradientClosure (cubePoint (n := n))) :
      Lp (Point n) 2 (cubePoint (n := n))), value (partialTest φ i)⟫_ℝ at h
  rw [inner_value, inner_component_value] at h
  exact h

end SharpWasserstein.PeriodicWeakHessian
