import SharpWasserstein.PeriodicSmoothGradient

/-! A periodic optimizer depends only on the source action on the actual
periodic gradient space. Equality on smooth periodic gradients is sufficient,
by the proved Fourier closure and the genuine coercive weak equation. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology InnerProductSpace ContDiff BoundedContinuousFunction
namespace SharpWasserstein.PeriodicGradientClosure
open WeightedTangent WeightedDensity PeriodicBochner PeriodicGalerkin PeriodicSmoothGradient
open PeriodicIntegrationByParts
variable {n : ℕ} [MeasurableSpace (Point n)] [BorelSpace (Point n)]

theorem functional_eq_on_periodicSpace_of_smooth
    (ℓ ℓ' : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)
    (h : ∀ (f : Coordinates n → ℝ) (hf : ContDiff ℝ ∞ f), Periodic f →
      ℓ (gradientVector f hf) = ℓ' (gradientVector f hf))
    (w : periodicSpace (n := n)) : ℓ w = ℓ' w := by
  have hs : periodicSpace (n := n) ≤ (periodicGradientMap (n := n)).range.topologicalClosure :=
    le_of_eq periodicSpace_eq_smoothGradientClosure
  have hw := hs w.property
  rw [← SetLike.mem_coe,Submodule.topologicalClosure_coe] at hw
  apply closure_minimal (s := ((periodicGradientMap (n := n)).range : Set _))
    (t := {v | ℓ v = ℓ' v}) ?_ (isClosed_eq ℓ.continuous ℓ'.continuous) hw
  rintro v ⟨f,rfl⟩
  exact h f.val f.property.1 f.property.2

theorem optimizer_eq_of_functional_eq_on_periodicSpace
    (ρ : Point n →ᵇ ℝ) (ℓ ℓ' : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)
    {a : ℝ} (ha : 0 < a) (hp : ∀ᵐ y ∂cubePoint, a ≤ ρ y)
    (h : ∀ w : periodicSpace (n := n), ℓ w = ℓ' w) : optimizer ρ ℓ = optimizer ρ ℓ' := by
  let u := optimizer ρ ℓ
  let v := optimizer ρ ℓ'
  have hu := optimizer_equation ρ ℓ ha hp (u-v)
  have hv := optimizer_equation ρ ℓ' ha hp (u-v)
  have hz : ⟪weightedOperator cubePoint ρ (u.val-v.val),
      u.val-v.val⟫_ℝ = 0 := by
    rw [map_sub,inner_sub_left]
    exact sub_eq_zero.mpr (hu.trans ((h (u-v)).trans hv.symm))
  have hb := WeightedGalerkin.weightedOperator_lower_bound cubePoint ρ hp
    (u.val-v.val)
  rw [hz] at hb
  have hn : ‖u.val-v.val‖ = 0 := by
    apply sq_eq_zero_iff.mp
    exact le_antisymm ((mul_le_mul_iff_right₀ ha).mp (by simpa only [mul_zero] using hb)) (sq_nonneg _)
  apply Subtype.ext
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

theorem optimizer_energy_eq_of_functional_eq_on_periodicSpace
    (ρ : Point n →ᵇ ℝ) (ℓ ℓ' : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)
    {a : ℝ} (ha : 0 < a) (hp : ∀ᵐ y ∂cubePoint, a ≤ ρ y)
    (h : ∀ w : periodicSpace (n := n), ℓ w = ℓ' w) :
    ℓ (optimizer ρ ℓ) = ℓ' (optimizer ρ ℓ') := by
  rw [optimizer_eq_of_functional_eq_on_periodicSpace ρ ℓ ℓ' ha hp h]
  exact h _

end SharpWasserstein.PeriodicGradientClosure
