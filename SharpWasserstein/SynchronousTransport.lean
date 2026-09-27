import SharpWasserstein.SynchronousStability
import SharpWasserstein.RandomMapTransport
import SharpWasserstein.EuclideanDrift

/-! Synchronous Wasserstein stability derived from genuine coordinatewise
additive integral equations. The coefficient is independent of the number of
particles; the spatial-dimension factor only converts the ambient coordinate
sup norm to the manuscript's unnormalized Euclidean quadratic cost. -/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace SharpWasserstein

variable {d N : ℕ} {Ω : Type*}

/-- Coordinatewise common forcing yields an actual product-cost estimate. -/
theorem decoupledTrajectory_productCost_le
    {v : ℝ → Position d → Position d} {K : ℝ≥0}
    (hv : ∀ t, 0 ≤ t → LipschitzWith K (v t))
    (F : ℝ → Configuration d N × Ω → Configuration d N)
    (w : Ω → Fin N → ℝ → Position d)
    (hF : ∀ x ω i, AdditiveTrajectory v (w ω i) (x i) (fun s => F s (x, ω) i))
    {t : ℝ} (ht : 0 ≤ t) (x y : Configuration d N) (ω : Ω) :
    productCost (F t (x, ω)) (F t (y, ω)) ≤
      (d * Real.exp ((K : ℝ) * t) ^ 2) * productCost x y := by
  rw [productCost_eq_sum_positionSq, productCost_eq_sum_positionSq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h := additiveTrajectory_stability hv (hF x ω i) (hF y ω i) ht
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 h
  calc
    positionSq (F t (x, ω) i - F t (y, ω) i) ≤
        d * ‖F t (x, ω) i - F t (y, ω) i‖ ^ 2 := positionSq_le_norm_sq _
    _ ≤ d * (‖x i - y i‖ * Real.exp ((K : ℝ) * t)) ^ 2 :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = (d * Real.exp ((K : ℝ) * t) ^ 2) * ‖x i - y i‖ ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (norm_sq_le_positionSq _) (by positivity)

/-- The true Wasserstein estimate follows from synchronous coupling, without
assuming any Wasserstein contraction as an input. -/
theorem wassersteinSq_decoupledTrajectory_le
    [MeasurableSpace Ω]
    {v : ℝ → Position d → Position d} {K : ℝ≥0}
    (hv : ∀ t, 0 ≤ t → LipschitzWith K (v t))
    (F : ℝ → Configuration d N × Ω → Configuration d N)
    (w : Ω → Fin N → ℝ → Position d)
    (htrajectory : ∀ x ω i,
      AdditiveTrajectory v (w ω i) (x i) (fun s => F s (x, ω) i))
    (ξ : Measure Ω) [IsProbabilityMeasure ξ]
    (μ ν : Measure (Configuration d N)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {t : ℝ} (ht : 0 ≤ t) (hF : Measurable (F t)) :
    wassersteinSq (randomMapLaw (F t) μ ξ) (randomMapLaw (F t) ν ξ) ≤
      ENNReal.ofReal (d * Real.exp ((K : ℝ) * t) ^ 2) * wassersteinSq μ ν := by
  exact wassersteinSq_randomMapLaw_le (F t) hF ξ μ ν (by positivity)
    (decoupledTrajectory_productCost_le hv F w htrajectory ht)

/-- Specialization to the actual mean-field nonlinear drift. Probability of
`ρ t` and bounded kernel derivatives provide the required Lipschitz bound. -/
theorem wassersteinSq_nonlinearTrajectory_le
    [MeasurableSpace Ω]
    {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
    (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
    (hL₁ : 0 ≤ L₁) (ρ : ℝ → Measure (Position d))
    (hρ : ∀ t, IsProbabilityMeasure (ρ t))
    (F : ℝ → Configuration d N × Ω → Configuration d N)
    (w : Ω → Fin N → ℝ → Position d)
    (htrajectory : ∀ x ω i,
      AdditiveTrajectory (fun s => nonlinearDrift b (ρ s)) (w ω i) (x i)
        (fun s => F s (x, ω) i))
    (ξ : Measure Ω) [IsProbabilityMeasure ξ]
    (μ ν : Measure (Configuration d N)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {t : ℝ} (ht : 0 ≤ t) (hF : Measurable (F t)) :
    wassersteinSq (randomMapLaw (F t) μ ξ) (randomMapLaw (F t) ν ξ) ≤
      ENNReal.ofReal (d * Real.exp (L₁ * t) ^ 2) * wassersteinSq μ ν := by
  have hv : ∀ s, 0 ≤ s → LipschitzWith ⟨L₁, hL₁⟩ (nonlinearDrift b (ρ s)) := by
    intro s _
    letI := hρ s
    exact nonlinearDrift_lipschitz hb hbound hL₁ (ρ s)
  exact wassersteinSq_decoupledTrajectory_le hv F w htrajectory ξ μ ν ht hF

end SharpWasserstein
