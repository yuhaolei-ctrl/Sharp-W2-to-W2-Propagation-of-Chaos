module

public import SharpWasserstein.Compat
public import SharpWasserstein.PeriodicEnergyExhaustion
public import SharpWasserstein.KernelPeriodMultiples

@[expose] public section

/-! Exact passage from all admissible test periods of one fixed periodic
kernel to the full Euclidean compact-test energy, with no change of law or
source and no change in the bound. -/
noncomputable section
open Set MeasureTheory
namespace SharpWasserstein.BrownianEnergyPeriodization
open WeightedTangent

/-- All positive integer multiples of a fixed physical kernel period suffice
for full Euclidean source energy. This only supplies the exhaustion interface;
the actual propagated bounds are proved by the Brownian hierarchy. -/
theorem full_energy_le_of_kernel_periods {d n : ℕ}
    [MeasurableSpace (Point n)] [BorelSpace (Point n)]
    {b : Position d → Position d → Position d} {P : ℝ} (hP : 0 < P)
    (hx : ∀ i x y,b (x+Pi.single i P) y=b x y)
    (hy : ∀ i x y,b x (y+Pi.single i P)=b x y)
    (μ : Measure (Point n)) [IsFiniteMeasure μ] (σ : Test n →ₗ[ℝ] ℝ)
    (hσ : FiniteEnergy μ σ) {C : ℝ}
    (hC : ∀ Q : ℝ,0 < Q →
      (∀ i x y,b (x+Pi.single i Q) y=b x y) →
      (∀ i x y,b x (y+Pi.single i Q)=b x y) →
      WeightedPeriodicTangentPhysical.energy Q μ σ ≤ C) : energy μ σ ≤ C := by
  apply PeriodicEnergyExhaustion.full_energy_le_of_periodic_multiples μ σ hσ
    (A := P/(2*Real.pi)) (div_pos hP (mul_pos (by norm_num) Real.pi_pos))
  intro j
  have hmul : 2*Real.pi*(P/(2*Real.pi)*((j:ℝ)+1)) = ((j+1:ℕ):ℝ)*P := by
    push_cast
    field_simp
  rw [hmul]
  exact hC _ (mul_pos (by positivity) hP) (KernelPeriodMultiples.first hx (j+1))
    (KernelPeriodMultiples.second hy (j+1))

end SharpWasserstein.BrownianEnergyPeriodization
