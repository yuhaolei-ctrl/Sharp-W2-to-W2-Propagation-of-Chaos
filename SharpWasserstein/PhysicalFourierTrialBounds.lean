module

public import SharpWasserstein.Compat
public import SharpWasserstein.WeightedPeriodicFourierPhysical
public import SharpWasserstein.WeightedPeriodicCoefficientEvolutionFourier

@[expose] public section

/-! All analytic hypotheses of the finite diffusion calculation are
verified for the actual physical-period Fourier atoms. -/
noncomputable section
open scoped ContDiff BigOperators
namespace SharpWasserstein.WeightedPeriodicFourierPhysical
open WeightedTangent NoiseAverage PeriodicIntegrationByParts PeriodicBochner PeriodicFourierTests
variable {n : ℕ}

theorem physicalPotential_allDerivativesBounded (P : ℝ) {f : Coordinates n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Periodic f) : AllDerivativesBounded (physicalPotential P f) :=
  (WeightedPeriodicCoefficientEvolution.periodic_allDerivativesBounded hf hp).comp_linear hf
    (P⁻¹ • (coordinateEquiv n).toContinuousLinearMap)

theorem physicalAtom_laplacian (P : ℝ) (p : (Fin n → ℤ) × Bool) (x : Point n) :
    PDEPairings.laplacian (physicalPotential P (atom p)) x =
      -(eigenvalue p.1/P^2)*physicalPotential P (atom p) x := by
  change PDEPairings.laplacian (pullback (WeightedPeriodicFourierScale.atom P p)) x = _
  rw [PeriodicBochner.laplacian_pullback,WeightedPeriodicFourierScale.laplacian_atom]
  rfl

theorem physicalAtom_eigenvalue_nonneg (P : ℝ) (p : (Fin n → ℤ) × Bool) :
    0 ≤ eigenvalue p.1/P^2 := by
  apply div_nonneg _ (sq_nonneg _)
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

end SharpWasserstein.WeightedPeriodicFourierPhysical
