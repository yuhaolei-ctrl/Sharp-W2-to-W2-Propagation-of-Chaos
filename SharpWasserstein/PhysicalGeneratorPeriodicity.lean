import SharpWasserstein.ExternalInteractionPeriodic
import SharpWasserstein.FiniteGeneratorBounds

/-! Genuine physical-period invariance of the full Euclidean diffusion
operator. This legitimizes pairing the generator test with the periodic
representative, rather than the larger full-gradient representative. -/
noncomputable section
namespace SharpWasserstein.PhysicalGeneratorPeriodicity
open WeightedTangent PDEPairings PeriodicBochner WeightedPeriodicFourierScale
open ExternalInteractionPeriodic
variable {n : ℕ} {P : ℝ}

theorem directionDeriv_periodic {f : Point n → ℝ}
    (hp : PeriodicOf P (f ∘ (coordinateEquiv n).symm)) (v : Point n) :
    PeriodicOf P (directionDeriv v f ∘ (coordinateEquiv n).symm) := by
  apply of_euclidean_lattice_periodic
  intro k x
  have he : (fun y => f (y+euclideanLattice P k)) = f := funext (euclidean_lattice_periodic hp k)
  have hd := fderiv_comp_add_right (𝕜 := ℝ) (f := f) (x := x) (euclideanLattice P k)
  rw [he] at hd
  exact congrArg (fun L => L v) hd.symm

theorem laplacian_periodic {f : Point n → ℝ}
    (hp : PeriodicOf P (f ∘ (coordinateEquiv n).symm)) :
    PeriodicOf P (PDEPairings.laplacian f ∘ (coordinateEquiv n).symm) := by
  intro i x
  change (∑ j : Fin n, _) = ∑ j : Fin n, _
  apply Finset.sum_congr rfl
  intro j _
  exact directionDeriv_periodic (directionDeriv_periodic hp _) _ i x

theorem generator_periodic {f : Point n → ℝ}
    (hp : PeriodicOf P (f ∘ (coordinateEquiv n).symm))
    {b : Point n → Point n}
    (hpb : ∀ i,Function.Periodic (b ∘ (coordinateEquiv n).symm) (Pi.single i P)) :
    PeriodicOf P (FiniteGeneratorCalculus.generator b f ∘ (coordinateEquiv n).symm) := by
  apply of_euclidean_lattice_periodic
  intro k x
  unfold FiniteGeneratorCalculus.generator
  rw [euclidean_lattice_periodic (laplacian_periodic hp),euclidean_lattice_periodic hpb,
    gradient_lattice_periodic hp]

end SharpWasserstein.PhysicalGeneratorPeriodicity
