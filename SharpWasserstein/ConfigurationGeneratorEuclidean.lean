import SharpWasserstein.ConfigurationEuclidean
import SharpWasserstein.BoundedWeakTests

/-! Exact transport of the genuine coordinate generator to Euclidean space.
No factor of the number of particles is introduced by this coordinate change. -/
noncomputable section
open scoped InnerProductSpace BigOperators
namespace SharpWasserstein
open WeightedTangent PDEPairings

/-- Each actual coordinate derivative becomes its corresponding Euclidean directional derivative. -/
theorem coordinateDerivative_pullback {d N : ℕ} (f : Point (N*d) → ℝ)
    (i : Fin N) (a : Fin d) (x : Configuration d N) :
    coordinateDerivative (f ∘ configurationEuclidean d N) i a x =
      directionDeriv (EuclideanSpace.single (finProdFinEquiv (i,a)) 1) f
        (configurationEuclidean d N x) := by
  unfold coordinateDerivative directionDeriv
  rw [(configurationEuclidean d N).comp_right_fderiv]
  change fderiv ℝ f (configurationEuclidean d N x)
    (configurationEuclidean d N (coordinateVector i a)) = _
  rw [configurationEuclidean_coordinateVector]

/-- The second coordinate derivative obeys the same exact change of coordinates. -/
theorem coordinateDerivative_twice_pullback {d N : ℕ} (f : Point (N*d) → ℝ)
    (i : Fin N) (a : Fin d) (x : Configuration d N) :
    coordinateDerivative (coordinateDerivative (f ∘ configurationEuclidean d N) i a) i a x =
      directionDeriv (EuclideanSpace.single (finProdFinEquiv (i,a)) 1)
        (directionDeriv (EuclideanSpace.single (finProdFinEquiv (i,a)) 1) f)
        (configurationEuclidean d N x) := by
  have hfun : coordinateDerivative (f ∘ configurationEuclidean d N) i a =
      directionDeriv (EuclideanSpace.single (finProdFinEquiv (i,a)) 1) f ∘ configurationEuclidean d N :=
    funext (coordinateDerivative_pullback f i a)
  rw [hfun, coordinateDerivative_pullback]

theorem laplacian_pullback {d N : ℕ} (f : Point (N*d) → ℝ) (x : Configuration d N) :
    SharpWasserstein.laplacian (f ∘ configurationEuclidean d N) x =
      PDEPairings.laplacian f (configurationEuclidean d N x) := by
  unfold SharpWasserstein.laplacian PDEPairings.laplacian
  simp_rw [coordinateDerivative_twice_pullback]
  let g := fun k : Fin (N*d) ↦ directionDeriv (EuclideanSpace.single k 1)
    (directionDeriv (EuclideanSpace.single k 1) f) (configurationEuclidean d N x)
  change (∑ i, ∑ a, g (finProdFinEquiv (i,a))) = ∑ k, g k
  calc
    _ = ∑ p : Fin N × Fin d, g (finProdFinEquiv p) := (Fintype.sum_prod_type _).symm
    _ = _ := Fintype.sum_equiv finProdFinEquiv _ _ (fun _ ↦ rfl)

/-- Exact configuration generator identity, including both diffusion and drift. -/
theorem generator_pullback {d N : ℕ} (f : Point (N*d) → ℝ)
    (v : Configuration d N → Configuration d N) (x : Configuration d N) :
    generator v (f ∘ configurationEuclidean d N) x =
      BoundedWeakTests.generator f (configurationEuclidean d N x) (configurationEuclidean d N (v x)) := by
  unfold generator BoundedWeakTests.generator
  rw [laplacian_pullback, ← fderiv_eq_sum_coordinateDerivative, real_inner_comm, inner_gradient_left,
    (configurationEuclidean d N).comp_right_fderiv]
  rfl

end SharpWasserstein
