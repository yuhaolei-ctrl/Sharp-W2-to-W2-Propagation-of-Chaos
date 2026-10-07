module

public import SharpWasserstein.Compat
public import SharpWasserstein.EulerBrownianLaw
public import SharpWasserstein.ConfigurationEuclidean

@[expose] public section

/-! The probabilistic coordinate flattening uses exactly the same unnormalized
Euclidean coordinates as the transport and drift estimates. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace SharpWasserstein

theorem configurationFlatten_apply {d N : ℕ} (x : Configuration d N) (k : Fin (N*d)) :
    configurationFlatten d N x k = x (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 := by
  simp [configurationFlatten, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]

theorem configurationFlatten_symm_apply {d N : ℕ} (x : Position (N*d)) (i : Fin N) (a : Fin d) :
    (configurationFlatten d N).symm x i a = x (finProdFinEquiv (i,a)) := by
  simp [configurationFlatten, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]

/-- The measurable flattening and the previously constructed continuous linear
Euclidean equivalence have literally the same coordinates. -/
theorem configurationFlatten_eq_euclidean {d N : ℕ} (x : Configuration d N) :
    configurationFlatten d N x = WithLp.ofLp (configurationEuclidean d N x) := by
  funext k
  rw [configurationFlatten_apply]
  rfl

/-- No factor of the dimension enters the Gaussian transition cost. -/
theorem configurationFlatten_displacementSq {d N : ℕ} (x y : Configuration d N) :
    (∑ k : Fin (N*d), (configurationFlatten d N x k - configurationFlatten d N y k)^2) =
      productCost x y := by
  rw [configurationFlatten_eq_euclidean, configurationFlatten_eq_euclidean,
    productCost_eq_configurationEuclidean_dist_sq, EuclideanSpace.real_norm_sq_eq]
  rfl

end SharpWasserstein
