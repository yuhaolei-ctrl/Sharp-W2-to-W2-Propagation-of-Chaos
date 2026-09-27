import SharpWasserstein.InitialSourcePermutation
import SharpWasserstein.WeightedSourceSymmetry
import SharpWasserstein.PropagatedSourcePermutationAction
import SharpWasserstein.PropagatedSourceEquationDistribution

/-! Actual source symmetry from its generator definition through canonical
weighted-tangent selection and Brownian-Jacobian propagation. No equivariance
of a selected vector field or of the propagated source is a hypothesis. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal ContDiff
namespace SharpWasserstein.InitialSourcePermutation
open WeightedTangent PropagatedSourcePermutation PropagatedSourceEquation

variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  (b : Position d → Position d → Position d) (q : Measure (Position d))
  (μ : Measure (Configuration d N)) [IsFiniteMeasure μ] (hμ : Exchangeable μ)
  (σ : ConfigurationTest d N →ₗ[ℝ] ℝ) (hσE : ConfigurationFiniteEnergy μ σ)
  (hσ : ∀ φ : ConfigurationTest d N, σ φ =
    ∫ x, generator (fun z i => nonlinearDrift b q (z i)) φ.val x -
      generator (particleDrift b) φ.val x ∂μ)

include hμ hσE hσ

/-- The canonical Hilbert representative of the actual generator source is
permutation-equivariant, derived from its defining scalar pairing and energy. -/
theorem initialRepresentative_equivariant (e : Equiv.Perm (Fin N)) :
    ∀ᵐ x ∂euclideanLaw μ,
      (representative (euclideanLaw μ) (euclideanDistribution σ) :
        Lp (Point (N*d)) 2 (euclideanLaw μ)) (euclideanPermutation e x) =
      euclideanPermutation e ((representative (euclideanLaw μ) (euclideanDistribution σ) :
        Lp (Point (N*d)) 2 (euclideanLaw μ)) x) := by
  have hm : (euclideanLaw μ).map (euclideanPermutationIsometry (d := d) e) = euclideanLaw μ :=
    euclideanLaw_permutation μ hμ e
  exact WeightedSourceSymmetry.representative_equivariant (euclideanLaw μ)
    (euclideanPermutationIsometry e) hm (euclideanDistribution σ)
    ((configurationFiniteEnergy_iff μ σ).mp hσE) (euclideanSource_invariant b q μ hμ σ hσ e)

variable (hbs : BoundedSmoothKernel b) {M K : ℝ≥0}
  (hv : Continuous (Function.uncurry (fun _ : ℝ =>
    equivDrift (configurationEuclidean d N) (particleDrift b))))
  (hb : ∀ _ : ℝ, ∀ x, ‖equivDrift (configurationEuclidean d N) (particleDrift b) x‖ ≤ M)
  (hl : ∀ _ : ℝ, LipschitzWith K (equivDrift (configurationEuclidean d N) (particleDrift b)))
  {T : ℝ} (hT : 0 ≤ T)

/-- The actual canonical Brownian-propagated generator source is exchangeable
on compact tests at every time in the clamped construction. -/
theorem particle_distributionAt_invariant (e : Equiv.Perm (Fin N))
    (r : ℝ) (φ : Test (N*d)) :
    Brownian.distributionAt hv hb hl hT (particleDrift_smooth hbs)
      (particleDrift_allDerivativesBounded hbs) (euclideanLaw μ) (euclideanDistribution σ) r
      (pullTest (euclideanPermutation e) φ) =
    Brownian.distributionAt hv hb hl hT (particleDrift_smooth hbs)
      (particleDrift_allDerivativesBounded hbs) (euclideanLaw μ) (euclideanDistribution σ) r φ := by
  exact particle_sourceAt_invariant hbs hv hb hl hT (euclideanLaw μ) e
    (euclideanLaw_permutation μ hμ e) _ (Lp.memLp _)
    (initialRepresentative_equivariant b q μ hμ σ hσE hσ e) r φ

/-- The same actual canonical source symmetry reaches the noncompact kernel
tests used in periodic smoothing, through the literal differentiated expectation. -/
theorem particle_action_invariant (e : Equiv.Perm (Fin N))
    {F : Point (N*d) → ℝ} (hF : Continuous F) (r : ℝ) :
    PeriodicSourceConvolution.action hv hb hl hT (euclideanBrownianPathLaw d N T)
      (euclideanLaw μ) (representative (euclideanLaw μ) (euclideanDistribution σ) :
        Lp (Point (N*d)) 2 (euclideanLaw μ)) (F ∘ euclideanPermutation e) r =
    PeriodicSourceConvolution.action hv hb hl hT (euclideanBrownianPathLaw d N T)
      (euclideanLaw μ) (representative (euclideanLaw μ) (euclideanDistribution σ) :
        Lp (Point (N*d)) 2 (euclideanLaw μ)) F r := by
  exact PropagatedSourcePermutation.action_invariant hv hb hl hT (euclideanPermutation e)
    (particle_equivDrift_covariant b e) _ (euclideanBrownianPathLaw_permutation e)
    (euclideanLaw μ) (euclideanLaw_permutation μ hμ e) _
    (initialRepresentative_equivariant b q μ hμ σ hσE hσ e) hF r

end SharpWasserstein.InitialSourcePermutation
