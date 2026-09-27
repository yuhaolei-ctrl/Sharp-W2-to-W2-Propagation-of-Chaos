import SharpWasserstein.PropagatedSourcePermutationParticle
import SharpWasserstein.RegularizedSource
import SharpWasserstein.QuantitativeGenerator

/-! Exchangeability of the actual generator-difference source. The diffusion
terms cancel before changing coordinates; no transformation law for a Hessian
or Laplacian is assumed. The result applies to the full regularized source
constructed from the transport-to-entropy argument. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal ContDiff InnerProductSpace
namespace SharpWasserstein.InitialSourcePermutation
open WeightedTangent PropagatedSourcePermutation

/-- Permutation pullback of a genuine configuration test. -/
def configurationPullTest {d N : ℕ} (e : Equiv.Perm (Fin N))
    (φ : ConfigurationTest d N) : ConfigurationTest d N :=
  ⟨φ.val ∘ configurationPermutation e,
    φ.property.1.comp (configurationPermutation e).contDiff,
    φ.property.2.comp_homeomorph (configurationPermutation e).toHomeomorph⟩

/-- The actual full initial current has the manuscript's reference-minus-particle sign. -/
def initialCurrent {d N : ℕ} (b : Position d → Position d → Position d)
    (q : Measure (Position d)) (x : Configuration d N) : Configuration d N :=
  (fun i => nonlinearDrift b q (x i)) - particleDrift b x

/-- The same nonlinear one-particle drift is used in every coordinate; together
with the true particle drift this gives equivariance of the actual current. -/
theorem initialCurrent_covariant {d N : ℕ} (b : Position d → Position d → Position d)
    (q : Measure (Position d)) (e : Equiv.Perm (Fin N)) (x : Configuration d N) :
    initialCurrent b q (configurationPermutation e x) =
      configurationPermutation e (initialCurrent b q x) := by
  unfold initialCurrent
  rw [particleDrift_permutation, map_sub]
  rfl

/-- The two diffusion operators cancel, leaving exactly the actual drift-current pairing. -/
theorem generator_difference {d N : ℕ} (b : Position d → Position d → Position d)
    (q : Measure (Position d)) (φ : Configuration d N → ℝ) (x : Configuration d N) :
    generator (fun z i => nonlinearDrift b q (z i)) φ x -
      generator (particleDrift b) φ x = fderiv ℝ φ x (initialCurrent b q x) := by
  simp only [generator_eq_laplacian_add_fderiv, initialCurrent, map_sub]
  ring

/-- Exchangeability of the full law forces invariance of the actual scalar
source determined by its generator pairing. No source symmetry is a premise. -/
theorem source_invariant {d N : ℕ} (b : Position d → Position d → Position d)
    (q : Measure (Position d)) (μ : Measure (Configuration d N)) (hμ : Exchangeable μ)
    (σ : ConfigurationTest d N →ₗ[ℝ] ℝ)
    (hσ : ∀ φ : ConfigurationTest d N, σ φ =
      ∫ x, generator (fun z i => nonlinearDrift b q (z i)) φ.val x -
        generator (particleDrift b) φ.val x ∂μ)
    (e : Equiv.Perm (Fin N)) (φ : ConfigurationTest d N) :
    σ (configurationPullTest e φ) = σ φ := by
  rw [hσ, hσ]
  simp_rw [generator_difference]
  have hpair (x : Configuration d N) :
      fderiv ℝ (configurationPullTest e φ).val x (initialCurrent b q x) =
      fderiv ℝ φ.val (configurationPermutation e x)
        (initialCurrent b q (configurationPermutation e x)) := by
    change fderiv ℝ (φ.val ∘ configurationPermutation e) x _ = _
    rw [(configurationPermutation e).comp_right_fderiv, initialCurrent_covariant]
    rfl
  simp_rw [hpair]
  have hm : μ.map (configurationPermutation e) = μ := hμ e
  have hi := integral_map_equiv (μ := μ)
    (configurationPermutation (d := d) e).toHomeomorph.toMeasurableEquiv
    (fun x => fderiv ℝ φ.val x (initialCurrent b q x))
  change (∫ x, fderiv ℝ φ.val x (initialCurrent b q x) ∂μ.map (configurationPermutation e)) =
    ∫ x, fderiv ℝ φ.val (configurationPermutation e x)
      (initialCurrent b q (configurationPermutation e x)) ∂μ at hi
  rw [hm] at hi
  exact hi.symm

/-- Euclidean pullback tests agree exactly with the configuration test pullback. -/
theorem testEuclidean_symm_pull {d N : ℕ} (e : Equiv.Perm (Fin N)) (φ : Test (N*d)) :
    (configurationTestEuclidean d N).symm (pullTest (euclideanPermutation e) φ) =
      configurationPullTest e ((configurationTestEuclidean d N).symm φ) := by
  apply Subtype.ext
  funext x
  change (φ : Point (N*d) → ℝ) (euclideanPermutation e (configurationEuclidean d N x)) =
    (φ : Point (N*d) → ℝ) (configurationEuclidean d N (configurationPermutation e x))
  rw [euclideanPermutation_coordinates]

/-- The actual Euclidean distribution satisfies the precise scalar-test
symmetry required for equivariance of its canonical weighted tangent. -/
theorem euclideanSource_invariant {d N : ℕ} (b : Position d → Position d → Position d)
    (q : Measure (Position d)) (μ : Measure (Configuration d N)) (hμ : Exchangeable μ)
    (σ : ConfigurationTest d N →ₗ[ℝ] ℝ)
    (hσ : ∀ φ : ConfigurationTest d N, σ φ =
      ∫ x, generator (fun z i => nonlinearDrift b q (z i)) φ.val x -
        generator (particleDrift b) φ.val x ∂μ)
    (e : Equiv.Perm (Fin N)) (φ : Test (N*d)) :
    euclideanDistribution σ (pullTest (euclideanPermutation e) φ) = euclideanDistribution σ φ := by
  change σ ((configurationTestEuclidean d N).symm (pullTest (euclideanPermutation e) φ)) =
    σ ((configurationTestEuclidean d N).symm φ)
  rw [testEuclidean_symm_pull]
  exact source_invariant b q μ hμ σ hσ e _

/-- In particular, regularization by the constructed decoupled Brownian flow
preserves the exchangeability needed by the actual full generator source. -/
theorem regularizedSource_invariant {d N : ℕ}
    {v : ℝ → Position d → Position d} {M K : ℝ≥0}
    (hv : Continuous (Function.uncurry v)) (hb : ∀ t x, ‖v t x‖ ≤ M)
    (hl : ∀ t, LipschitzWith K (v t)) {T : ℝ} (hT : 0 ≤ T)
    (P : Measure (Configuration d N)) [IsProbabilityMeasure P] (hP : Exchangeable P)
    (q : Measure (Position d)) (b : Position d → Position d → Position d)
    (σ : ConfigurationTest d N →ₗ[ℝ] ℝ)
    (hσ : ∀ φ : ConfigurationTest d N, σ φ =
      ∫ x, generator (fun z i => nonlinearDrift b q (z i)) φ.val x -
        generator (particleDrift b) φ.val x ∂DecoupledFlow.brownianLaw hv hb hl hT P)
    (e : Equiv.Perm (Fin N)) (φ : Test (N*d)) :
    euclideanDistribution σ (pullTest (euclideanPermutation e) φ) = euclideanDistribution σ φ :=
  euclideanSource_invariant b q _ (DecoupledFlow.brownianLaw_exchangeable hv hb hl hT P hP)
    σ hσ e φ

end SharpWasserstein.InitialSourcePermutation
