import SharpWasserstein.PropagatedSourcePermutation
import SharpWasserstein.ParticleWeakIdentification

/-! The actual independent Brownian path law and self-interacting particle
vector field satisfy the source covariance hypotheses in genuine Euclidean
coordinates. The Euclidean permutation is an isometry for the unnormalized
sum-of-squares cost, with no factor depending on the number of particles. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal ContDiff InnerProductSpace BigOperators
namespace SharpWasserstein.PropagatedSourcePermutation
open WeightedTangent PropagatedSourceEquation NoiseAverage

/-- Conjugate the whole-particle permutation by the true Euclidean coordinates. -/
def euclideanPermutation {d N : ℕ} (e : Equiv.Perm (Fin N)) :
    Point (N*d) ≃L[ℝ] Point (N*d) :=
  ((configurationEuclidean d N).symm.trans (configurationPermutation e)).trans
    (configurationEuclidean d N)

@[simp] theorem euclideanPermutation_coordinates {d N : ℕ} (e : Equiv.Perm (Fin N))
    (x : Configuration d N) :
    euclideanPermutation e (configurationEuclidean d N x) =
      configurationEuclidean d N (configurationPermutation e x) := by
  simp [euclideanPermutation]

/-- Unlike the nested Pi-to-Euclidean coordinate map, the conjugated permutation
preserves the genuine Hilbert norm exactly. -/
theorem euclideanPermutation_norm {d N : ℕ} (e : Equiv.Perm (Fin N)) (y : Point (N*d)) :
    ‖euclideanPermutation e y‖ = ‖y‖ := by
  obtain ⟨x,rfl⟩ := (configurationEuclidean d N).surjective y
  have hsq : ‖euclideanPermutation e (configurationEuclidean d N x)‖^2 =
      ‖configurationEuclidean d N x‖^2 := by
    rw [euclideanPermutation_coordinates, configurationEuclidean_norm_sq,
      configurationEuclidean_norm_sq]
    change (∑ i, ∑ a, (x (e i) a)^2) = ∑ i, ∑ a, (x i a)^2
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  nlinarith [norm_nonneg (euclideanPermutation e (configurationEuclidean d N x)),
    norm_nonneg (configurationEuclidean d N x)]

/-- The actual linear isometry used in gradient and energy identities. -/
def euclideanPermutationIsometry {d N : ℕ} (e : Equiv.Perm (Fin N)) :
    Point (N*d) ≃ₗᵢ[ℝ] Point (N*d) where
  toLinearEquiv := (euclideanPermutation e).toLinearEquiv
  norm_map' := euclideanPermutation_norm e

/-- The gradient of a pulled-back scalar test is the inverse-permuted gradient. -/
theorem euclideanPermutation_gradient {d N : ℕ} (e : Equiv.Perm (Fin N))
    (φ : Test (N*d)) (x : Point (N*d)) :
    gradient (pullTest (euclideanPermutation e) φ : Point (N*d) → ℝ) x =
      (euclideanPermutation e).symm
        (gradient (φ : Point (N*d) → ℝ) (euclideanPermutation e x)) := by
  apply ext_inner_right ℝ
  intro v
  rw [pullTest_gradient_pairing]
  have h := (euclideanPermutationIsometry (d := d) e).inner_map_map
    ((euclideanPermutation e).symm (gradient (φ : Point (N*d) → ℝ)
      (euclideanPermutation e x))) v
  simpa [euclideanPermutationIsometry] using h

/-- Covariance of the genuine Euclidean mean-field drift, including self-interaction. -/
theorem particle_equivDrift_covariant {d N : ℕ}
    (b : Position d → Position d → Position d) (e : Equiv.Perm (Fin N))
    (y : Point (N*d)) :
    equivDrift (configurationEuclidean d N) (particleDrift b) (euclideanPermutation e y) =
      euclideanPermutation e (equivDrift (configurationEuclidean d N) (particleDrift b) y) := by
  obtain ⟨x,rfl⟩ := (configurationEuclidean d N).surjective y
  simp [equivDrift, particleDrift_permutation]

/-- The two literal path transformations commute with flattening coordinates. -/
theorem equivPath_permutation {d N : ℕ} {T : ℝ} (e : Equiv.Perm (Fin N)) :
    equivPath (T := T) (euclideanPermutation (d := d) e) ∘ equivPath (configurationEuclidean d N) =
      equivPath (configurationEuclidean d N) ∘ permutedPath e := by
  funext w
  apply ContinuousMap.ext
  intro t
  exact euclideanPermutation_coordinates e (w t)

/-- Independent Brownian path noise is invariant under the genuine Euclidean
particle permutation. This is derived from the constructed product path law. -/
theorem euclideanBrownianPathLaw_permutation {d N : ℕ}
    [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
    {T : ℝ} (e : Equiv.Perm (Fin N)) :
    (euclideanBrownianPathLaw d N T).map (equivPath (euclideanPermutation e)) =
      euclideanBrownianPathLaw d N T := by
  unfold euclideanBrownianPathLaw
  rw [Measure.map_map (equivPath_continuous _).measurable (equivPath_continuous _).measurable,
    equivPath_permutation,
    ← Measure.map_map (equivPath_continuous _).measurable (permutedPath_continuous e).measurable,
    BrownianNoise.configurationLaw_permutation]

/-- Exchangeability of the original configuration law gives actual Euclidean
measure invariance, including singular initial laws. -/
theorem euclideanLaw_permutation {d N : ℕ}
    [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
    (μ : Measure (Configuration d N)) (hμ : Exchangeable μ) (e : Equiv.Perm (Fin N)) :
    (μ.map (configurationEuclidean d N)).map (euclideanPermutation e) =
      μ.map (configurationEuclidean d N) := by
  rw [Measure.map_map (euclideanPermutation e).continuous.measurable
    (configurationEuclidean d N).continuous.measurable]
  have he : euclideanPermutation e ∘ configurationEuclidean d N =
      configurationEuclidean d N ∘ configurationPermutation e := by
    funext x
    exact euclideanPermutation_coordinates e x
  rw [he, ← Measure.map_map (configurationEuclidean d N).continuous.measurable
    (configurationPermutation e).continuous.measurable]
  have hm : μ.map (configurationPermutation e) = μ := hμ e
  rw [hm]

/-- The actual Brownian-Jacobian particle source is invariant under every
permutation for which its initial L² field is equivariant. All drift and noise
covariance hypotheses have been discharged for the actual particle model. -/
theorem particle_sourceAt_invariant {d N : ℕ}
    [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
    {b : Position d → Position d → Position d} (hbs : BoundedSmoothKernel b)
    {M K : ℝ≥0}
    (hv : Continuous (Function.uncurry (fun _ : ℝ =>
      equivDrift (configurationEuclidean d N) (particleDrift b))))
    (hb : ∀ _ : ℝ, ∀ x, ‖equivDrift (configurationEuclidean d N) (particleDrift b) x‖ ≤ M)
    (hl : ∀ _ : ℝ, LipschitzWith K (equivDrift (configurationEuclidean d N) (particleDrift b)))
    {T : ℝ} (hT : 0 ≤ T) (μ : Measure (Point (N*d))) [IsFiniteMeasure μ]
    (e : Equiv.Perm (Fin N)) (hμ : μ.map (euclideanPermutation e) = μ)
    (u : Point (N*d) → Point (N*d)) (hu : MemLp u 2 μ)
    (hue : ∀ᵐ x ∂μ, u (euclideanPermutation e x) = euclideanPermutation e (u x))
    (r : ℝ) (φ : Test (N*d)) :
    Brownian.sourceAt hv hb hl hT (particleDrift_smooth hbs)
      (particleDrift_allDerivativesBounded hbs) μ u hu r (pullTest (euclideanPermutation e) φ) =
    Brownian.sourceAt hv hb hl hT (particleDrift_smooth hbs)
      (particleDrift_allDerivativesBounded hbs) μ u hu r φ := by
  exact source_invariant hv hb hl hT (euclideanPermutation e)
    (particle_equivDrift_covariant b e) _ (euclideanBrownianPathLaw_permutation e)
    (projIcc 0 T hT r).property _ _ μ hμ u hu hue φ

end SharpWasserstein.PropagatedSourcePermutation
