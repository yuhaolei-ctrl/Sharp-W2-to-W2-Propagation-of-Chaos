import SharpWasserstein.BoundedWeakTests
import SharpWasserstein.WeightedMarginal

/-! Genuine Euclidean cylinder calculus and weak marginalization. Compact tests
in the retained coordinates become noncompact cylinder functions in the full
space; the second-order cutoff theorem justifies their weak evolution identity. -/

noncomputable section
namespace SharpWasserstein.CylinderWeakEvolution
open WeightedTangent WeightedMarginal PDEPairings BochnerIdentity BoundedWeakTests
open scoped InnerProductSpace Topology ContDiff BigOperators

/-- The actual directional chain rule for a continuous linear change of coordinates. -/
theorem directionDeriv_comp_linear {n k : ℕ} (L : Point k →L[ℝ] Point n)
    {f : Point n → ℝ} (hf : Differentiable ℝ f) (v x : Point k) :
    directionDeriv v (f ∘ L) x = directionDeriv (L v) f (L x) := by
  unfold directionDeriv
  rw [fderiv_comp x (hf _) L.differentiableAt, L.fderiv]
  rfl

/-- Applying the actual chain rule twice gives the correct restricted second derivative. -/
theorem directionDeriv_twice_comp_linear {n k : ℕ} (L : Point k →L[ℝ] Point n)
    {f : Point n → ℝ} (hf : ContDiff ℝ 2 f) (v x : Point k) :
    directionDeriv v (directionDeriv v (f ∘ L)) x =
      directionDeriv (L v) (directionDeriv (L v) f) (L x) := by
  have heq : directionDeriv v (f ∘ L) = (directionDeriv (L v) f) ∘ L := by
    funext y
    exact directionDeriv_comp_linear L (hf.differentiable (by simp)) v y
  rw [heq]
  exact directionDeriv_comp_linear L
    ((contDiff_directionDeriv (m := 1) hf (by norm_num) _).differentiable (by simp)) v x

@[simp] theorem prefixProjection_single_left (n m : ℕ) (i : Fin n) :
    prefixProjection n m (EuclideanSpace.single (i.castAdd m) 1) = EuclideanSpace.single i 1 := by
  ext k
  simp [prefixProjection, EuclideanSpace.single, PiLp.single_apply]

@[simp] theorem prefixProjection_single_right (n m : ℕ) (i : Fin m) :
    prefixProjection n m (EuclideanSpace.single (i.natAdd n) 1) = 0 := by
  ext k
  simp [prefixProjection, EuclideanSpace.single, PiLp.single_apply]
  intro h
  have hh := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hh
  omega

/-- The Laplacian of the genuine noncompact cylinder is exactly the lifted marginal Laplacian. -/
theorem laplacian_comp_prefixProjection {n m : ℕ} {f : Point n → ℝ}
    (hf : ContDiff ℝ 2 f) (x : Point (n + m)) :
    laplacian (f ∘ prefixProjection n m) x = laplacian f (prefixProjection n m x) := by
  unfold laplacian
  simp_rw [directionDeriv_twice_comp_linear (prefixProjection n m) hf]
  rw [Fin.sum_univ_add]
  simp only [prefixProjection_single_left, prefixProjection_single_right, directionDeriv,
    map_zero, Finset.sum_const_zero, add_zero]

/-- The actual diffusion-and-drift generator of a cylinder retains only the projected velocity. -/
theorem generator_comp_prefixProjection {n m : ℕ} {f : Point n → ℝ}
    (hf : ContDiff ℝ 2 f) (x v : Point (n + m)) :
    generator (f ∘ prefixProjection n m) x v =
      generator f (prefixProjection n m x) (prefixProjection n m v) := by
  unfold generator
  rw [laplacian_comp_prefixProjection hf, gradient_comp_prefixProjection (hf.differentiable (by simp))]
  congr 1
  rw [real_inner_comm, inner_prefixEmbedding, real_inner_comm]

open MeasureTheory
variable {n m : ℕ} [MeasurableSpace (Point n)] [BorelSpace (Point n)]
  [MeasurableSpace (Point (n + m))] [BorelSpace (Point (n + m))]

/-- Actual compact-test integrals under a coordinate marginal equal cylinder integrals under the full law. -/
theorem integral_marginalLaw (μ : Measure (Point (n + m))) (φ : Test n) :
    (∫ x, (φ : Point n → ℝ) x ∂marginalLaw μ) =
      ∫ x, (φ : Point n → ℝ) (prefixProjection n m x) ∂μ :=
  integral_map (prefixProjection n m).continuous.measurable.aemeasurable
    φ.property.1.continuous.aestronglyMeasurable

/-- A genuine compact-test weak evolution law implies the exact weak law of every coordinate marginal.
The noncompact cylinder is justified by the actual cutoff bounds and dominated convergence. -/
theorem marginal_weak_generator_identity {Ω : Type*} [MeasurableSpace Ω]
    (μ₀ μ₁ : Measure (Point (n + m))) [IsFiniteMeasure μ₀] [IsFiniteMeasure μ₁]
    (τ : Measure Ω) [IsFiniteMeasure τ]
    (X v : Ω → Point (n + m)) (hX : AEStronglyMeasurable X τ) (hv : Integrable v τ)
    (hweak : ∀ φ : Test (n + m),
      (∫ x, (φ : Point (n + m) → ℝ) x ∂μ₁) - (∫ x, (φ : Point (n + m) → ℝ) x ∂μ₀) =
        ∫ z, generator φ (X z) (v z) ∂τ) (φ : Test n) :
    (∫ x, (φ : Point n → ℝ) x ∂marginalLaw μ₁) -
      (∫ x, (φ : Point n → ℝ) x ∂marginalLaw μ₀) =
      ∫ z, generator φ (prefixProjection n m (X z)) (prefixProjection n m (v z)) ∂τ := by
  obtain ⟨hs, ⟨A, hA⟩, ⟨B, hB⟩⟩ := cylinder_test_smooth_bounded (m := m) φ
  have hφ2 : ContDiff ℝ 2 (φ : Point n → ℝ) := contDiff_two_of_smooth φ.property.1
  obtain ⟨D, hD⟩ := (compact_laplacian φ).exists_bound_of_continuous (continuous_laplacian hφ2)
  have hd (x : Point (n + m)) : |laplacian ((φ : Point n → ℝ) ∘ prefixProjection n m) x| ≤ D := by
    rw [laplacian_comp_prefixProjection hφ2]
    simpa only [Real.norm_eq_abs] using hD (prefixProjection n m x)
  have h := extend_weak_generator_identity μ₀ μ₁ τ X v hX hv hweak
    ((φ : Point n → ℝ) ∘ prefixProjection n m) hs hA hB hd
  rw [integral_marginalLaw μ₁ φ, integral_marginalLaw μ₀ φ]
  change (∫ x, ((φ : Point n → ℝ) ∘ prefixProjection n m) x ∂μ₁) -
    (∫ x, ((φ : Point n → ℝ) ∘ prefixProjection n m) x ∂μ₀) = _
  rw [h]
  apply integral_congr_ae
  filter_upwards [] with z
  exact generator_comp_prefixProjection hφ2 _ _

end SharpWasserstein.CylinderWeakEvolution
