module

public import SharpWasserstein.Compat
public import SharpWasserstein.WeightedGradientApproximation
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Calculus.FDeriv.Comp

@[expose] public section

/-! Actual coordinate marginal lifting in weighted Euclidean `L²`.
The measure on the lower-dimensional space is the genuine pushforward by the
prefix projection. Zero-extension and pullback preserve its exact `L²` norm. -/

noncomputable section
namespace SharpWasserstein.WeightedMarginal

open MeasureTheory Set Filter WeightedTangent
open scoped InnerProductSpace Topology BigOperators ContDiff

/-- Retain the first `n` Euclidean coordinates. -/
def prefixProjection (n m : ℕ) : Point (n + m) →L[ℝ] Point n where
  toFun x := WithLp.toLp 2 (fun i => x (i.castAdd m))
  map_add' x y := rfl
  map_smul' c x := rfl
  cont := (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp (by fun_prop)

theorem prefixProjection_apply (n m : ℕ) (x : Point (n + m)) :
    prefixProjection n m x = WithLp.toLp 2 (fun i => x (i.castAdd m)) := rfl

/-- Extend a lower-dimensional vector by zero in the remaining coordinates. -/
def prefixEmbedding (n m : ℕ) : Point n →ₗᵢ[ℝ] Point (n + m) where
  toFun v := WithLp.toLp 2 (Fin.addCases (fun i => v i) (fun _ => 0))
  map_add' v w := by ext k; cases k using Fin.addCases <;> simp
  map_smul' c v := by ext k; cases k using Fin.addCases <;> simp
  norm_map' v := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_add]

/-- Coordinate restriction and zero-extension are adjoint in the true Euclidean inner product. -/
theorem inner_prefixEmbedding (n m : ℕ) (v : Point n) (x : Point (n + m)) :
    ⟪prefixEmbedding n m v, x⟫_ℝ = ⟪v, prefixProjection n m x⟫_ℝ := by
  simp [prefixEmbedding, prefixProjection_apply, PiLp.inner_apply, Fin.sum_univ_add]

@[simp] theorem prefixProjection_embedding (n m : ℕ) (v : Point n) :
    prefixProjection n m (prefixEmbedding n m v) = v := by
  ext i
  simp [prefixProjection_apply, prefixEmbedding]

/-- The genuine gradient of a lifted test is its zero-extended marginal gradient. -/
theorem gradient_comp_prefixProjection {n m : ℕ} {φ : Point n → ℝ}
    (hφ : Differentiable ℝ φ) (x : Point (n + m)) :
    gradient (φ ∘ prefixProjection n m) x =
      prefixEmbedding n m (gradient φ (prefixProjection n m x)) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left, inner_prefixEmbedding, inner_gradient_left]
  rw [fderiv_comp x (hφ _) (prefixProjection n m).differentiableAt,
    ContinuousLinearMap.fderiv]
  rfl

variable {n m : ℕ} [MeasurableSpace (Point n)] [BorelSpace (Point n)]
  [MeasurableSpace (Point (n + m))] [BorelSpace (Point (n + m))]

/-- The actual coordinate marginal measure. -/
def marginalLaw (μ : Measure (Point (n + m))) : Measure (Point n) :=
  Measure.map (prefixProjection n m) μ

instance marginalLaw_finite (μ : Measure (Point (n + m))) [IsFiniteMeasure μ] :
    IsFiniteMeasure (marginalLaw μ) := by unfold marginalLaw; infer_instance

/-- The prefix map is measure preserving for its pushforward marginal. -/
theorem measurePreserving_prefix (μ : Measure (Point (n + m))) :
    MeasurePreserving (prefixProjection n m) μ (marginalLaw μ) :=
  ⟨(prefixProjection n m).continuous.measurable, rfl⟩

/-- Pull back a marginal vector field and zero-extend its values into the full coordinates. -/
def vectorLiftLinear (μ : Measure (Point (n + m))) :
    Lp (Point n) 2 (marginalLaw μ) →ₗ[ℝ] Lp (Point (n + m)) 2 μ :=
  ((prefixEmbedding n m).toContinuousLinearMap.compLpₗ 2 μ).comp
    (Lp.compMeasurePreservingₗ ℝ (prefixProjection n m) (measurePreserving_prefix μ))

/-- The `L²` field is the actual coordinate pullback and zero extension almost everywhere. -/
theorem vectorLiftLinear_ae (μ : Measure (Point (n + m)))
    (v : Lp (Point n) 2 (marginalLaw μ)) :
    vectorLiftLinear μ v =ᵐ[μ] fun x => prefixEmbedding n m (v (prefixProjection n m x)) := by
  filter_upwards [(prefixEmbedding n m).toContinuousLinearMap.coeFn_compLp
      (Lp.compMeasurePreserving (prefixProjection n m) (measurePreserving_prefix μ) v),
    Lp.coeFn_compMeasurePreserving v (measurePreserving_prefix μ)] with x ha hb
  exact ha.trans (congrArg (prefixEmbedding n m) hb)

/-- Marginal lifting preserves the exact norm, independently of correlations in the full law. -/
theorem vectorLiftLinear_norm (μ : Measure (Point (n + m)))
    (v : Lp (Point n) 2 (marginalLaw μ)) : ‖vectorLiftLinear μ v‖ = ‖v‖ := by
  have hnorm : ∀ᵐ x ∂μ, ‖vectorLiftLinear μ v x‖ =
      ‖Lp.compMeasurePreserving (prefixProjection n m) (measurePreserving_prefix μ) v x‖ := by
    filter_upwards [vectorLiftLinear_ae μ v,
      Lp.coeFn_compMeasurePreserving v (measurePreserving_prefix μ)] with x ha hb
    rw [ha, hb, LinearIsometry.norm_map]
    rfl
  calc
    ‖vectorLiftLinear μ v‖ = ‖Lp.compMeasurePreserving (prefixProjection n m)
        (measurePreserving_prefix μ) v‖ := by
          simp only [Lp.norm_def]
          congr 1
          exact eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _) hnorm
    _ = ‖v‖ := Lp.norm_compMeasurePreserving _ _

/-- The actual coordinate lift as a linear isometry of weighted Hilbert spaces. -/
def vectorLift (μ : Measure (Point (n + m))) :
    Lp (Point n) 2 (marginalLaw μ) →ₗᵢ[ℝ] Lp (Point (n + m)) 2 μ where
  toLinearMap := vectorLiftLinear μ
  norm_map' := vectorLiftLinear_norm μ

variable (μ : Measure (Point (n + m))) [IsFiniteMeasure μ]

/-- A lifted test gradient is almost everywhere the gradient of the actual noncompact cylinder test. -/
theorem vectorLift_testGradient_ae (φ : Test n) :
    vectorLift μ (testGradient (marginalLaw μ) φ) =ᵐ[μ]
      gradient ((φ : Point n → ℝ) ∘ prefixProjection n m) := by
  have hg := ae_of_ae_map (prefixProjection n m).continuous.measurable.aemeasurable
    (testGradient_ae (marginalLaw μ) φ)
  filter_upwards [vectorLiftLinear_ae μ (testGradient (marginalLaw μ) φ), hg] with x ha hb
  exact ha.trans (by rw [hb, gradient_comp_prefixProjection (test_differentiable φ)])

omit [MeasurableSpace (Point n)] [BorelSpace (Point n)]
  [MeasurableSpace (Point (n + m))] [BorelSpace (Point (n + m))] in
/-- Every compact marginal test lifts to a smooth globally bounded cylinder function. -/
theorem cylinder_test_smooth_bounded (φ : Test n) :
    ContDiff ℝ ∞ ((φ : Point n → ℝ) ∘ prefixProjection n m) ∧
      (∃ A : ℝ, ∀ x : Point (n + m), |φ.val (prefixProjection n m x)| ≤ A) ∧
      (∃ B : ℝ, ∀ x : Point (n + m),
        ‖gradient ((φ : Point n → ℝ) ∘ prefixProjection n m) x‖ ≤ B) := by
  refine ⟨φ.property.1.comp (prefixProjection n m).contDiff, ?_, ?_⟩
  · obtain ⟨A, hA⟩ := φ.property.2.exists_bound_of_continuous φ.property.1.continuous
    exact ⟨A, fun x => by simpa only [Real.norm_eq_abs] using hA (prefixProjection n m x)⟩
  · obtain ⟨B, hB⟩ := (compactSupport_test_gradient φ).exists_bound_of_continuous
      (continuous_test_gradient φ)
    refine ⟨B, fun x => ?_⟩
    rw [gradient_comp_prefixProjection (test_differentiable φ), LinearIsometry.norm_map]
    exact hB (prefixProjection n m x)

/-- Lifted compact-test gradients belong to the full gradient closure by actual smooth-cutoff approximation. -/
theorem vectorLift_testGradient_mem (φ : Test n) :
    vectorLift μ (testGradient (marginalLaw μ) φ) ∈ gradientClosure μ := by
  obtain ⟨hs, ha, hb⟩ := cylinder_test_smooth_bounded (m := m) φ
  have hg := bounded_smooth_gradient_memLp μ _ hs hb
  have he : vectorLift μ (testGradient (marginalLaw μ) φ) =
      hg.toLp (gradient ((φ : Point n → ℝ) ∘ prefixProjection n m)) := by
    apply Lp.ext
    exact (vectorLift_testGradient_ae μ φ).trans hg.coeFn_toLp.symm
  rw [he]
  exact bounded_smooth_gradient_memClosure μ _ hs ha hb hg

/-- The actual lifted gradient is the strong weighted `L²` limit of compact smooth test gradients. -/
theorem exists_lifted_test_approximation (φ : Test n) :
    ∃ ψs : ℕ → Test (n + m), Tendsto (fun j => testGradient μ (ψs j)) atTop
      (𝓝 (vectorLift μ (testGradient (marginalLaw μ) φ))) := by
  obtain ⟨hs, ha, hb⟩ := cylinder_test_smooth_bounded (m := m) φ
  have hg := bounded_smooth_gradient_memLp μ _ hs hb
  have he : vectorLift μ (testGradient (marginalLaw μ) φ) =
      hg.toLp (gradient ((φ : Point n → ℝ) ∘ prefixProjection n m)) := by
    apply Lp.ext
    exact (vectorLift_testGradient_ae μ φ).trans hg.coeFn_toLp.symm
  rw [he]
  exact exists_test_gradient_tendsto μ _ hs ha hb hg

/-- The full closed marginal tangent space embeds in the full closed gradient space. -/
theorem vectorLift_gradientClosure_mem (w : gradientClosure (marginalLaw μ)) :
    vectorLift μ (w : Lp (Point n) 2 (marginalLaw μ)) ∈ gradientClosure μ := by
  refine (dense_gradientIntoClosure (marginalLaw μ)).induction_on w ?_ ?_
  · exact (testGradientLinear μ).range.isClosed_topologicalClosure.preimage
      ((vectorLift μ).continuous.comp continuous_subtype_val)
  · intro φ
    exact vectorLift_testGradient_mem μ φ

/-- The actual embedding of closed weighted marginal gradient spaces. -/
def tangentLift : gradientClosure (marginalLaw μ) →ₗᵢ[ℝ] gradientClosure μ where
  toFun w := ⟨vectorLift μ (w : Lp (Point n) 2 (marginalLaw μ)), vectorLift_gradientClosure_mem μ w⟩
  map_add' w z := by apply Subtype.ext; exact map_add (vectorLift μ) _ _
  map_smul' c w := by apply Subtype.ext; exact map_smul (vectorLift μ) _ _
  norm_map' w := (vectorLift μ).norm_map w

/-- The actual lifted marginal gradient subspace of the full weighted tangent space. -/
def liftedGradientSubspace : Submodule ℝ (gradientClosure μ) :=
  (tangentLift μ).toLinearMap.range

/-- This concrete marginal gradient subspace is closed, since its embedding is an isometry. -/
theorem liftedGradientSubspace_isClosed : IsClosed (liftedGradientSubspace μ : Set (gradientClosure μ)) :=
  (tangentLift μ).isometry.isClosedEmbedding.isClosed_range

instance liftedGradientSubspace_completeSpace : CompleteSpace (liftedGradientSubspace μ) :=
  (liftedGradientSubspace_isClosed μ).completeSpace_coe

/-- The marginal distribution obtained by the canonical finite-energy action on cylinder gradients. -/
def marginalDistribution (σ : Test (n + m) →ₗ[ℝ] ℝ) : Test n →ₗ[ℝ] ℝ :=
  (innerₗ (Lp (Point (n + m)) 2 μ) (representative μ σ : Lp (Point (n + m)) 2 μ)).comp
    ((vectorLift μ).toLinearMap.comp (testGradientLinear (marginalLaw μ)))

/-- The induced marginal action is an actual weighted integral against a cylinder gradient. -/
theorem marginalDistribution_integral (σ : Test (n + m) →ₗ[ℝ] ℝ) (φ : Test n) :
    marginalDistribution μ σ φ = ∫ x,
      ⟪gradient ((φ : Point n → ℝ) ∘ prefixProjection n m) x,
        (representative μ σ : Lp (Point (n + m)) 2 μ) x⟫_ℝ ∂μ := by
  change ⟪(representative μ σ : Lp (Point (n + m)) 2 μ),
    vectorLift μ (testGradient (marginalLaw μ) φ)⟫_ℝ = _
  rw [real_inner_comm, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [vectorLift_testGradient_ae μ φ] with x hx
  rw [hx]

/-- Each marginal variational objective is bounded by the full representative's genuine energy. -/
theorem marginal_testObjective_le (σ : Test (n + m) →ₗ[ℝ] ℝ) (φ : Test n) :
    testObjective (marginalLaw μ) (marginalDistribution μ σ) φ ≤ ‖representative μ σ‖ ^ 2 := by
  unfold testObjective
  rw [← testGradient_norm_sq]
  change 2 * ⟪(representative μ σ : Lp (Point (n + m)) 2 μ),
    vectorLift μ (testGradient (marginalLaw μ) φ)⟫_ℝ - ‖testGradient (marginalLaw μ) φ‖ ^ 2 ≤
      ‖(representative μ σ : Lp (Point (n + m)) 2 μ)‖ ^ 2
  have hh := norm_sub_sq_real (representative μ σ : Lp (Point (n + m)) 2 μ)
    (vectorLift μ (testGradient (marginalLaw μ) φ))
  rw [LinearIsometry.norm_map] at hh
  nlinarith [sq_nonneg ‖(representative μ σ : Lp (Point (n + m)) 2 μ) -
    vectorLift μ (testGradient (marginalLaw μ) φ)‖]

/-- The induced marginal distribution has finite energy without assuming any marginal estimate. -/
theorem marginalDistribution_finite (σ : Test (n + m) →ₗ[ℝ] ℝ) :
    FiniteEnergy (marginalLaw μ) (marginalDistribution μ σ) := by
  refine ⟨‖representative μ σ‖ ^ 2, ?_⟩
  rintro y ⟨φ, rfl⟩
  exact marginal_testObjective_le μ σ φ

/-- Marginal consistency holds on the entire actual closed weighted gradient space by density. -/
theorem marginal_representative_pairing (σ : Test (n + m) →ₗ[ℝ] ℝ)
    (w : gradientClosure (marginalLaw μ)) :
    ⟪(representative μ σ : Lp (Point (n + m)) 2 μ),
      vectorLift μ (w : Lp (Point n) 2 (marginalLaw μ))⟫_ℝ =
    ⟪(representative (marginalLaw μ) (marginalDistribution μ σ) :
      Lp (Point n) 2 (marginalLaw μ)), (w : Lp (Point n) 2 (marginalLaw μ))⟫_ℝ := by
  refine (dense_gradientIntoClosure (marginalLaw μ)).induction_on w
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro φ
  have hp := representative_divergence (marginalLaw μ) (marginalDistribution μ σ)
    (marginalDistribution_finite μ σ) φ
  rw [gradient_pairing_eq_inner] at hp
  change marginalDistribution μ σ φ = _
  rw [real_inner_comm]
  exact hp

/-- The exact increment for genuine coordinate marginals, with no abstract subspace consistency assumption. -/
theorem marginal_energy_increment (σ : Test (n + m) →ₗ[ℝ] ℝ) (hσ : FiniteEnergy μ σ) :
    energy μ σ - energy (marginalLaw μ) (marginalDistribution μ σ) =
      ‖(representative μ σ : Lp (Point (n + m)) 2 μ) -
        vectorLift μ (representative (marginalLaw μ) (marginalDistribution μ σ) :
          Lp (Point n) 2 (marginalLaw μ))‖ ^ 2 := by
  rw [energy_eq_norm_sq μ σ hσ,
    energy_eq_norm_sq _ _ (marginalDistribution_finite μ σ)]
  have hp := marginal_representative_pairing μ σ
    (representative (marginalLaw μ) (marginalDistribution μ σ))
  rw [real_inner_self_eq_norm_sq] at hp
  rw [norm_sub_sq_real, LinearIsometry.norm_map]
  change ‖(representative μ σ : Lp (Point (n + m)) 2 μ)‖ ^ 2 -
    ‖(representative (marginalLaw μ) (marginalDistribution μ σ) :
      Lp (Point n) 2 (marginalLaw μ))‖ ^ 2 = _
  linarith

/-- Genuine marginalization decreases the variational tangent energy. -/
theorem marginal_energy_le (σ : Test (n + m) →ₗ[ℝ] ℝ) (hσ : FiniteEnergy μ σ) :
    energy (marginalLaw μ) (marginalDistribution μ σ) ≤ energy μ σ := by
  have h := marginal_energy_increment μ σ hσ
  nlinarith [sq_nonneg ‖(representative μ σ : Lp (Point (n + m)) 2 μ) -
    vectorLift μ (representative (marginalLaw μ) (marginalDistribution μ σ) :
      Lp (Point n) 2 (marginalLaw μ))‖]

/-- The lower tangent is the actual orthogonal projection onto the concrete closed marginal gradient subspace. -/
theorem marginal_representative_projection (σ : Test (n + m) →ₗ[ℝ] ℝ) :
    (liftedGradientSubspace μ).starProjection (representative μ σ) =
      tangentLift μ (representative (marginalLaw μ) (marginalDistribution μ σ)) := by
  apply (liftedGradientSubspace μ).eq_starProjection_of_mem_of_inner_eq_zero
    (LinearMap.mem_range_self _ _)
  intro z hz
  obtain ⟨w, rfl⟩ := hz
  rw [inner_sub_left]
  change ⟪(representative μ σ : Lp (Point (n + m)) 2 μ),
    vectorLift μ (w : Lp (Point n) 2 (marginalLaw μ))⟫_ℝ -
    ⟪vectorLift μ (representative (marginalLaw μ) (marginalDistribution μ σ) :
      Lp (Point n) 2 (marginalLaw μ)), vectorLift μ (w : Lp (Point n) 2 (marginalLaw μ))⟫_ℝ = 0
  rw [marginal_representative_pairing, LinearIsometry.inner_map_map, sub_self]

/-- Cylinder action is a limit of genuine compact-test distribution values, as required for marginal consistency. -/
theorem marginalDistribution_is_cutoff_limit (σ : Test (n + m) →ₗ[ℝ] ℝ)
    (hσ : FiniteEnergy μ σ) (φ : Test n) :
    ∃ ψs : ℕ → Test (n + m),
      Tendsto (fun j => testGradient μ (ψs j)) atTop
        (𝓝 (vectorLift μ (testGradient (marginalLaw μ) φ))) ∧
      Tendsto (fun j => σ (ψs j)) atTop (𝓝 (marginalDistribution μ σ φ)) := by
  obtain ⟨ψs, ht⟩ := exists_lifted_test_approximation μ φ
  refine ⟨ψs, ht, ?_⟩
  have hp (j : ℕ) : σ (ψs j) =
      ⟪(representative μ σ : Lp (Point (n + m)) 2 μ), testGradient μ (ψs j)⟫_ℝ := by
    rw [representative_divergence μ σ hσ, gradient_pairing_eq_inner, real_inner_comm]
  simp_rw [hp]
  exact (continuous_const.inner continuous_id).continuousAt.tendsto.comp ht

end SharpWasserstein.WeightedMarginal
