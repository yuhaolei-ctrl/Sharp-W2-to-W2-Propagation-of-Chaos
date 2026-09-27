import SharpWasserstein.WeightedPeriodicFourierClosure

/-! The genuine periodic tangent of an arbitrary finite-energy distribution.
The periodic test action is the uniquely continuous extension obtained from
actual compact-gradient cutoffs. Its representing vector is the orthogonal
projection of the full Euclidean tangent into the proved periodic closure. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace
namespace SharpWasserstein.WeightedPeriodicTangent
open WeightedTangent PeriodicIntegrationByParts PeriodicBochner
open PeriodicSmoothGradient (SmoothPeriodicTest)
open WeightedPeriodicFourier
variable {n : ℕ} [MeasurableSpace (Point n)] [BorelSpace (Point n)]
variable (μ : Measure (Point n)) [IsFiniteMeasure μ]

/-- Restrict the already constructed continuous distributional extension to
actual smooth periodic gradients. -/
def source (σ : Test n →ₗ[ℝ] ℝ) : SmoothPeriodicTest n →ₗ[ℝ] ℝ :=
  (DenseVariational.extension σ (gradientIntoClosure μ)).toLinearMap.comp (periodicGradientMap μ)

/-- The actual periodic representative, within its strict closed subspace. -/
def representative (σ : Test n →ₗ[ℝ] ℝ) : periodicSpace μ :=
  (periodicSpace μ).orthogonalProjectionOnto (WeightedTangent.representative μ σ)

/-- The genuine periodic test-gradient map into that subspace. -/
def gradientIntoPeriodic : SmoothPeriodicTest n →ₗ[ℝ] periodicSpace μ :=
  (periodicGradientMap μ).codRestrict (periodicSpace μ)
    (fun f => gradientVector_mem_periodicSpace μ f.val f.property.1 f.property.2)

theorem dense_gradientIntoPeriodic : DenseRange (gradientIntoPeriodic μ) := by
  rw [DenseRange,Subtype.dense_iff]
  intro v hv
  rw [periodicSpace_eq_smoothGradientClosure] at hv
  change v ∈ closure (Set.range (periodicGradientMap μ)) at hv
  convert hv using 1
  congr 1
  ext w
  simp only [Set.mem_image,Set.mem_range]
  constructor
  · rintro ⟨z,⟨f,rfl⟩,rfl⟩
    exact ⟨f,rfl⟩
  · rintro ⟨f,rfl⟩
    exact ⟨gradientIntoPeriodic μ f,⟨f,rfl⟩,rfl⟩

theorem source_eq_full_pairing (σ : Test n →ₗ[ℝ] ℝ) (f : SmoothPeriodicTest n) :
    source μ σ f = ⟪WeightedTangent.representative μ σ,periodicGradientMap μ f⟫_ℝ := by
  exact (TangentEnergy.inner_rieszRepresentative
    (DenseVariational.extension σ (gradientIntoClosure μ)) (periodicGradientMap μ f)).symm

theorem representative_pairing (σ : Test n →ₗ[ℝ] ℝ) (f : SmoothPeriodicTest n) :
    ⟪representative μ σ,gradientIntoPeriodic μ f⟫_ℝ = source μ σ f := by
  rw [source_eq_full_pairing]
  exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right _ _

theorem gradientVector_pairing (f : SmoothPeriodicTest n) (v : gradientClosure μ) :
    ⟪periodicGradientMap μ f,v⟫_ℝ =
      ∫ x, ⟪gradient (pullback f.val) x,(v : Lp (Point n) 2 μ) x⟫_ℝ ∂μ := by
  change ⟪(gradientVector μ f.val f.property.1 f.property.2).val,v.val⟫_ℝ = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [gradientVector_ae μ f.val f.property.1 f.property.2] with x hx
  rw [hx]

/-- A literal periodic divergence pairing, not an assumed smooth optimizer. -/
theorem representative_divergence (σ : Test n →ₗ[ℝ] ℝ) (f : SmoothPeriodicTest n) :
    source μ σ f = ∫ x, ⟪gradient (pullback f.val) x,
      ((representative μ σ : gradientClosure μ) : Lp (Point n) 2 μ) x⟫_ℝ ∂μ := by
  rw [← gradientVector_pairing,← representative_pairing]
  exact real_inner_comm _ _

/-- Any actual representing flux gives the same periodic test action. -/
theorem source_eq_flux_pairing (σ : Test n →ₗ[ℝ] ℝ) (v : Lp (Point n) 2 μ)
    (hv : ∀ φ : Test n, σ φ = ∫ x,⟪gradient (φ : Point n → ℝ) x,v x⟫_ℝ ∂μ)
    (f : SmoothPeriodicTest n) :
    source μ σ f = ∫ x,⟪gradient (pullback f.val) x,v x⟫_ℝ ∂μ := by
  have ho := flux_residual_orthogonal μ σ v hv (periodicGradientMap μ f)
  rw [inner_sub_left] at ho
  rw [source_eq_full_pairing]
  change ⟪(WeightedTangent.representative μ σ).val,(periodicGradientMap μ f).val⟫_ℝ = _
  rw [← sub_eq_zero.mp ho,real_inner_comm,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [gradientVector_ae μ f.val f.property.1 f.property.2] with x hx
  change ⟪(gradientVector μ f.val f.property.1 f.property.2).val x,v x⟫_ℝ = _
  rw [hx]

/-- The periodic action is the limit of the original distribution evaluated
on actual compact smooth cutoff tests. -/
theorem exists_compact_source_approximation (σ : Test n →ₗ[ℝ] ℝ)
    (hσ : FiniteEnergy μ σ) (f : SmoothPeriodicTest n) :
    ∃ φ : ℕ → Test n, Tendsto (fun j => σ (φ j)) atTop (𝓝 (source μ σ f)) := by
  obtain ⟨φ,hφ⟩ := exists_test_gradient_tendsto μ (pullback f.val)
    (f.property.1.comp (coordinateEquiv n).contDiff)
    (pullback_value_bound f.val f.property.1 f.property.2)
    (pullback_gradient_bound f.val f.property.1 f.property.2)
    (periodic_gradient_memLp μ f.val f.property.1 f.property.2)
  refine ⟨φ,?_⟩
  have h := tendsto_const_nhds.inner hφ (𝕜 := ℝ)
    (f := fun _ : ℕ => (WeightedTangent.representative μ σ : Lp (Point n) 2 μ))
  rw [source_eq_full_pairing]
  change Tendsto (fun j => σ (φ j)) atTop
    (𝓝 ⟪(WeightedTangent.representative μ σ).val,
      (periodic_gradient_memLp μ f.val f.property.1 f.property.2).toLp (gradient (pullback f.val))⟫_ℝ)
  convert h using 1
  funext j
  rw [WeightedTangent.representative_divergence μ σ hσ (φ j),gradient_pairing_eq_inner,
    real_inner_comm]

/-- The periodic variational objective uses the genuine gradient integral. -/
def objective (σ : Test n →ₗ[ℝ] ℝ) (f : SmoothPeriodicTest n) : ℝ :=
  2*source μ σ f-∫ x,‖gradient (pullback f.val) x‖^2 ∂μ

def energy (σ : Test n →ₗ[ℝ] ℝ) : ℝ := sSup (Set.range (objective μ σ))

theorem gradient_norm_sq (f : SmoothPeriodicTest n) :
    ‖gradientIntoPeriodic μ f‖^2 = ∫ x,‖gradient (pullback f.val) x‖^2 ∂μ := by
  change ‖(gradientVector μ f.val f.property.1 f.property.2).val‖^2 = _
  rw [lp_norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [gradientVector_ae μ f.val f.property.1 f.property.2] with x hx
  rw [hx]

theorem objective_eq_dense (σ : Test n →ₗ[ℝ] ℝ) :
    objective μ σ = DenseVariational.objective (H := periodicSpace μ) (source μ σ) (gradientIntoPeriodic μ) := by
  funext f
  simp only [objective,DenseVariational.objective,gradient_norm_sq]

theorem objective_bddAbove (σ : Test n →ₗ[ℝ] ℝ) : BddAbove (Set.range (objective μ σ)) := by
  refine ⟨‖representative μ σ‖^2,?_⟩
  rintro y ⟨f,rfl⟩
  rw [objective_eq_dense]
  unfold DenseVariational.objective
  rw [← representative_pairing]
  nlinarith [norm_sub_sq_real (representative μ σ) (gradientIntoPeriodic μ f),
    sq_nonneg ‖representative μ σ-gradientIntoPeriodic μ f‖]

/-- Exact periodic variational energy with a genuine dense test space. -/
theorem energy_eq_norm_sq (σ : Test n →ₗ[ℝ] ℝ) : energy μ σ = ‖representative μ σ‖^2 := by
  apply IsLUB.csSup_eq _ (Set.range_nonempty _)
  constructor
  · rintro y ⟨f,rfl⟩
    rw [objective_eq_dense]
    unfold DenseVariational.objective
    rw [← representative_pairing]
    nlinarith [norm_sub_sq_real (representative μ σ) (gradientIntoPeriodic μ f),
      sq_nonneg ‖representative μ σ-gradientIntoPeriodic μ f‖]
  · intro C hC
    have hb (w : periodicSpace μ) : 2*⟪representative μ σ,w⟫_ℝ-‖w‖^2 ≤ C := by
      refine (dense_gradientIntoPeriodic μ).induction_on w
        (isClosed_le (by fun_prop) continuous_const) ?_
      intro f
      rw [representative_pairing,gradient_norm_sq]
      exact hC ⟨f,rfl⟩
    have he := hb (representative μ σ)
    rw [real_inner_self_eq_norm_sq] at he
    linarith

/-- Periodic testing can only decrease the full Euclidean tangent energy. -/
theorem energy_le_full (σ : Test n →ₗ[ℝ] ℝ) (hσ : FiniteEnergy μ σ) :
    energy μ σ ≤ WeightedTangent.energy μ σ := by
  rw [energy_eq_norm_sq,WeightedTangent.energy_eq_norm_sq μ σ hσ]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    ((periodicSpace μ).norm_orthogonalProjectionOnto_apply_le _)

theorem energy_eq_integral (σ : Test n →ₗ[ℝ] ℝ) :
    energy μ σ = ∫ x,‖((representative μ σ : gradientClosure μ) : Lp (Point n) 2 μ) x‖^2 ∂μ := by
  rw [energy_eq_norm_sq]
  exact lp_norm_sq_eq_integral μ ((representative μ σ : gradientClosure μ) : Lp (Point n) 2 μ)

/-- Exact full-to-periodic energy loss, retaining the literal L² residual. -/
theorem full_energy_increment (σ : Test n →ₗ[ℝ] ℝ) (hσ : FiniteEnergy μ σ) :
    WeightedTangent.energy μ σ-energy μ σ =
      ∫ x,‖(WeightedTangent.representative μ σ : Lp (Point n) 2 μ) x-
        ((representative μ σ : gradientClosure μ) : Lp (Point n) 2 μ) x‖^2 ∂μ := by
  rw [WeightedTangent.energy_eq_norm_sq μ σ hσ,energy_eq_norm_sq]
  have h := TangentEnergy.projection_energy_increment (periodicSpace μ)
    (WeightedTangent.representative μ σ)
  change ‖WeightedTangent.representative μ σ‖^2-‖representative μ σ‖^2 =
    ‖WeightedTangent.representative μ σ-(representative μ σ : gradientClosure μ)‖^2 at h
  rw [h]
  change ‖(WeightedTangent.representative μ σ).val-(representative μ σ).val.val‖^2 = _
  rw [lp_norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (WeightedTangent.representative μ σ).val
    (representative μ σ).val.val] with x hx
  rw [hx]
  rfl

end SharpWasserstein.WeightedPeriodicTangent
