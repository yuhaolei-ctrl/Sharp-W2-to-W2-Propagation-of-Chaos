import SharpWasserstein.WeightedPeriodicTangent
import SharpWasserstein.PeriodicMarginalLift

/-! Actual prefix lifting between periodic tangent spaces for arbitrary finite
carrying measures, and the exact energy increment of genuine source marginals. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace
namespace SharpWasserstein.WeightedPeriodicMarginal
open WeightedTangent WeightedMarginal PeriodicIntegrationByParts PeriodicBochner
open PeriodicSmoothGradient (SmoothPeriodicTest)
open WeightedPeriodicFourier
open PeriodicConvolution (prefixCoords)
variable {n m : ℕ}

/-- A genuine smooth periodic cylinder test, constant in the remaining coordinates. -/
def liftTest : SmoothPeriodicTest n →ₗ[ℝ] SmoothPeriodicTest (n+m) where
  toFun f := ⟨f.val ∘ prefixCoords n m,f.property.1.comp (PeriodicMarginalLift.prefix_smooth n m),
    PeriodicMarginalLift.prefix_periodic f.property.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable [MeasurableSpace (Point n)] [BorelSpace (Point n)]
  [MeasurableSpace (Point (n+m))] [BorelSpace (Point (n+m))]
variable (μ : Measure (Point (n+m))) [IsFiniteMeasure μ]

/-- Prefix lifting is exactly the gradient of the actual periodic cylinder test. -/
theorem tangentLift_gradientVector (f : Coordinates n → ℝ)
    (hf : ContDiff ℝ ∞ f) (hp : Periodic f) :
    tangentLift μ (gradientVector (marginalLaw μ) f hf hp) =
      gradientVector μ (f ∘ prefixCoords n m) (hf.comp (PeriodicMarginalLift.prefix_smooth n m))
        (PeriodicMarginalLift.prefix_periodic hp) := by
  apply Subtype.ext
  apply Lp.ext
  have hl := ae_of_ae_map (prefixProjection n m).continuous.measurable.aemeasurable
    (gradientVector_ae (marginalLaw μ) f hf hp)
  filter_upwards [vectorLiftLinear_ae μ (gradientVector (marginalLaw μ) f hf hp).val,hl,
    gradientVector_ae μ (f ∘ prefixCoords n m) (hf.comp (PeriodicMarginalLift.prefix_smooth n m))
      (PeriodicMarginalLift.prefix_periodic hp)] with x ha hb hc
  change vectorLiftLinear μ (gradientVector (marginalLaw μ) f hf hp).val x = _
  rw [ha,hb,hc]
  exact (gradient_comp_prefixProjection
    ((hf.comp (coordinateEquiv n).contDiff).differentiable (by simp)) x).symm

/-- The actual isometric marginal tangent lift preserves the weighted periodic closure. -/
theorem tangentLift_periodic_mem (w : periodicSpace (marginalLaw μ)) :
    tangentLift μ (w : gradientClosure (marginalLaw μ)) ∈ periodicSpace μ := by
  have hle : periodicSpace (marginalLaw μ) ≤
      (periodicSpace μ).comap (tangentLift μ).toLinearMap := by
    rw [periodicSpace_eq_smoothGradientClosure]
    apply Submodule.topologicalClosure_minimal
    · rintro v ⟨f,rfl⟩
      change tangentLift μ (gradientVector (marginalLaw μ) f.val f.property.1 f.property.2) ∈ periodicSpace μ
      rw [tangentLift_gradientVector]
      exact gradientVector_mem_periodicSpace μ _ _ (PeriodicMarginalLift.prefix_periodic f.property.2)
    · exact (iSup (trialSpace μ)).isClosed_topologicalClosure.preimage (tangentLift μ).continuous
  exact hle w.property

/-- Genuine periodic marginal lifting, with the exact Euclidean L² norm. -/
def periodicLift : periodicSpace (marginalLaw μ) →ₗᵢ[ℝ] periodicSpace μ where
  toFun w := ⟨tangentLift μ w,tangentLift_periodic_mem μ w⟩
  map_add' _ _ := by apply Subtype.ext; exact map_add (tangentLift μ) _ _
  map_smul' _ _ := by apply Subtype.ext; exact map_smul (tangentLift μ) _ _
  norm_map' w := (tangentLift μ).norm_map w

theorem periodicLift_ae (w : periodicSpace (marginalLaw μ)) :
    ((periodicLift μ w : gradientClosure μ) : Lp (Point (n+m)) 2 μ) =ᵐ[μ]
      fun x => prefixEmbedding n m
        (((w : gradientClosure (marginalLaw μ)) : Lp (Point n) 2 (marginalLaw μ))
          (prefixProjection n m x)) :=
  vectorLiftLinear_ae μ _

omit [MeasurableSpace (Point n)] [BorelSpace (Point n)] in
/-- Closed-space pairings of the actual periodic representative retain the
original distributional action. -/
theorem representative_closed_pairing (σ : Test (n+m) →ₗ[ℝ] ℝ) (w : periodicSpace μ) :
    ⟪WeightedPeriodicTangent.representative μ σ,w⟫_ℝ =
      ⟪WeightedTangent.representative μ σ,(w : gradientClosure μ)⟫_ℝ :=
  Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right w _

/-- Actual source marginalization commutes with restriction to periodic tests. -/
theorem source_liftTest (σ : Test (n+m) →ₗ[ℝ] ℝ) (f : SmoothPeriodicTest n) :
    WeightedPeriodicTangent.source (marginalLaw μ) (marginalDistribution μ σ) f =
      WeightedPeriodicTangent.source μ σ (liftTest (m := m) f) := by
  rw [WeightedPeriodicTangent.source_eq_full_pairing,WeightedPeriodicTangent.source_eq_full_pairing]
  have hp := marginal_representative_pairing μ σ (periodicGradientMap (marginalLaw μ) f)
  change ⟪WeightedTangent.representative μ σ,
      tangentLift μ (periodicGradientMap (marginalLaw μ) f)⟫_ℝ =
    ⟪WeightedTangent.representative (marginalLaw μ) (marginalDistribution μ σ),
      periodicGradientMap (marginalLaw μ) f⟫_ℝ at hp
  rw [← hp]
  congr 1
  exact tangentLift_gradientVector μ f.val f.property.1 f.property.2

/-- Consistency is derived for the actual periodic representatives and true
pushforward marginal, with no assumed orthogonality identity. -/
theorem marginal_representative_pairing (σ : Test (n+m) →ₗ[ℝ] ℝ)
    (w : periodicSpace (marginalLaw μ)) :
    ⟪WeightedPeriodicTangent.representative μ σ,periodicLift μ w⟫_ℝ =
      ⟪WeightedPeriodicTangent.representative (marginalLaw μ) (marginalDistribution μ σ),w⟫_ℝ := by
  rw [representative_closed_pairing]
  have hr : ⟪WeightedPeriodicTangent.representative (marginalLaw μ) (marginalDistribution μ σ),w⟫_ℝ =
      ⟪WeightedTangent.representative (marginalLaw μ) (marginalDistribution μ σ),
        (w : gradientClosure (marginalLaw μ))⟫_ℝ :=
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right w _
  rw [hr]
  exact WeightedMarginal.marginal_representative_pairing μ σ w

/-- Exact periodic marginal energy increment, at arbitrary finite carrying laws. -/
theorem marginal_energy_increment (σ : Test (n+m) →ₗ[ℝ] ℝ) :
    WeightedPeriodicTangent.energy μ σ -
      WeightedPeriodicTangent.energy (marginalLaw μ) (marginalDistribution μ σ) =
    ‖WeightedPeriodicTangent.representative μ σ-periodicLift μ
      (WeightedPeriodicTangent.representative (marginalLaw μ) (marginalDistribution μ σ))‖^2 := by
  rw [WeightedPeriodicTangent.energy_eq_norm_sq,WeightedPeriodicTangent.energy_eq_norm_sq]
  have hp := marginal_representative_pairing μ σ
    (WeightedPeriodicTangent.representative (marginalLaw μ) (marginalDistribution μ σ))
  rw [real_inner_self_eq_norm_sq] at hp
  rw [norm_sub_sq_real (WeightedPeriodicTangent.representative μ σ)
    (periodicLift μ (WeightedPeriodicTangent.representative (marginalLaw μ) (marginalDistribution μ σ))),
    LinearIsometry.norm_map,hp]
  ring

/-- Literal full-minus-lifted fluctuation energy, with the true zero-extension
field and no loss from coordinate sup norms. -/
theorem marginal_energy_increment_integral (σ : Test (n+m) →ₗ[ℝ] ℝ) :
    WeightedPeriodicTangent.energy μ σ -
      WeightedPeriodicTangent.energy (marginalLaw μ) (marginalDistribution μ σ) =
    ∫ x, ‖((WeightedPeriodicTangent.representative μ σ : gradientClosure μ) : Lp (Point (n+m)) 2 μ) x -
      prefixEmbedding n m (((WeightedPeriodicTangent.representative (marginalLaw μ)
        (marginalDistribution μ σ) : gradientClosure (marginalLaw μ)) :
        Lp (Point n) 2 (marginalLaw μ)) (prefixProjection n m x))‖^2 ∂μ := by
  rw [marginal_energy_increment]
  let U := WeightedPeriodicTangent.representative μ σ
  let u := WeightedPeriodicTangent.representative (marginalLaw μ) (marginalDistribution μ σ)
  change ‖U.val.val-(periodicLift μ u).val.val‖^2 = _
  rw [lp_norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub U.val.val (periodicLift μ u).val.val,periodicLift_ae μ u] with x hx hy
  rw [hx]
  simp only [Pi.sub_apply,hy]
  rfl

/-- Actual periodic marginalization decreases the variational energy. -/
theorem marginal_energy_le (σ : Test (n+m) →ₗ[ℝ] ℝ) :
    WeightedPeriodicTangent.energy (marginalLaw μ) (marginalDistribution μ σ) ≤
      WeightedPeriodicTangent.energy μ σ := by
  have h := marginal_energy_increment μ σ
  linarith [sq_nonneg ‖WeightedPeriodicTangent.representative μ σ-periodicLift μ
    (WeightedPeriodicTangent.representative (marginalLaw μ) (marginalDistribution μ σ))‖]

end SharpWasserstein.WeightedPeriodicMarginal
