import SharpWasserstein.WeightedPeriodicTangentPhysical
import SharpWasserstein.WeightedPeriodicMarginal
import SharpWasserstein.PeriodicMarginalLift

/-! Actual prefix lifting between physical-period tangent spaces for arbitrary finite
carrying measures, and the exact energy increment of genuine source marginals. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace
namespace SharpWasserstein.WeightedPeriodicMarginalPhysical
open WeightedTangent WeightedMarginal PeriodicIntegrationByParts PeriodicBochner
open PeriodicSmoothGradient (SmoothPeriodicTest)
open WeightedPeriodicFourierPhysical
open PeriodicConvolution (prefixCoords)
variable {n m : ℕ}

open WeightedPeriodicMarginal (liftTest)

variable [MeasurableSpace (Point n)] [BorelSpace (Point n)]
  [MeasurableSpace (Point (n+m))] [BorelSpace (Point (n+m))]
variable (P : ℝ) (μ : Measure (Point (n+m))) [IsFiniteMeasure μ]

/-- Prefix lifting is exactly the gradient of the actual periodic cylinder test. -/
theorem tangentLift_gradientVector (f : Coordinates n → ℝ)
    (hf : ContDiff ℝ ∞ f) (hp : Periodic f) :
    tangentLift μ (gradientVector P (marginalLaw μ) f hf hp) =
      gradientVector P μ (f ∘ prefixCoords n m) (hf.comp (PeriodicMarginalLift.prefix_smooth n m))
        (PeriodicMarginalLift.prefix_periodic hp) := by
  apply Subtype.ext
  apply Lp.ext
  have hl := ae_of_ae_map (prefixProjection n m).continuous.measurable.aemeasurable
    (gradientVector_ae P (marginalLaw μ) f hf hp)
  filter_upwards [vectorLiftLinear_ae μ (gradientVector P (marginalLaw μ) f hf hp).val,hl,
    gradientVector_ae P μ (f ∘ prefixCoords n m) (hf.comp (PeriodicMarginalLift.prefix_smooth n m))
      (PeriodicMarginalLift.prefix_periodic hp)] with x ha hb hc
  change vectorLiftLinear μ (gradientVector P (marginalLaw μ) f hf hp).val x = _
  rw [ha,hb,hc]
  exact (gradient_comp_prefixProjection
    ((physicalPotential_smooth P hf).differentiable (by simp)) x).symm

/-- The actual isometric marginal tangent lift preserves the weighted periodic closure. -/
theorem tangentLift_periodic_mem (w : periodicSpace P (marginalLaw μ)) :
    tangentLift μ (w : gradientClosure (marginalLaw μ)) ∈ periodicSpace P μ := by
  have hle : periodicSpace P (marginalLaw μ) ≤
      (periodicSpace P μ).comap (tangentLift μ).toLinearMap := by
    rw [periodicSpace_eq_smoothGradientClosure]
    apply Submodule.topologicalClosure_minimal
    · rintro v ⟨f,rfl⟩
      change tangentLift μ (gradientVector P (marginalLaw μ) f.val f.property.1 f.property.2) ∈ periodicSpace P μ
      rw [tangentLift_gradientVector]
      exact gradientVector_mem_periodicSpace P μ _ _ (PeriodicMarginalLift.prefix_periodic f.property.2)
    · exact (iSup (trialSpace P μ)).isClosed_topologicalClosure.preimage (tangentLift μ).continuous
  exact hle w.property

/-- Genuine periodic marginal lifting, with the exact Euclidean L² norm. -/
def periodicLift : periodicSpace P (marginalLaw μ) →ₗᵢ[ℝ] periodicSpace P μ where
  toFun w := ⟨tangentLift μ w,tangentLift_periodic_mem P μ w⟩
  map_add' _ _ := by apply Subtype.ext; exact map_add (tangentLift μ) _ _
  map_smul' _ _ := by apply Subtype.ext; exact map_smul (tangentLift μ) _ _
  norm_map' w := (tangentLift μ).norm_map w

theorem periodicLift_ae (w : periodicSpace P (marginalLaw μ)) :
    ((periodicLift P μ w : gradientClosure μ) : Lp (Point (n+m)) 2 μ) =ᵐ[μ]
      fun x => prefixEmbedding n m
        (((w : gradientClosure (marginalLaw μ)) : Lp (Point n) 2 (marginalLaw μ))
          (prefixProjection n m x)) :=
  vectorLiftLinear_ae μ _

omit [MeasurableSpace (Point n)] [BorelSpace (Point n)] in
/-- Closed-space pairings of the actual periodic representative retain the
original distributional action. -/
theorem representative_closed_pairing (σ : Test (n+m) →ₗ[ℝ] ℝ) (w : periodicSpace P μ) :
    ⟪WeightedPeriodicTangentPhysical.representative P μ σ,w⟫_ℝ =
      ⟪WeightedTangent.representative μ σ,(w : gradientClosure μ)⟫_ℝ :=
  Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right w _

/-- Actual source marginalization commutes with restriction to periodic tests. -/
theorem source_liftTest (σ : Test (n+m) →ₗ[ℝ] ℝ) (f : SmoothPeriodicTest n) :
    WeightedPeriodicTangentPhysical.source P (marginalLaw μ) (marginalDistribution μ σ) f =
      WeightedPeriodicTangentPhysical.source P μ σ (liftTest (m := m) f) := by
  rw [WeightedPeriodicTangentPhysical.source_eq_full_pairing,WeightedPeriodicTangentPhysical.source_eq_full_pairing]
  have hp := WeightedMarginal.marginal_representative_pairing μ σ (periodicGradientMap P (marginalLaw μ) f)
  change ⟪WeightedTangent.representative μ σ,
      tangentLift μ (periodicGradientMap P (marginalLaw μ) f)⟫_ℝ =
    ⟪WeightedTangent.representative (marginalLaw μ) (marginalDistribution μ σ),
      periodicGradientMap P (marginalLaw μ) f⟫_ℝ at hp
  rw [← hp]
  congr 1
  exact tangentLift_gradientVector P μ f.val f.property.1 f.property.2

/-- Consistency is derived for the actual periodic representatives and true
pushforward marginal, with no assumed orthogonality identity. -/
theorem marginal_representative_pairing (σ : Test (n+m) →ₗ[ℝ] ℝ)
    (w : periodicSpace P (marginalLaw μ)) :
    ⟪WeightedPeriodicTangentPhysical.representative P μ σ,periodicLift P μ w⟫_ℝ =
      ⟪WeightedPeriodicTangentPhysical.representative P (marginalLaw μ) (marginalDistribution μ σ),w⟫_ℝ := by
  rw [representative_closed_pairing]
  have hr : ⟪WeightedPeriodicTangentPhysical.representative P (marginalLaw μ) (marginalDistribution μ σ),w⟫_ℝ =
      ⟪WeightedTangent.representative (marginalLaw μ) (marginalDistribution μ σ),
        (w : gradientClosure (marginalLaw μ))⟫_ℝ :=
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right w _
  rw [hr]
  exact WeightedMarginal.marginal_representative_pairing μ σ w

/-- Exact periodic marginal energy increment, at arbitrary finite carrying laws. -/
theorem marginal_energy_increment (σ : Test (n+m) →ₗ[ℝ] ℝ) :
    WeightedPeriodicTangentPhysical.energy P μ σ -
      WeightedPeriodicTangentPhysical.energy P (marginalLaw μ) (marginalDistribution μ σ) =
    ‖WeightedPeriodicTangentPhysical.representative P μ σ-periodicLift P μ
      (WeightedPeriodicTangentPhysical.representative P (marginalLaw μ) (marginalDistribution μ σ))‖^2 := by
  rw [WeightedPeriodicTangentPhysical.energy_eq_norm_sq,WeightedPeriodicTangentPhysical.energy_eq_norm_sq]
  have hp := marginal_representative_pairing P μ σ
    (WeightedPeriodicTangentPhysical.representative P (marginalLaw μ) (marginalDistribution μ σ))
  rw [real_inner_self_eq_norm_sq] at hp
  rw [norm_sub_sq_real (WeightedPeriodicTangentPhysical.representative P μ σ)
    (periodicLift P μ (WeightedPeriodicTangentPhysical.representative P (marginalLaw μ) (marginalDistribution μ σ))),
    LinearIsometry.norm_map,hp]
  ring

/-- Literal full-minus-lifted fluctuation energy, with the true zero-extension
field and no loss from coordinate sup norms. -/
theorem marginal_energy_increment_integral (σ : Test (n+m) →ₗ[ℝ] ℝ) :
    WeightedPeriodicTangentPhysical.energy P μ σ -
      WeightedPeriodicTangentPhysical.energy P (marginalLaw μ) (marginalDistribution μ σ) =
    ∫ x, ‖((WeightedPeriodicTangentPhysical.representative P μ σ : gradientClosure μ) : Lp (Point (n+m)) 2 μ) x -
      prefixEmbedding n m (((WeightedPeriodicTangentPhysical.representative P (marginalLaw μ)
        (marginalDistribution μ σ) : gradientClosure (marginalLaw μ)) :
        Lp (Point n) 2 (marginalLaw μ)) (prefixProjection n m x))‖^2 ∂μ := by
  rw [marginal_energy_increment]
  let U := WeightedPeriodicTangentPhysical.representative P μ σ
  let u := WeightedPeriodicTangentPhysical.representative P (marginalLaw μ) (marginalDistribution μ σ)
  change ‖U.val.val-(periodicLift P μ u).val.val‖^2 = _
  rw [lp_norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub U.val.val (periodicLift P μ u).val.val,periodicLift_ae P μ u] with x hx hy
  rw [hx]
  simp only [Pi.sub_apply,hy]
  rfl

/-- Actual periodic marginalization decreases the variational energy. -/
theorem marginal_energy_le (σ : Test (n+m) →ₗ[ℝ] ℝ) :
    WeightedPeriodicTangentPhysical.energy P (marginalLaw μ) (marginalDistribution μ σ) ≤
      WeightedPeriodicTangentPhysical.energy P μ σ := by
  have h := marginal_energy_increment P μ σ
  linarith [sq_nonneg ‖WeightedPeriodicTangentPhysical.representative P μ σ-periodicLift P μ
    (WeightedPeriodicTangentPhysical.representative P (marginalLaw μ) (marginalDistribution μ σ))‖]

end SharpWasserstein.WeightedPeriodicMarginalPhysical
