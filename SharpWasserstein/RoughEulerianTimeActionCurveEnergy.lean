module

public import SharpWasserstein.Compat
public import SharpWasserstein.RoughEulerianTimeActionCurve
public import SharpWasserstein.RoughEulerianTransportRegularCoordinates

@[expose] public section

/-! Exact local-time action and genuine configuration second moments for the
constructed clamped smoothing curve. These are the quantitative inputs of
the regular continuity-equation transport theorem. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff ProbabilityTheory
namespace SharpWasserstein.RoughEulerianSmoothing
open WeightedTangent RoughEulerianTime
variable {d : ℕ} [MeasurableSpace (Point d)] [BorelSpace (Point d)]

/-- The local-time action is the translated original action, so its integral
retains the exact contraction coefficient. -/
theorem spaceTimeProbabilityCurve_action {τ ε δ a b T : ℝ} (hτ : 0 < τ) (hε : 0 < ε)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (κ : Kernel ℝ (Point d)) [IsMarkovKernel κ]
    (hab : a ≤ b) (ha : τ ≤ a) (hb : b+τ ≤ T)
    {U : ℝ × Point d → Point d}
    (hU : Integrable U ((volume.restrict (Icc 0 T)) ⊗ₘ κ))
    (hU₂ : Integrable (fun z => ‖U z‖^2) ((volume.restrict (Icc 0 T)) ⊗ₘ κ)) :
    let ρ := (volume.restrict (Icc 0 T)) ⊗ₘ κ
    let f := floorVelocity (1-δ) (spaceTimeDensity τ hτ ε hε ρ)
      (fun p => δ*gaussianFloor p.2) (spaceTimeFlux τ hτ ε hε ρ U)
    let E := fun t => ∫ x,‖f (a+t,x)‖^2
      ∂(spaceTimeProbabilityCurve hτ hε hδ hδ₁ κ hab ha hb t : Measure (Point d))
    IntervalIntegrable E volume 0 (b-a) ∧
      (∫ t in 0..(b-a),E t) ≤ (1-δ)*∫ z,‖U z‖^2 ∂ρ := by
  dsimp only
  let ρ := (volume.restrict (Icc 0 T)) ⊗ₘ κ
  let f := floorVelocity (1-δ) (spaceTimeDensity τ hτ ε hε ρ)
    (fun p => δ*gaussianFloor p.2) (spaceTimeFlux τ hτ ε hε ρ U)
  let e := fun t => ∫ x,‖f (t,x)‖^2 ∂spaceTimeRegularizedLaw τ hτ ε hε δ ρ t
  let E := fun t => ∫ x,‖f (a+t,x)‖^2
    ∂(spaceTimeProbabilityCurve hτ hε hδ hδ₁ κ hab ha hb t : Measure (Point d))
  have heq : EqOn E (fun t => e (a+t)) (Icc 0 (b-a)) := by
    intro t ht
    dsimp [E,e]
    rw [spaceTimeProbabilityCurve_coe hτ hε hδ hδ₁ κ hab ha hb ht]
  have heraw : IntervalIntegrable e volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (spaceTimeRegularizedLaw_action_integrable_and_le hτ hε hδ hδ₁ ρ hU hU₂ (Icc a b)).1
  have hshift : IntervalIntegrable (fun t => e (a+t)) volume 0 (b-a) := by
    simpa only [sub_self] using heraw.comp_add_left a
  have hi : IntervalIntegrable E volume 0 (b-a) := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le (sub_nonneg.mpr hab)).mpr
    apply ((intervalIntegrable_iff_integrableOn_Icc_of_le (sub_nonneg.mpr hab)).mp hshift).congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (heq ht).symm
  refine ⟨hi,?_⟩
  calc
    (∫ t in 0..(b-a),E t) = ∫ t in 0..(b-a),e (a+t) :=
      intervalIntegral.integral_congr (by simpa only [uIcc_of_le (sub_nonneg.mpr hab)] using heq)
    _ = ∫ t in a..b,e t := by
      rw [intervalIntegral.integral_comp_add_left]
      simp only [add_zero,add_sub_cancel]
    _ ≤ _ := by
      rw [intervalIntegral.integral_of_le hab]
      exact (spaceTimeRegularizedLaw_action_integrable_and_le hτ hε hδ hδ₁ ρ hU hU₂ (Ioc a b)).2

omit [BorelSpace (Point d)] in
/-- Compact carrying support in space combines with the actual finite time
window to give bounded support of the one joint input measure. -/
theorem compProd_norm_le {T R : ℝ} (κ : Kernel ℝ (Point d))
    (hρ : ∀ᵐ z ∂((volume.restrict (Icc 0 T)) ⊗ₘ κ),‖z.2‖ ≤ R) :
    ∀ᵐ z ∂((volume.restrict (Icc 0 T)) ⊗ₘ κ),‖z‖ ≤ max |T| R := by
  have ht : ∀ᵐ z ∂((volume.restrict (Icc 0 T)) ⊗ₘ κ), z.1 ∈ Icc 0 T :=
    Measure.ae_compProd_of_ae_fst κ measurableSet_Icc (ae_restrict_mem measurableSet_Icc)
  filter_upwards [ht,hρ] with z hz hR
  have hz' : ‖z.1‖ ≤ |T| := by
    rw [Real.norm_eq_abs,abs_of_nonneg hz.1]
    exact hz.2.trans (le_abs_self T)
  exact max_le_max hz' hR

end SharpWasserstein.RoughEulerianSmoothing

namespace SharpWasserstein.RoughEulerianSmoothing
open WeightedTangent
variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]

/-- The Euclidean moment is exactly the manuscript's unnormalized
configuration second moment after the actual coordinate isomorphism. -/
theorem hasSecondMoment_configuration_of_quadratic (μ : Measure (Point (N*d)))
    (hμ : Integrable (fun x => ‖x‖^2) μ) :
    HasSecondMoment (μ.map (configurationEuclidean d N).symm) := by
  apply (hasSecondMoment_iff_integrable _).mpr
  apply (integrable_map_measure
    (measurable_productCost.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    (configurationEuclidean d N).symm.continuous.measurable.aemeasurable).mpr
  have he (x : Point (N*d)) : productCost ((configurationEuclidean d N).symm x) 0 = ‖x‖^2 := by
    have hh := configurationEuclidean_norm_sq ((configurationEuclidean d N).symm x)
    simpa only [ContinuousLinearEquiv.apply_symm_apply,productCost,Pi.zero_apply,sub_zero] using hh.symm
  change Integrable (fun x : Point (N*d) => productCost ((configurationEuclidean d N).symm x) 0) μ
  simpa only [he] using hμ

end SharpWasserstein.RoughEulerianSmoothing
