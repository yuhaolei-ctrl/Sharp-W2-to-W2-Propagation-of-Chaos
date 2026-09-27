import SharpWasserstein.RoughEulerianSpaceTimeEquation
import SharpWasserstein.RoughEulerianTimeActionCurveEnergy
import SharpWasserstein.RoughEulerianTransportJointRegularity

/-! The actual jointly smoothed probability curve satisfies the coefficient-one
finite-action transport estimate. The original rough flux equation is the only
evolution premise; all smooth-curve regularity and action inputs are derived. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff InnerProductSpace ProbabilityTheory
namespace SharpWasserstein.RoughEulerianSmoothing
open WeightedTangent RoughEulerianTime RoughEulerianTransport
variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]

theorem spaceTimeRegularizedLaw_wassersteinSq_le {τ ε δ R T a b : ℝ}
    (hτ : 0 < τ) (hε : 0 < ε) (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    {μ : ℝ → ProbabilityMeasure (Point (N*d))} (hμ : Continuous μ)
    {U : ℝ × Point (N*d) → Point (N*d)}
    (hU : Integrable U ((volume.restrict (Icc 0 T)) ⊗ₘ probabilityCurveKernel μ hμ))
    (hU₂ : Integrable (fun z => ‖U z‖^2) ((volume.restrict (Icc 0 T)) ⊗ₘ probabilityCurveKernel μ hμ))
    (hρ : ∀ᵐ z ∂((volume.restrict (Icc 0 T)) ⊗ₘ probabilityCurveKernel μ hμ),‖z.2‖ ≤ R)
    (heq : ∀ ψ : Test (N*d),∀ r ∈ Icc 0 T,
      (∫ x,(ψ : Point (N*d) → ℝ) x ∂(μ r : Measure (Point (N*d))))-
        (∫ x,(ψ : Point (N*d) → ℝ) x ∂(μ 0 : Measure (Point (N*d)))) =
      ∫ s in 0..r,∫ x,⟪gradient (ψ : Point (N*d) → ℝ) x,U (s,x)⟫_ℝ ∂(μ s : Measure (Point (N*d))))
    (hab : a ≤ b) (ha : τ < a) (hb : b+τ < T) :
    let ρ := (volume.restrict (Icc 0 T)) ⊗ₘ probabilityCurveKernel μ hμ
    wassersteinSq
      ((spaceTimeRegularizedLaw τ hτ ε hε δ ρ a).map (configurationEuclidean d N).symm)
      ((spaceTimeRegularizedLaw τ hτ ε hε δ ρ b).map (configurationEuclidean d N).symm) ≤
      ENNReal.ofReal ((b-a)*((1-δ)*∫ z,‖U z‖^2 ∂ρ)) := by
  dsimp only
  let κ := probabilityCurveKernel μ hμ
  let ρ := (volume.restrict (Icc 0 T)) ⊗ₘ κ
  let ν := spaceTimeProbabilityCurve hτ hε hδ hδ₁ κ hab ha.le hb.le
  let f := floorVelocity (1-δ) (spaceTimeDensity τ hτ ε hε ρ)
    (fun p => δ*gaussianFloor p.2) (spaceTimeFlux τ hτ ε hε ρ U)
  let v := fun t x => f (a+t,x)
  have hc : EuclideanCompactWeakContinuity v ν (b-a) := by
    refine ⟨spaceTimeProbabilityCurve_continuous hτ hε hδ hδ₁ κ hab ha.le hb.le hρ,?_⟩
    intro φ p hp q hq
    exact spaceTimeProbabilityCurve_equation hτ hε hδ hδ₁ hμ hU heq hab ha hb φ hp hq
  obtain ⟨M,K,K₁,hM,hK,hs,hBs,hK₁⟩ :=
    spaceTimeFloorVelocity_spatial_regular hτ hε hδ hδ₁ ρ (compProd_norm_le κ hρ) hU
  have hvc : Continuous (Function.uncurry v) :=
    (spaceTimeFloorVelocity_smooth hτ hε hδ hδ₁ ρ hU).continuous.comp
      ((continuous_const.add continuous_fst).prodMk continuous_snd)
  have hp : HasSecondMoment ((ν 0 : Measure (Point (N*d))).map (configurationEuclidean d N).symm) :=
    hasSecondMoment_configuration_of_quadratic _
      (spaceTimeProbabilityCurve_quadratic hτ hε hδ hδ₁ κ hab ha.le hb.le hρ 0).1
  obtain ⟨hEi,hEle⟩ := spaceTimeProbabilityCurve_action hτ hε hδ hδ₁ κ hab ha.le hb.le hU hU₂
  have hcost := hc.wassersteinSq_le_finiteAction hvc (fun t x => hM (a+t) x)
    (fun t => hK (a+t)) (sub_nonneg.mpr hab) (fun t => hs (a+t))
    (fun t => hBs (a+t)) (fun t => hK₁ (a+t)) hp
    (a := 0) (b := b-a) ⟨le_rfl,sub_nonneg.mpr hab⟩ ⟨sub_nonneg.mpr hab,le_rfl⟩
    (sub_nonneg.mpr hab) hEi (Eventually.of_forall fun _ => le_rfl)
  have hzero : (ν 0 : Measure (Point (N*d))) = spaceTimeRegularizedLaw τ hτ ε hε δ ρ a := by
    simpa only [add_zero] using spaceTimeProbabilityCurve_coe hτ hε hδ hδ₁ κ hab ha.le hb.le
      (t := 0) ⟨le_rfl,sub_nonneg.mpr hab⟩
  have hend : (ν (b-a) : Measure (Point (N*d))) = spaceTimeRegularizedLaw τ hτ ε hε δ ρ b := by
    simpa only [add_sub_cancel] using spaceTimeProbabilityCurve_coe hτ hε hδ hδ₁ κ hab ha.le hb.le
      (t := b-a) ⟨sub_nonneg.mpr hab,le_rfl⟩
  rw [hzero,hend] at hcost
  apply hcost.trans
  apply ENNReal.ofReal_le_ofReal
  simpa only [sub_zero] using mul_le_mul_of_nonneg_left hEle (sub_nonneg.mpr hab)

end SharpWasserstein.RoughEulerianSmoothing
