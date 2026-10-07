module

public import SharpWasserstein.Compat
public import SharpWasserstein.RoughEulerianSpaceTimePairing
public import SharpWasserstein.RoughEulerianTimeActionCurve
public import SharpWasserstein.RoughEulerianTransportRegularCoordinates

@[expose] public section

/-! The actual time-space convolution and stationary floor satisfy the
compact-test continuity equation. The original input is only the integrated
rough flux equation, and the derivative of the regularized law is derived. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff InnerProductSpace Interval ProbabilityTheory
namespace SharpWasserstein.RoughEulerianSmoothing
open WeightedTangent RoughEulerianTime RoughEulerianTransport
variable {d : ℕ} [MeasurableSpace (Point d)] [BorelSpace (Point d)]

def spaceTimeVelocity (τ : ℝ) (hτ : 0 < τ) (ε : ℝ) (hε : 0 < ε) (δ : ℝ)
    (ρ : Measure (ℝ × Point d)) (U : ℝ × Point d → Point d) (t : ℝ) (x : Point d) : Point d :=
  floorVelocity (1-δ) (spaceTimeDensity τ hτ ε hε ρ) (fun p => δ*gaussianFloor p.2)
    (spaceTimeFlux τ hτ ε hε ρ U) (t,x)

theorem joint_gradient_pairing_integrable (ρ : Measure (ℝ × Point d))
    {U : ℝ × Point d → Point d} (hU : Integrable U ρ) (φ : Test d) :
    Integrable (fun z => ⟪gradient (φ : Point d → ℝ) z.2,U z⟫_ℝ) ρ := by
  obtain ⟨M,hM⟩ := (compactSupport_test_gradient φ).exists_bound_of_continuous (continuous_test_gradient φ)
  apply (hU.norm.const_mul M).mono'
    (((continuous_test_gradient φ).comp continuous_snd).aestronglyMeasurable.inner hU.aestronglyMeasurable)
  exact Eventually.of_forall fun z => (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _))

theorem spaceTimeRegularizedLaw_flux_continuous {τ ε δ : ℝ}
    (hτ : 0 < τ) (hε : 0 < ε) (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (ρ : Measure (ℝ × Point d)) [IsFiniteMeasure ρ]
    {U : ℝ × Point d → Point d} (hU : Integrable U ρ) (φ : Test d) :
    Continuous (fun t => ∫ x,⟪gradient (φ : Point d → ℝ) x,spaceTimeVelocity τ hτ ε hε δ ρ U t x⟫_ℝ
      ∂spaceTimeRegularizedLaw τ hτ ε hε δ ρ t) := by
  change Continuous (fun t => ∫ x,⟪gradient (φ : Point d → ℝ) x,
    floorVelocity (1-δ) _ _ _ (t,x)⟫_ℝ ∂spaceTimeRegularizedLaw τ hτ ε hε δ ρ t)
  simp_rw [spaceTimeRegularizedLaw_flux_pairing hτ hε hδ hδ₁ ρ hU φ]
  apply continuous_const.mul
  obtain ⟨C,D,hC,hD⟩ := timeKernel_bounds hτ
  have hi := joint_gradient_pairing_integrable ρ hU (smoothTest ε hε φ)
  apply continuous_of_dominated (bound := fun z => C*‖⟪gradient (smoothTest ε hε φ : Point d → ℝ) z.2,U z⟫_ℝ‖)
  · intro t
    exact (time_weighted_joint_pairing_integrable hτ ρ hU (smoothTest ε hε φ) t).aestronglyMeasurable
  · intro t
    exact Eventually.of_forall fun z => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
  · exact hi.norm.const_mul C
  · exact Eventually.of_forall fun z =>
      ((timeKernel_smooth hτ).continuous.comp (continuous_id.sub continuous_const)).mul continuous_const

/-- The actual smoothed probability-law pairing has the derivative represented
by the actual smooth velocity. The only evolution premise is the original
integrated equation of the rough curve. -/
theorem spaceTimeRegularizedLaw_hasDerivAt {τ ε δ T t : ℝ}
    (hτ : 0 < τ) (hε : 0 < ε) (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    {μ : ℝ → ProbabilityMeasure (Point d)} (hμ : Continuous μ)
    {U : ℝ × Point d → Point d}
    (hU : Integrable U ((volume.restrict (Icc 0 T)) ⊗ₘ probabilityCurveKernel μ hμ))
    (heq : ∀ ψ : Test d,∀ r ∈ Icc 0 T,
      (∫ x,(ψ : Point d → ℝ) x ∂(μ r : Measure (Point d)))-
        (∫ x,(ψ : Point d → ℝ) x ∂(μ 0 : Measure (Point d))) =
      ∫ s in 0..r,∫ x,⟪gradient (ψ : Point d → ℝ) x,U (s,x)⟫_ℝ ∂(μ s : Measure (Point d)))
    (ht : τ < t) (htT : t+τ < T) (φ : Test d) :
    let ρ := (volume.restrict (Icc 0 T)) ⊗ₘ probabilityCurveKernel μ hμ
    HasDerivAt (fun s => ∫ x,(φ : Point d → ℝ) x ∂spaceTimeRegularizedLaw τ hτ ε hε δ ρ s)
      (∫ x,⟪gradient (φ : Point d → ℝ) x,spaceTimeVelocity τ hτ ε hε δ ρ U t x⟫_ℝ
        ∂spaceTimeRegularizedLaw τ hτ ε hε δ ρ t) t := by
  dsimp only
  let ρ := (volume.restrict (Icc 0 T)) ⊗ₘ probabilityCurveKernel μ hμ
  let ψ := smoothTest ε hε φ
  have hi := (joint_gradient_pairing_integrable ρ hU ψ).integral_compProd
  have hit : IntegrableOn (fun s => ∫ x,⟪gradient (ψ : Point d → ℝ) x,U (s,x)⟫_ℝ
      ∂(μ s : Measure (Point d))) (Icc 0 T) := by
    exact hi
  have hd := timeKernel_hasDerivAt_source hτ (by simpa using ht.le) htT.le
    (continuous_compact_test_pairing hμ ψ).continuousOn hit (heq ψ)
  have hd' := (hd.const_mul (1-δ)).add_const (δ*(∫ x,(φ : Point d → ℝ) x ∂gaussianFloorLaw))
  have hfun : (fun s => ∫ x,(φ : Point d → ℝ) x ∂spaceTimeRegularizedLaw τ hτ ε hε δ ρ s) =ᶠ[𝓝 t]
      (fun s => (1-δ)*timeConvolution (timeKernel τ hτ) 0 T
        (fun r => ∫ x,(ψ : Point d → ℝ) x ∂(μ r : Measure (Point d))) s+
        δ*(∫ x,(φ : Point d → ℝ) x ∂gaussianFloorLaw)) := by
    filter_upwards [eventually_gt_nhds ht,
      ((continuous_id.add continuous_const).tendsto t).eventually (eventually_lt_nhds htT)] with s hs hsT
    exact spaceTimeRegularizedLaw_test_pairing hτ hε hδ.le hδ₁ hμ hs.le hsT.le φ
  apply (hd'.congr_of_eventuallyEq hfun).congr_deriv
  change (1-δ)*timeConvolution (timeKernel τ hτ) 0 T
    (fun s => ∫ x,⟪gradient (ψ : Point d → ℝ) x,U (s,x)⟫_ℝ ∂(μ s : Measure (Point d))) t = _
  change _ = ∫ x,⟪gradient (φ : Point d → ℝ) x,floorVelocity (1-δ) _ _ _ (t,x)⟫_ℝ
    ∂spaceTimeRegularizedLaw τ hτ ε hε δ ρ t
  rw [spaceTimeRegularizedLaw_flux_pairing hτ hε hδ hδ₁ ρ hU φ,
    Measure.integral_compProd (time_weighted_joint_pairing_integrable hτ ρ hU ψ t)]
  simp only [probabilityCurveKernel_apply,integral_const_mul,timeConvolution,ψ]


/-- Literal integrated compact-test equation for the actual globally clamped
probability curve and the actual shifted smooth velocity. -/
theorem spaceTimeProbabilityCurve_equation {τ ε δ T a b p q : ℝ}
    (hτ : 0 < τ) (hε : 0 < ε) (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    {μ : ℝ → ProbabilityMeasure (Point d)} (hμ : Continuous μ)
    {U : ℝ × Point d → Point d}
    (hU : Integrable U ((volume.restrict (Icc 0 T)) ⊗ₘ probabilityCurveKernel μ hμ))
    (heq : ∀ ψ : Test d,∀ r ∈ Icc 0 T,
      (∫ x,(ψ : Point d → ℝ) x ∂(μ r : Measure (Point d)))-
        (∫ x,(ψ : Point d → ℝ) x ∂(μ 0 : Measure (Point d))) =
      ∫ s in 0..r,∫ x,⟪gradient (ψ : Point d → ℝ) x,U (s,x)⟫_ℝ ∂(μ s : Measure (Point d)))
    (hab : a ≤ b) (ha : τ < a) (hb : b+τ < T)
    (φ : Test d) (hp : p ∈ Icc 0 (b-a)) (hq : q ∈ Icc 0 (b-a)) :
    let ρ := (volume.restrict (Icc 0 T)) ⊗ₘ probabilityCurveKernel μ hμ
    let ν := spaceTimeProbabilityCurve hτ hε hδ hδ₁ (probabilityCurveKernel μ hμ) hab ha.le hb.le
    let v := fun r x => spaceTimeVelocity τ hτ ε hε δ ρ U (a+r) x
    IntervalIntegrable (fun r => ∫ x,⟪gradient (φ : Point d → ℝ) x,v r x⟫_ℝ
      ∂(ν r : Measure (Point d))) volume p q ∧
    (∫ x,(φ : Point d → ℝ) x ∂(ν q : Measure (Point d)))-
      (∫ x,(φ : Point d → ℝ) x ∂(ν p : Measure (Point d))) =
      ∫ r in p..q,∫ x,⟪gradient (φ : Point d → ℝ) x,v r x⟫_ℝ ∂(ν r : Measure (Point d)) := by
  dsimp only
  let ρ := (volume.restrict (Icc 0 T)) ⊗ₘ probabilityCurveKernel μ hμ
  let ν := spaceTimeProbabilityCurve hτ hε hδ hδ₁ (probabilityCurveKernel μ hμ) hab ha.le hb.le
  let F : ℝ → ℝ := fun r => ∫ x,(φ : Point d → ℝ) x ∂spaceTimeRegularizedLaw τ hτ ε hε δ ρ (a+r)
  let G : ℝ → ℝ := fun r => ∫ x,⟪gradient (φ : Point d → ℝ) x,
    spaceTimeVelocity τ hτ ε hε δ ρ U (a+r) x⟫_ℝ ∂spaceTimeRegularizedLaw τ hτ ε hε δ ρ (a+r)
  let H : ℝ → ℝ := fun r => ∫ x,⟪gradient (φ : Point d → ℝ) x,
    spaceTimeVelocity τ hτ ε hε δ ρ U (a+r) x⟫_ℝ ∂(ν r : Measure (Point d))
  have hG : Continuous G := (spaceTimeRegularizedLaw_flux_continuous hτ hε hδ hδ₁ ρ hU φ).comp
    (continuous_const.add continuous_id)
  have hGH : EqOn G H (Icc 0 (b-a)) := by
    intro r hr
    dsimp only [G,H,ν]
    rw [spaceTimeProbabilityCurve_coe hτ hε hδ hδ₁ _ hab ha.le hb.le hr]
  have hd (r : ℝ) (hr : r ∈ Icc 0 (b-a)) : HasDerivAt F (G r) r := by
    have hh := (spaceTimeRegularizedLaw_hasDerivAt hτ hε hδ hδ₁ hμ hU heq
      (t := a+r) (by linarith [hr.1]) (by linarith [hr.2]) φ).comp r
        ((hasDerivAt_id r).const_add a)
    simp only [Function.comp_def,mul_one] at hh
    exact hh
  have hsub : uIcc p q ⊆ Icc 0 (b-a) := uIcc_subset_Icc hp hq
  have hiG : IntervalIntegrable G volume p q := hG.intervalIntegrable p q
  have hiH : IntervalIntegrable H volume p q := hiG.congr
    (fun r hr => hGH (hsub (uIoc_subset_uIcc hr)))
  refine ⟨hiH,?_⟩
  have hFq : (∫ x,(φ : Point d → ℝ) x ∂(ν q : Measure (Point d))) = F q := by
    dsimp only [ν,F]
    rw [spaceTimeProbabilityCurve_coe hτ hε hδ hδ₁ _ hab ha.le hb.le hq]
  have hFp : (∫ x,(φ : Point d → ℝ) x ∂(ν p : Measure (Point d))) = F p := by
    dsimp only [ν,F]
    rw [spaceTimeProbabilityCurve_coe hτ hε hδ hδ₁ _ hab ha.le hb.le hp]
  change (∫ x,(φ : Point d → ℝ) x ∂(ν q : Measure (Point d)))-
    (∫ x,(φ : Point d → ℝ) x ∂(ν p : Measure (Point d))) = ∫ r in p..q,H r
  rw [hFq,hFp,← intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r hr => hd r (hsub hr)) hiG]
  exact intervalIntegral.integral_congr (fun r hr => hGH (hsub hr))

end SharpWasserstein.RoughEulerianSmoothing
