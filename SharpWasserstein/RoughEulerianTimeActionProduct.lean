module

public import SharpWasserstein.Compat
public import SharpWasserstein.RoughEulerianTimeActionConvolution
public import SharpWasserstein.RoughEulerianSpaceTimeSmooth

@[expose] public section

/-! Exact normalization and action contraction for the actual product
space-time mollifier. The total action estimate concerns the original joint
finite measure and its one L² field, with no measurable timewise choices. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace SharpWasserstein.RoughEulerianSmoothing
open WeightedTangent RoughEulerianTime
variable {d : ℕ} [MeasurableSpace (Point d)] [BorelSpace (Point d)]

theorem spaceTimeKernel_integrable {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε) :
    Integrable (spaceTimeKernel (d := d) τ hτ ε hε)
      ((volume : Measure ℝ).prod (volume : Measure (Point d))) :=
  (timeKernel_integrable hτ).mul_prod (mollifier_integrable hε)

theorem spaceTimeKernel_integral {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε) :
    (∫ p,spaceTimeKernel (d := d) τ hτ ε hε p
      ∂(volume : Measure ℝ).prod (volume : Measure (Point d))) = 1 := by
  rw [show spaceTimeKernel (d := d) τ hτ ε hε =
    (fun p : ℝ × Point d => timeKernel τ hτ p.1*mollifier ε hε p.2) from rfl,
    integral_prod_mul,timeKernel_integral hτ,mollifier_integral hε,mul_one]

/-- Product convolution obeys the exact scalar Fubini identity. -/
theorem integral_spaceTimeKernel_mul {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε)
    (ρ : Measure (ℝ × Point d)) [SFinite ρ] {f : ℝ × Point d → ℝ} (hf : Integrable f ρ) :
    (∫ p,∫ z,spaceTimeKernel τ hτ ε hε (p-z)*f z ∂ρ
      ∂(volume : Measure ℝ).prod (volume : Measure (Point d))) = ∫ z,f z ∂ρ :=
    integral_kernel_mul _ (spaceTimeKernel_smooth hτ hε).continuous
      (spaceTimeKernel_nonneg hτ hε) (spaceTimeKernel_integrable hτ hε)
      (spaceTimeKernel_integral hτ hε) ρ hf

/-- The actual smooth density and flux with a positive Gaussian floor have
integrable whole space-time action, bounded by the original action. -/
theorem spaceTimeFloor_action_integrable_and_le {τ ε δ : ℝ} (hτ : 0 < τ) (hε : 0 < ε)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (ρ : Measure (ℝ × Point d)) [IsFiniteMeasure ρ]
    {U : ℝ × Point d → Point d} (hU : Integrable U ρ)
    (hU₂ : Integrable (fun z => ‖U z‖^2) ρ) :
    let A := fun p => floorDensity (1-δ) (spaceTimeDensity τ hτ ε hε ρ)
      (fun p => δ*gaussianFloor p.2) p *
      ‖floorVelocity (1-δ) (spaceTimeDensity τ hτ ε hε ρ)
        (fun p => δ*gaussianFloor p.2) (spaceTimeFlux τ hτ ε hε ρ U) p‖^2
    Integrable A ((volume : Measure ℝ).prod (volume : Measure (Point d))) ∧
      (∫ p,A p ∂(volume : Measure ℝ).prod (volume : Measure (Point d))) ≤
        (1-δ)*∫ z,‖U z‖^2 ∂ρ := by
  obtain ⟨C,_,hC⟩ := (spaceTimeKernel_allDerivativesBounded (d := d) hτ hε).bounded
  exact kernel_floor_action_integrable_and_le _ (spaceTimeKernel_smooth hτ hε).continuous
    (spaceTimeKernel_nonneg hτ hε) (spaceTimeKernel_integrable hτ hε)
    (spaceTimeKernel_integral hτ hε) ⟨C,hC⟩ ρ hU hU₂ (sub_nonneg.mpr hδ₁)
    (fun p => mul_pos hδ (gaussianFloor_pos p.2))
    (continuous_const.mul (gaussianFloor_smooth.continuous.comp continuous_snd)).aestronglyMeasurable

/-- Restricting to any time window preserves the same sharp action bound. -/
theorem spaceTimeFloor_action_time_restrict {τ ε δ : ℝ} (hτ : 0 < τ) (hε : 0 < ε)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (ρ : Measure (ℝ × Point d)) [IsFiniteMeasure ρ]
    {U : ℝ × Point d → Point d} (hU : Integrable U ρ)
    (hU₂ : Integrable (fun z => ‖U z‖^2) ρ) (I : Set ℝ) :
    let A := fun p => floorDensity (1-δ) (spaceTimeDensity τ hτ ε hε ρ)
      (fun p => δ*gaussianFloor p.2) p *
      ‖floorVelocity (1-δ) (spaceTimeDensity τ hτ ε hε ρ)
        (fun p => δ*gaussianFloor p.2) (spaceTimeFlux τ hτ ε hε ρ U) p‖^2
    Integrable (fun t => ∫ x,A (t,x)) (volume.restrict I) ∧
      (∫ t in I,∫ x,A (t,x)) ≤ (1-δ)*∫ z,‖U z‖^2 ∂ρ := by
  dsimp only
  let A := fun p => floorDensity (1-δ) (spaceTimeDensity τ hτ ε hε ρ)
    (fun p => δ*gaussianFloor p.2) p *
    ‖floorVelocity (1-δ) (spaceTimeDensity τ hτ ε hε ρ)
      (fun p => δ*gaussianFloor p.2) (spaceTimeFlux τ hτ ε hε ρ U) p‖^2
  obtain ⟨hi,hle⟩ := spaceTimeFloor_action_integrable_and_le hτ hε hδ hδ₁ ρ hU hU₂
  have hμ : (volume.restrict I).prod (volume : Measure (Point d)) ≤
      (volume : Measure ℝ).prod (volume : Measure (Point d)) :=
    Measure.prod_mono Measure.restrict_le_self le_rfl
  have hr : Integrable A ((volume.restrict I).prod (volume : Measure (Point d))) :=
    hi.mono_measure hμ
  refine ⟨hr.integral_prod_left,?_⟩
  rw [← integral_prod A hr]
  refine (integral_mono_measure hμ ?_ hi).trans hle
  exact Eventually.of_forall fun p => mul_nonneg
    (floorDensity_pos (sub_nonneg.mpr hδ₁) (spaceTimeDensity_nonneg hτ hε ρ)
      (fun q => mul_pos hδ (gaussianFloor_pos q.2)) p).le (sq_nonneg _)

end SharpWasserstein.RoughEulerianSmoothing
