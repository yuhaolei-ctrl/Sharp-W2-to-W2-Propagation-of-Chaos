import SharpWasserstein.RoughEulerianTimeActionProduct

/-! The jointly smoothed density is the density of a genuine averaged
probability law. Its law-weighted kinetic action is exactly the previously
proved space-time action, not a proxy quantity. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff ProbabilityTheory
namespace SharpWasserstein.RoughEulerianSmoothing
open WeightedTangent RoughEulerianTime
variable {d : ℕ} [MeasurableSpace (Point d)] [BorelSpace (Point d)]

/-- Actual spatial convolution of the actual time-averaged law. -/
theorem spaceTimeDensity_eq_averaged {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε)
    (ρ : Measure (ℝ × Point d)) [IsFiniteMeasure ρ] (t : ℝ) (x : Point d) :
    spaceTimeDensity τ hτ ε hε ρ (t,x) = density ε hε (averagedKernel τ hτ ρ t) x := by
  unfold density
  have hf : StronglyMeasurable (fun y : Point d => mollifier ε hε (x-y)) :=
    ((mollifier_smooth hε).continuous.comp (continuous_const.sub continuous_id)).stronglyMeasurable
  rw [integral_averagedKernel hτ ρ (fun y => mollifier ε hε (x-y)) hf t]
  rfl

/-- The spatial flux is the true time-weighted original joint flux. -/
theorem spaceTimeFlux_eq_weighted {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε)
    (ρ : Measure (ℝ × Point d)) [IsFiniteMeasure ρ] (U : ℝ × Point d → Point d)
    (t : ℝ) (x : Point d) :
    spaceTimeFlux τ hτ ε hε ρ U (t,x) =
      ∫ z,mollifier ε hε (x-z.2) • U z ∂weightedTimeKernel τ hτ ρ t := by
  rw [integral_weightedTimeKernel]
  simp only [spaceTimeFlux,spaceTimeKernel,Prod.fst_sub,Prod.snd_sub,mul_smul]

/-- One total law-valued curve, constructed from the original joint measure. -/
def spaceTimeRegularizedLaw (τ : ℝ) (hτ : 0 < τ) (ε : ℝ) (hε : 0 < ε)
    (δ : ℝ) (ρ : Measure (ℝ × Point d)) [IsFiniteMeasure ρ] (t : ℝ) : Measure (Point d) :=
  regularizedLaw ε hε δ (averagedKernel τ hτ ρ t)

theorem spaceTimeRegularizedLaw_eq {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε)
    (δ : ℝ) (ρ : Measure (ℝ × Point d)) [IsFiniteMeasure ρ] (t : ℝ) :
    spaceTimeRegularizedLaw τ hτ ε hε δ ρ t = volume.withDensity (fun x =>
      ENNReal.ofReal (floorDensity (1-δ) (spaceTimeDensity τ hτ ε hε ρ)
        (fun p => δ*gaussianFloor p.2) (t,x))) := by
  unfold spaceTimeRegularizedLaw regularizedLaw regularizedDensity floorDensity
  congr 1
  funext x
  rw [spaceTimeDensity_eq_averaged]

theorem spaceTimeRegularizedLaw_probability {τ ε δ a b t : ℝ} (hτ : 0 < τ) (hε : 0 < ε)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (κ : Kernel ℝ (Point d)) [IsMarkovKernel κ]
    (ha : a+τ ≤ t) (hb : t+τ ≤ b) :
    IsProbabilityMeasure (spaceTimeRegularizedLaw τ hτ ε hε δ
      ((volume.restrict (Icc a b)) ⊗ₘ κ) t) := by
  letI := averagedKernel_probability hτ κ ha hb
  exact regularizedLaw_probability hε hδ hδ₁ _

/-- The actual representing velocity has exactly the density-weighted
Lebesgue action under the actual constructed law. -/
theorem spaceTimeRegularizedLaw_action_eq {τ ε δ : ℝ} (hτ : 0 < τ) (hε : 0 < ε)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (ρ : Measure (ℝ × Point d)) [IsFiniteMeasure ρ]
    (U : ℝ × Point d → Point d) (t : ℝ) :
    let v := floorVelocity (1-δ) (spaceTimeDensity τ hτ ε hε ρ)
      (fun p => δ*gaussianFloor p.2) (spaceTimeFlux τ hτ ε hε ρ U)
    (∫ x,‖v (t,x)‖^2 ∂spaceTimeRegularizedLaw τ hτ ε hε δ ρ t) =
      ∫ x,floorDensity (1-δ) (spaceTimeDensity τ hτ ε hε ρ)
        (fun p => δ*gaussianFloor p.2) (t,x)*‖v (t,x)‖^2 := by
  dsimp only
  rw [spaceTimeRegularizedLaw_eq]
  have hd : Continuous (fun x : Point d => floorDensity (1-δ) (spaceTimeDensity τ hτ ε hε ρ)
      (fun p => δ*gaussianFloor p.2) (t,x)) :=
    (continuous_const.mul ((spaceTimeDensity_smooth hτ hε ρ).continuous.comp
      (continuous_const.prodMk continuous_id))).add (continuous_const.mul gaussianFloor_smooth.continuous)
  rw [integral_withDensity_eq_integral_toReal_smul hd.measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (floorDensity_pos (sub_nonneg.mpr hδ₁)
    (spaceTimeDensity_nonneg hτ hε ρ) (fun p => mul_pos hδ (gaussianFloor_pos p.2)) _).le,smul_eq_mul]

/-- Actual law-weighted finite action on every time window, with sharp
contraction from the single original joint L² field. -/
theorem spaceTimeRegularizedLaw_action_integrable_and_le {τ ε δ : ℝ} (hτ : 0 < τ) (hε : 0 < ε)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (ρ : Measure (ℝ × Point d)) [IsFiniteMeasure ρ]
    {U : ℝ × Point d → Point d} (hU : Integrable U ρ)
    (hU₂ : Integrable (fun z => ‖U z‖^2) ρ) (I : Set ℝ) :
    let v := floorVelocity (1-δ) (spaceTimeDensity τ hτ ε hε ρ)
      (fun p => δ*gaussianFloor p.2) (spaceTimeFlux τ hτ ε hε ρ U)
    let E := fun t => ∫ x,‖v (t,x)‖^2 ∂spaceTimeRegularizedLaw τ hτ ε hε δ ρ t
    Integrable E (volume.restrict I) ∧
      (∫ t in I,E t) ≤ (1-δ)*∫ z,‖U z‖^2 ∂ρ := by
  dsimp only
  simp_rw [spaceTimeRegularizedLaw_action_eq hτ hε hδ hδ₁ ρ U]
  exact spaceTimeFloor_action_time_restrict hτ hε hδ hδ₁ ρ hU hU₂ I

end SharpWasserstein.RoughEulerianSmoothing
