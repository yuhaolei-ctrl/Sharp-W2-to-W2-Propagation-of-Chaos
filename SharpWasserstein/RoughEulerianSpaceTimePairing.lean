import SharpWasserstein.RoughEulerianSmoothingDuality
import SharpWasserstein.RoughEulerianSmoothingMixture
import SharpWasserstein.RoughEulerianTimeActionIdentification
import SharpWasserstein.RoughEulerianTimeWeak

/-! Actual law and flux pairings of the joint regularization. Compact spatial
tests are pulled back before invoking the original integrated weak equation. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff InnerProductSpace Interval ProbabilityTheory
namespace SharpWasserstein.RoughEulerianSmoothing
open WeightedTangent RoughEulerianTime RoughEulerianTransport
variable {d : ℕ} [MeasurableSpace (Point d)] [BorelSpace (Point d)]

theorem spaceTimeFlux_test_pairing {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε)
    (ρ : Measure (ℝ × Point d)) [IsFiniteMeasure ρ]
    {U : ℝ × Point d → Point d} (hU : Integrable U ρ) (φ : Test d) (t : ℝ) :
    (∫ x,⟪gradient (φ : Point d → ℝ) x,spaceTimeFlux τ hτ ε hε ρ U (t,x)⟫_ℝ) =
      ∫ z,timeKernel τ hτ (t-z.1)*⟪gradient (smoothTest ε hε φ : Point d → ℝ) z.2,U z⟫_ℝ ∂ρ := by
  obtain ⟨C,D,hC,hD⟩ := timeKernel_bounds hτ
  have hi : Integrable (fun z : ℝ × Point d => timeKernel τ hτ (t-z.1) • U z) ρ :=
    hU.bdd_smul C ((timeKernel_smooth hτ).continuous.comp
      (continuous_const.sub continuous_fst)).aestronglyMeasurable (Eventually.of_forall fun z => hC _)
  have he (x : Point d) : spaceTimeFlux τ hτ ε hε ρ U (t,x) =
      labelFlux ε hε ρ Prod.snd (fun z => timeKernel τ hτ (t-z.1) • U z) x := by
    unfold spaceTimeFlux spaceTimeKernel labelFlux
    simp only [Prod.fst_sub,Prod.snd_sub,smul_smul,mul_comm]
  simp_rw [he]
  rw [labelFlux_test_pairing hε ρ measurable_snd hi φ]
  simp only [real_inner_smul_right]

theorem regularizedLaw_test_pairing {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1)
    (ν : Measure (Point d)) [IsProbabilityMeasure ν] (φ : Test d) :
    (∫ x,(φ : Point d → ℝ) x ∂regularizedLaw ε hε δ ν) =
      (1-δ)*(∫ x,(smoothTest ε hε φ : Point d → ℝ) x ∂ν)+
        δ*(∫ x,(φ : Point d → ℝ) x ∂gaussianFloorLaw) := by
  have hi₁ : Integrable (φ : Point d → ℝ) (convolvedLaw ε hε ν) :=
    φ.property.1.continuous.integrable_of_hasCompactSupport φ.property.2
  have hi₂ : Integrable (φ : Point d → ℝ) (gaussianFloorLaw (d := d)) :=
    φ.property.1.continuous.integrable_of_hasCompactSupport φ.property.2
  rw [regularizedLaw_eq_mixture hε hδ hδ₁ ν,
    integral_add_measure (hi₁.smul_measure ENNReal.ofReal_ne_top) (hi₂.smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure,integral_smul_measure,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hδ₁),ENNReal.toReal_ofReal hδ,
    convolvedLaw_test_pairing hε ν φ]
  rfl

theorem time_weighted_joint_pairing_integrable {τ : ℝ} (hτ : 0 < τ)
    (ρ : Measure (ℝ × Point d)) {U : ℝ × Point d → Point d} (hU : Integrable U ρ)
    (φ : Test d) (t : ℝ) :
    Integrable (fun z => timeKernel τ hτ (t-z.1)*⟪gradient (φ : Point d → ℝ) z.2,U z⟫_ℝ) ρ := by
  obtain ⟨M,hM⟩ := (compactSupport_test_gradient φ).exists_bound_of_continuous (continuous_test_gradient φ)
  have hi : Integrable (fun z => ⟪gradient (φ : Point d → ℝ) z.2,U z⟫_ℝ) ρ := by
    apply (hU.norm.const_mul M).mono'
      (((continuous_test_gradient φ).comp continuous_snd).aestronglyMeasurable.inner hU.aestronglyMeasurable)
    exact Eventually.of_forall fun z => (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _))
  obtain ⟨C,D,hC,hD⟩ := timeKernel_bounds hτ
  exact hi.bdd_mul ((timeKernel_smooth hτ).continuous.comp
    (continuous_const.sub continuous_fst)).aestronglyMeasurable (Eventually.of_forall fun z => hC _)

/-- Genuine disintegration of the regularized law pairing. -/
theorem spaceTimeRegularizedLaw_test_pairing {τ ε δ T t : ℝ}
    (hτ : 0 < τ) (hε : 0 < ε) (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1)
    {μ : ℝ → ProbabilityMeasure (Point d)} (hμ : Continuous μ)
    (ht : τ ≤ t) (htT : t+τ ≤ T) (φ : Test d) :
    (∫ x,(φ : Point d → ℝ) x ∂spaceTimeRegularizedLaw τ hτ ε hε δ
      ((volume.restrict (Icc 0 T)) ⊗ₘ probabilityCurveKernel μ hμ) t) =
      (1-δ)*timeConvolution (timeKernel τ hτ) 0 T
        (fun s => ∫ x,(smoothTest ε hε φ : Point d → ℝ) x ∂(μ s : Measure (Point d))) t+
      δ*(∫ x,(φ : Point d → ℝ) x ∂gaussianFloorLaw) := by
  let ρ := (volume.restrict (Icc 0 T)) ⊗ₘ probabilityCurveKernel μ hμ
  letI := averagedKernel_probability (a := 0) (b := T) hτ (probabilityCurveKernel μ hμ) (by simpa using ht) htT
  rw [spaceTimeRegularizedLaw,regularizedLaw_test_pairing hε hδ hδ₁ _ φ,
    integral_averagedKernel hτ ρ (smoothTest ε hε φ : Point d → ℝ)
      (smoothTestFunction_smooth hε φ).continuous.stronglyMeasurable t]
  congr 1
  congr 1
  obtain ⟨C,hC⟩ := (smoothTestFunction_compact hε φ).exists_bound_of_continuous
    (smoothTestFunction_smooth hε φ).continuous
  obtain ⟨B,D,hB,hD⟩ := timeKernel_bounds hτ
  have hi : Integrable (fun z : ℝ × Point d => timeKernel τ hτ (t-z.1) •
      (smoothTest ε hε φ : Point d → ℝ) z.2) ρ := by
    apply Integrable.of_bound
      (((timeKernel_smooth hτ).continuous.comp (continuous_const.sub continuous_fst)).aestronglyMeasurable.smul
        (((smoothTestFunction_smooth hε φ).continuous.comp continuous_snd).aestronglyMeasurable)) (B*C)
    exact Eventually.of_forall fun z => (norm_smul _ _).le.trans
      (mul_le_mul (hB _) (hC _) (norm_nonneg _) (by exact (norm_nonneg _).trans (hB 0)))
  rw [Measure.integral_compProd hi]
  simp only [probabilityCurveKernel_apply,smul_eq_mul,integral_const_mul,timeConvolution]

/-- The smooth velocity carries exactly the jointly mollified original flux. -/
theorem spaceTimeRegularizedLaw_flux_pairing {τ ε δ : ℝ}
    (hτ : 0 < τ) (hε : 0 < ε) (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (ρ : Measure (ℝ × Point d)) [IsFiniteMeasure ρ]
    {U : ℝ × Point d → Point d} (hU : Integrable U ρ) (φ : Test d) (t : ℝ) :
    let v := floorVelocity (1-δ) (spaceTimeDensity τ hτ ε hε ρ)
      (fun p => δ*gaussianFloor p.2) (spaceTimeFlux τ hτ ε hε ρ U)
    (∫ x,⟪gradient (φ : Point d → ℝ) x,v (t,x)⟫_ℝ
      ∂spaceTimeRegularizedLaw τ hτ ε hε δ ρ t) =
      (1-δ)*∫ z,timeKernel τ hτ (t-z.1)*
        ⟪gradient (smoothTest ε hε φ : Point d → ℝ) z.2,U z⟫_ℝ ∂ρ := by
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
  have he (x : Point d) := floorVelocity_flux (sub_nonneg.mpr hδ₁)
    (spaceTimeDensity_nonneg hτ hε ρ) (fun p => mul_pos hδ (gaussianFloor_pos p.2))
    (spaceTimeFlux τ hτ ε hε ρ U) (t,x)
  simp_rw [← real_inner_smul_right,he,real_inner_smul_right]
  rw [integral_const_mul,spaceTimeFlux_test_pairing hτ hε ρ hU φ t]

end SharpWasserstein.RoughEulerianSmoothing
