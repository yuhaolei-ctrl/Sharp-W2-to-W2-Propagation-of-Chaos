import SharpWasserstein.RoughEulerianSmoothingTests

/-! Exact compact-test duality for convolution of a genuine integrable
vector field with arbitrary measurable labels. The label formulation applies
directly to the joint time-space flux without selecting conditional fields. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff InnerProductSpace
namespace SharpWasserstein.RoughEulerianSmoothing
open WeightedTangent
variable {d : ℕ} [MeasurableSpace (Point d)] [BorelSpace (Point d)]
variable {Ω : Type*} [MeasurableSpace Ω]

def labelFlux (ε : ℝ) (hε : 0 < ε) (ρ : Measure Ω) (X U : Ω → Point d)
    (x : Point d) : Point d := ∫ w, mollifier ε hε (x-X w) • U w ∂ρ

theorem label_mollifier_smul_integrable {ε : ℝ} (hε : 0 < ε) (ρ : Measure Ω)
    {X U : Ω → Point d} (hX : Measurable X) (hU : Integrable U ρ) (x : Point d) :
    Integrable (fun w => mollifier ε hε (x-X w) • U w) ρ := by
  obtain ⟨C,_,hC⟩ := (mollifier_allDerivativesBounded (d := d) hε).bounded
  exact hU.bdd_smul C ((mollifier_smooth hε).continuous.measurable.comp
    (measurable_const.sub hX)).aestronglyMeasurable (Eventually.of_forall fun _ => hC _)

theorem label_mollifier_mul_joint_integrable {ε : ℝ} (hε : 0 < ε) (ρ : Measure Ω)
    [SFinite ρ] {X : Ω → Point d} (hX : Measurable X) {f : Ω → ℝ} (hf : Integrable f ρ) :
    Integrable (fun p : Point d × Ω => mollifier ε hε (p.1-X p.2)*f p.2)
      (volume.prod ρ) := by
  have hm : AEStronglyMeasurable
      (fun p : Point d × Ω => mollifier ε hε (p.1-X p.2)*f p.2) (volume.prod ρ) :=
    (((mollifier_smooth hε).continuous.measurable.comp
      (measurable_fst.sub (hX.comp measurable_snd))).aestronglyMeasurable).mul
        hf.aestronglyMeasurable.comp_snd
  apply (integrable_prod_iff' hm).mpr
  constructor
  · exact Eventually.of_forall fun w => ((mollifier_integrable hε).comp_sub_right (X w)).mul_const (f w)
  · have he (w : Ω) : (∫ x : Point d, ‖mollifier ε hε (x-X w)*f w‖) = ‖f w‖ := by
      simp_rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (mollifier_nonneg hε _)]
      rw [integral_mul_const, integral_sub_right_eq_self, mollifier_integral hε, one_mul]
    simpa only [he] using hf.norm

theorem label_flux_pairing_joint_integrable {ε : ℝ} (hε : 0 < ε) (ρ : Measure Ω)
    [SFinite ρ] {X U : Ω → Point d} (hX : Measurable X) (hU : Integrable U ρ)
    {F : Point d → Point d} (hF : Continuous F) {M : ℝ} (hM : ∀ x, ‖F x‖ ≤ M) :
    Integrable (fun p : Point d × Ω => mollifier ε hε (p.1-X p.2)*⟪F p.1,U p.2⟫_ℝ)
      (volume.prod ρ) := by
  have hmajor := (label_mollifier_mul_joint_integrable hε ρ hX hU.norm).const_mul M
  apply Integrable.mono' hmajor
    ((((mollifier_smooth hε).continuous.measurable.comp
      (measurable_fst.sub (hX.comp measurable_snd))).aestronglyMeasurable).mul
        ((hF.measurable.comp measurable_fst).aestronglyMeasurable.inner hU.aestronglyMeasurable.comp_snd))
  exact Eventually.of_forall fun p => by
    change ‖mollifier ε hε (p.1-X p.2)*⟪F p.1,U p.2⟫_ℝ‖ ≤ M*(mollifier ε hε (p.1-X p.2)*‖U p.2‖)
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (mollifier_nonneg hε _)]
    calc
      _ ≤ mollifier ε hε (p.1-X p.2) * (M*‖U p.2‖) :=
        mul_le_mul_of_nonneg_left ((norm_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _))) (mollifier_nonneg hε _)
      _ = _ := by ring

/-- Spatial convolution acts on the source by an actual compact smooth test
pullback, including for a vector field on a larger label space. -/
theorem labelFlux_test_pairing {ε : ℝ} (hε : 0 < ε) (ρ : Measure Ω)
    [SFinite ρ] {X U : Ω → Point d} (hX : Measurable X) (hU : Integrable U ρ) (φ : Test d) :
    (∫ x, ⟪gradient (φ : Point d → ℝ) x,labelFlux ε hε ρ X U x⟫_ℝ) =
      ∫ w, ⟪gradient (smoothTest ε hε φ : Point d → ℝ) (X w),U w⟫_ℝ ∂ρ := by
  obtain ⟨M,hM⟩ := (compactSupport_test_gradient φ).exists_bound_of_continuous (continuous_test_gradient φ)
  have hi := label_flux_pairing_joint_integrable hε ρ hX hU (continuous_test_gradient φ) hM
  calc
    _ = ∫ x, ∫ w, mollifier ε hε (x-X w)*⟪gradient (φ : Point d → ℝ) x,U w⟫_ℝ ∂ρ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp only
        rw [labelFlux, ← integral_inner (label_mollifier_smul_integrable hε ρ hX hU x)]
        simp only [real_inner_smul_right]
    _ = ∫ w, (∫ x : Point d, mollifier ε hε (x-X w)*⟪gradient (φ : Point d → ℝ) x,U w⟫_ℝ) ∂ρ :=
      integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro w
      dsimp only
      rw [smoothTest_gradient_pairing hε φ (X w) (U w), mollifierLaw,
        integral_withDensity_eq_integral_toReal_smul
          (mollifier_smooth hε).continuous.measurable.ennreal_ofReal
          (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      simp only [ENNReal.toReal_ofReal (mollifier_nonneg hε _), smul_eq_mul]
      have hh := integral_add_left_eq_self (μ := (volume : Measure (Point d)))
        (fun x => mollifier ε hε (x-X w)*⟪gradient (φ : Point d → ℝ) x,U w⟫_ℝ) (X w)
      simp only [add_sub_cancel_left] at hh
      exact hh.symm

end SharpWasserstein.RoughEulerianSmoothing
