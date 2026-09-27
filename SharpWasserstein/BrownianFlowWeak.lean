import SharpWasserstein.BrownianFlow

/-! Complete weak evolution for genuine Brownian-driven laws of a bounded,
continuous time-dependent drift with a uniform spatial Lipschitz constant. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Interval Topology
namespace SharpWasserstein.BrownianFlow

variable {d N : ℕ} {v : ℝ → Configuration d N → Configuration d N} {M K : ℝ≥0}
  (hv : Continuous (Function.uncurry v)) (hb : ∀ t x, ‖v t x‖ ≤ M)
  (hl : ∀ t, LipschitzWith K (v t))

theorem globalLaw_boundedExpectation_continuousOn_Icc
    (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    {g : ℝ → Configuration d N → ℝ} (hg : Continuous (Function.uncurry g))
    {B : ℝ} (hB : ∀ t x, |g t x| ≤ B) {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (fun t => ∫ x, g t x ∂globalLaw hv hb hl μ t) (Icc 0 T) := by
  have h := EulerTime.trajectory_mean_continuousOn
    (P := μ.prod (BrownianNoise.configurationLaw d N T))
    (fun p => (BoundedFlow.flow_trajectory hv hb hl hT p.1 p.2).continuous)
    hg hB (fun _ ht => (BoundedFlow.flow_continuous hv hb hl hT ht).measurable)
  apply continuousOn_iff_continuous_restrict.mpr
  convert h.restrict using 1
  funext t
  dsimp only [Set.restrict]
  rw [globalLaw_eq hv hb hl hT μ t.property]
  exact law_integral_eq hv hb hl hT μ (hg.comp (continuous_const.prodMk continuous_id)) t.property

theorem globalLaw_boundedExpectation_continuous
    (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    {g : ℝ → Configuration d N → ℝ} (hg : Continuous (Function.uncurry g))
    {B : ℝ} (hB : ∀ t x, |g t x| ≤ B) :
    ContinuousOn (fun t => ∫ x, g t x ∂globalLaw hv hb hl μ t) (Ici 0) := by
  intro t ht
  change 0 ≤ t at ht
  have hT : 0 ≤ t+1 := by linarith
  have h := globalLaw_boundedExpectation_continuousOn_Icc hv hb hl μ hg hB hT t ⟨ht,by linarith⟩
  apply h.mono_of_mem_nhdsWithin
  rw [← Ici_inter_Iic]
  exact inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Iic_mem_nhds (by linarith : t < t+1)))

theorem globalLaw_testContinuous
    (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    {φ : Configuration d N → ℝ} (hφ : SmoothCompactTest φ) :
    ContinuousOn (fun t => ∫ x, φ x ∂globalLaw hv hb hl μ t) (Ici 0) := by
  obtain ⟨B,_,hB⟩ := FrozenGaussian.compact_bound hφ
  exact globalLaw_boundedExpectation_continuous hv hb hl μ (hφ.1.continuous.comp continuous_snd)
    (fun _ x => by simpa only [Real.norm_eq_abs] using hB x)

theorem globalLaw_generatorIntegrable
    (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    {φ : Configuration d N → ℝ} (hφ : SmoothCompactTest φ) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (generator (v t) φ) (globalLaw hv hb hl μ t) := by
  letI := globalLaw_probability hv hb hl μ ht
  exact CompactGenerator.integrable (CompactGenerator.generator_continuous hφ (hl t).continuous)
    (CompactGenerator.generator_compact hφ _) _

theorem globalLaw_timeIntegrable
    (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    {φ : Configuration d N → ℝ} (hφ : SmoothCompactTest φ) {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (fun s => ∫ x, generator (v s) φ x ∂globalLaw hv hb hl μ s) volume 0 t := by
  obtain ⟨B,_,hB⟩ := CompactGenerator.generator_uniform_bound hφ M
  exact (globalLaw_boundedExpectation_continuousOn_Icc hv hb hl μ (g := fun t => generator (v t) φ)
    (CompactGenerator.generator_joint_continuous hφ hv)
    (fun t x => by simpa only [Real.norm_eq_abs] using hB (v t) (hb t) x) ht).intervalIntegrable_of_Icc ht

/-- Integrated generator identity for the actual finite-horizon solution law. -/
theorem law_equation {T : ℝ} (hT : 0 < T)
    (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    {φ : Configuration d N → ℝ} (hφ : SmoothCompactTest φ) :
    (∫ x, φ x ∂law hv hb hl hT.le μ T) - (∫ x, φ x ∂μ) =
      ∫ s in (0 : ℝ)..T, ∫ x, generator (v s) φ x ∂law hv hb hl hT.le μ s := by
  have he := EulerTimeWeak.brownian_trajectory_weak_equation hT μ v hv M K hb hl
    (fun t p => BoundedFlow.flow hv hb hl hT.le p.1 p.2 t)
    (fun p => BoundedFlow.flow_trajectory hv hb hl hT.le p.1 p.2)
    (fun _ ht => (BoundedFlow.flow_continuous hv hb hl hT.le ht).measurable) hφ
  rw [law_integral_eq hv hb hl hT.le μ hφ.1.continuous ⟨hT.le,le_rfl⟩,he]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hT.le] at hs
  exact (law_integral_eq hv hb hl hT.le μ
    (CompactGenerator.generator_continuous hφ (hl s).continuous) hs).symm

theorem globalLaw_equation (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    {φ : Configuration d N → ℝ} (hφ : SmoothCompactTest φ) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, φ x ∂globalLaw hv hb hl μ t) - (∫ x, φ x ∂globalLaw hv hb hl μ 0) =
      ∫ s in (0 : ℝ)..t, ∫ x, generator (v s) φ x ∂globalLaw hv hb hl μ s := by
  rcases ht.eq_or_lt with rfl | ht
  · simp
  · rw [globalLaw_initial hv hb hl μ,globalLaw_eq hv hb hl ht.le μ ⟨ht.le,le_rfl⟩,
      law_equation hv hb hl ht μ hφ]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.le] at hs
    dsimp only
    rw [globalLaw_eq hv hb hl ht.le μ hs]

/-- Every initial probability law with a finite second moment produces an
actual weak evolution of the time-dependent Fokker--Planck equation. -/
theorem globalLaw_weakEvolution (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    (hμ : HasSecondMoment μ) : WeakEvolution v (globalLaw hv hb hl μ) where
  probability := fun _ ht => globalLaw_probability hv hb hl μ ht
  secondMoment := fun _ ht => globalLaw_secondMoment hv hb hl μ hμ ht
  momentBound := fun _ hT => globalLaw_momentBound hv hb hl μ hμ hT.le
  testContinuous := fun _ hφ => globalLaw_testContinuous hv hb hl μ hφ
  generatorIntegrable := fun _ hφ _ ht => globalLaw_generatorIntegrable hv hb hl μ hφ ht
  timeIntegrable := fun _ hφ _ ht => globalLaw_timeIntegrable hv hb hl μ hφ ht
  equation := fun _ hφ _ ht => globalLaw_equation hv hb hl μ hφ ht

end SharpWasserstein.BrownianFlow
