import SharpWasserstein.PeriodicParticleTangentLimitSource
import SharpWasserstein.WeightedTangentLimit

/-! Actual convergence of projected JV pairings and their carrying laws.
Only after both limits are proved is a supplied uniform energy bound passed
to the genuine varying-weight lower-semicontinuity theorem. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal Topology ContDiff
namespace SharpWasserstein.PeriodicParticleTangentLimit
open WeightedTangent PropagatedSourceEquation
variable {d N m : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  [MeasurableSpace (Point m)] [BorelSpace (Point m)]
  {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
  (hN : 0 < N) (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
  (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) {T : ℝ} (hT : 0 ≤ T)
  (ξ : Measure C(Icc 0 T,Point (N*d))) [IsProbabilityMeasure ξ]
  (μ : Measure (Point (N*d))) [IsFiniteMeasure μ]
  (A : Point (N*d) →L[ℝ] Point m) {t : ℝ} (ht : t ∈ Icc 0 T)

include ht in
omit [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))] in
theorem flux_tendsto (u : Point (N*d) → Point (N*d))
    (q : Point (N*d) × C(Icc 0 T,Point (N*d))) :
    Tendsto (fun n => flux hN (PeriodicParticle.interaction_smooth hb n)
      (PeriodicParticle.interaction_bounds hb hbound hL₁ hL₂ n) hM hL₁ hL₂ hT (t := t) u q)
      atTop (𝓝 (flux hN hb hbound hM hL₁ hL₂ hT (t := t) u q)) := by
  have he : Continuous (fun J : Point (N*d) →L[ℝ] Point (N*d) => J (u q.1)) :=
    continuous_id.clm_apply continuous_const
  exact he.continuousAt.tendsto.comp (flow_fderiv_tendsto hN hb hbound hM hL₁ hL₂ hT q.1 q.2 ht)

include ht in
omit [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  [MeasurableSpace (Point m)] [BorelSpace (Point m)] in
/-- A single integrable bound, in the actual Euclidean norm, for every period. -/
theorem pairing_norm_le {F : Point m → ℝ} {L : ℝ≥0}
    (hL : ∀ y, ‖fderiv ℝ F y‖ ≤ L) (u : Point (N*d) → Point (N*d))
    (q : Point (N*d) × C(Icc 0 T,Point (N*d))) :
    ‖fderiv ℝ F (A (endpoint hN hb hbound hM hL₁ hL₂ hT (t := t) q))
      (A (flux hN hb hbound hM hL₁ hL₂ hT (t := t) u q))‖ ≤
      ((L:ℝ)*‖A‖*Real.exp ((lipBound d L₁ L₂:ℝ)*t))*‖u q.1‖ := by
  have hJ := flow_fderiv_norm_le hN hb hbound hM hL₁ hL₂ hT q.1 q.2 ht
  calc
    _ ≤ (L:ℝ)*‖A (flux hN hb hbound hM hL₁ hL₂ hT (t := t) u q)‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hL _) (norm_nonneg _))
    _ ≤ (L:ℝ)*(‖A‖*(Real.exp ((lipBound d L₁ L₂:ℝ)*t)*‖u q.1‖)) := by
      apply mul_le_mul_of_nonneg_left _ L.coe_nonneg
      apply (A.le_opNorm _).trans
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hJ (norm_nonneg _))
    _ = _ := by ring

include ht in
omit [MeasurableSpace (Point m)] [BorelSpace (Point m)] in
/-- Literal projected random-flux pairing convergence under the original law.
No convergence of source distributions is assumed. -/
theorem pairing_tendsto {F : Point m → ℝ} (hF : ContDiff ℝ 1 F) {L : ℝ≥0}
    (hL : ∀ y, ‖fderiv ℝ F y‖ ≤ L) {u : Point (N*d) → Point (N*d)} (hu : MemLp u 2 μ) :
    Tendsto (fun n => ∫ q,
      fderiv ℝ F (A (endpoint hN (PeriodicParticle.interaction_smooth hb n)
        (PeriodicParticle.interaction_bounds hb hbound hL₁ hL₂ n) hM hL₁ hL₂ hT (t := t) q))
        (A (flux hN (PeriodicParticle.interaction_smooth hb n)
          (PeriodicParticle.interaction_bounds hb hbound hL₁ hL₂ n) hM hL₁ hL₂ hT (t := t) u q)) ∂μ.prod ξ)
      atTop (𝓝 (∫ q,fderiv ℝ F (A (endpoint hN hb hbound hM hL₁ hL₂ hT (t := t) q))
        (A (flux hN hb hbound hM hL₁ hL₂ hT (t := t) u q)) ∂μ.prod ξ)) := by
  have hup : MemLp (fun q : Point (N*d) × C(Icc 0 T,Point (N*d)) => u q.1) 2 (μ.prod ξ) :=
    hu.comp_measurePreserving (measurePreserving_fst (μ := μ) (ν := ξ))
  apply tendsto_integral_of_dominated_convergence
    (fun q : Point (N*d) × C(Icc 0 T,Point (N*d)) =>
      ((L:ℝ)*‖A‖*Real.exp ((lipBound d L₁ L₂:ℝ)*t))*‖u q.1‖)
  · intro n
    exact (pairing_integrable hN (PeriodicParticle.interaction_smooth hb n)
      (PeriodicParticle.interaction_bounds hb hbound hL₁ hL₂ n) hM hL₁ hL₂ hT ξ μ A ht hF hL hu).1
  · exact (hup.integrable (by norm_num)).norm.const_mul _
  · intro n
    exact Eventually.of_forall (fun q => pairing_norm_le hN (PeriodicParticle.interaction_smooth hb n)
      (PeriodicParticle.interaction_bounds hb hbound hL₁ hL₂ n) hM hL₁ hL₂ hT A ht hL u q)
  · apply Eventually.of_forall
    intro q
    have hD := (hF.continuous_fderiv (by norm_num)).continuousAt.tendsto.comp
      (A.continuous.continuousAt.tendsto.comp (flow_tendsto hN hb hbound hM hL₁ hL₂ hT q.1 q.2 ht))
    have hV := A.continuous.continuousAt.tendsto.comp (flux_tendsto hN hb hbound hM hL₁ hL₂ hT ht u q)
    exact (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp (hD.prodMk_nhds hV)

/-- The genuine projected source converges on each actual compact smooth test. -/
theorem source_tendsto (u : Point (N*d) → Point (N*d)) (hu : MemLp u 2 μ) (φ : Test m) :
    Tendsto (fun n => source hN (PeriodicParticle.interaction_smooth hb n)
      (PeriodicParticle.interaction_bounds hb hbound hL₁ hL₂ n) hM hL₁ hL₂ hT ξ μ A ht u hu φ)
      atTop (𝓝 (source hN hb hbound hM hL₁ hL₂ hT ξ μ A ht u hu φ)) := by
  simp_rw [source_apply]
  obtain ⟨_,L,_,hL⟩ := compactTest_bounds φ
  exact pairing_tendsto hN hb hbound hM hL₁ hL₂ hT ξ μ A ht
    (φ.property.1.of_le (by simp)) hL hu

omit [IsFiniteMeasure μ] in
/-- Narrow convergence of the genuine projected endpoint probabilities. -/
theorem probabilityLaw_tendsto [IsProbabilityMeasure μ] :
    Tendsto (fun n => probabilityLaw hN (PeriodicParticle.interaction_smooth hb n)
      (PeriodicParticle.interaction_bounds hb hbound hL₁ hL₂ n) hM hL₁ hL₂ hT ξ μ A ht)
      atTop (𝓝 (probabilityLaw hN hb hbound hM hL₁ hL₂ hT ξ μ A ht)) := by
  let P : ProbabilityMeasure (Point (N*d) × C(Icc 0 T,Point (N*d))) := ⟨μ.prod ξ,inferInstance⟩
  exact probabilityMeasure_map_tendsto P
    (fun n => (A.continuous.comp (endpoint_continuous hN (PeriodicParticle.interaction_smooth hb n)
      (PeriodicParticle.interaction_bounds hb hbound hL₁ hL₂ n) hM hL₁ hL₂ hT ht)).measurable)
    (A.continuous.comp (endpoint_continuous hN hb hbound hM hL₁ hL₂ hT ht)).measurable
    (Eventually.of_forall (fun q => A.continuous.continuousAt.tendsto.comp
      (flow_tendsto hN hb hbound hM hL₁ hL₂ hT q.1 q.2 ht)))

/-- After actual law and source convergence are proved, any independently
supplied uniform projected-energy bound passes to the original particle source.
This theorem does not assert or assume the manuscript's sharp estimate. -/
theorem energy_bound_of_periodic_bounds [IsProbabilityMeasure μ]
    (u : Point (N*d) → Point (N*d)) (hu : MemLp u 2 μ) {C : ℝ}
    (hC : ∀ᶠ n in atTop,
      energy (law hN (PeriodicParticle.interaction_smooth hb n)
        (PeriodicParticle.interaction_bounds hb hbound hL₁ hL₂ n) hM hL₁ hL₂ hT ξ μ A (t := t))
        (source hN (PeriodicParticle.interaction_smooth hb n)
          (PeriodicParticle.interaction_bounds hb hbound hL₁ hL₂ n) hM hL₁ hL₂ hT ξ μ A ht u hu) ≤ C) :
    FiniteEnergy (law hN hb hbound hM hL₁ hL₂ hT ξ μ A (t := t))
      (source hN hb hbound hM hL₁ hL₂ hT ξ μ A ht u hu) ∧
    energy (law hN hb hbound hM hL₁ hL₂ hT ξ μ A (t := t))
      (source hN hb hbound hM hL₁ hL₂ hT ξ μ A ht u hu) ≤ C := by
  apply WeightedTangent.finiteEnergy_bound_of_tendsto
    (probabilityLaw_tendsto hN hb hbound hM hL₁ hL₂ hT ξ μ A ht)
    (source_tendsto hN hb hbound hM hL₁ hL₂ hT ξ μ A ht u hu)
  filter_upwards [hC] with n hn
  exact ⟨source_finiteEnergy hN (PeriodicParticle.interaction_smooth hb n)
    (PeriodicParticle.interaction_bounds hb hbound hL₁ hL₂ n) hM hL₁ hL₂ hT ξ μ A ht u hu,hn⟩

end SharpWasserstein.PeriodicParticleTangentLimit
