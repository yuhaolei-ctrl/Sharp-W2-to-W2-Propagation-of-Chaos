import SharpWasserstein.PeriodicParticleTangentLimitFlow
import SharpWasserstein.PropagatedFlux

/-! Actual projected particle-flow laws and JV source distributions. Every
source is defined by a genuine L² random flux under the original input law. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal Topology ContDiff InnerProductSpace
namespace SharpWasserstein.PeriodicParticleTangentLimit
open WeightedTangent FlowInitialDerivative
variable {d N m : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  [MeasurableSpace (Point m)] [BorelSpace (Point m)]
  {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
  (hN : 0 < N) (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
  (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) {T : ℝ} (hT : 0 ≤ T)
  (ξ : Measure C(Icc 0 T,Point (N*d))) [IsProbabilityMeasure ξ]
  (μ : Measure (Point (N*d))) [IsFiniteMeasure μ]
  (A : Point (N*d) →L[ℝ] Point m) {t : ℝ} (ht : t ∈ Icc 0 T)

def endpoint (q : Point (N*d) × C(Icc 0 T,Point (N*d))) : Point (N*d) :=
  flow hN hb hbound hM hL₁ hL₂ hT q.1 q.2 t

def flux (u : Point (N*d) → Point (N*d)) (q : Point (N*d) × C(Icc 0 T,Point (N*d))) : Point (N*d) :=
  fderiv ℝ (fun y => flow hN hb hbound hM hL₁ hL₂ hT y q.2 t) q.1 (u q.1)

include ht in
omit [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))] in
theorem endpoint_continuous : Continuous (endpoint hN hb hbound hM hL₁ hL₂ hT (t := t)) :=
  BoundedFlow.flow_continuous (v := fun _ : ℝ => drift (N := N) b)
    ((drift_lipschitz hN hb hbound hL₁ hL₂).continuous.comp continuous_snd)
    (fun _ => drift_norm_le hN hbound hM) (fun _ => drift_lipschitz hN hb hbound hL₁ hL₂) hT ht

include ht in
omit [IsFiniteMeasure μ] in
theorem flux_memLp {u : Point (N*d) → Point (N*d)} (hu : MemLp u 2 μ) :
    MemLp (flux hN hb hbound hM hL₁ hL₂ hT (t := t) u) 2 (μ.prod ξ) :=
  boundedFlow_fderiv_apply_memLp
    ((drift_lipschitz hN hb hbound hL₁ hL₂).continuous.comp continuous_snd)
    (fun _ => drift_norm_le hN hbound hM) (fun _ => drift_lipschitz hN hb hbound hL₁ hL₂)
    (drift_smooth hb) (drift_allDerivativesBounded hb) hT ht (μ.prod ξ)
    (hu.comp_measurePreserving (measurePreserving_fst (μ := μ) (ν := ξ)))

/-- The carrying law is the actual projected random endpoint law. -/
def law : Measure (Point m) :=
  (μ.prod ξ).map (fun q => A (endpoint hN hb hbound hM hL₁ hL₂ hT (t := t) q))

include ht in
omit [IsFiniteMeasure μ] in
theorem law_probability [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (law hN hb hbound hM hL₁ hL₂ hT ξ μ A (t := t)) :=
  Measure.isProbabilityMeasure_map
    (A.continuous.comp (endpoint_continuous hN hb hbound hM hL₁ hL₂ hT ht)).measurable.aemeasurable

/-- The law with its actual probability proof, for the narrow topology. -/
def probabilityLaw [IsProbabilityMeasure μ] : ProbabilityMeasure (Point m) :=
  ⟨law hN hb hbound hM hL₁ hL₂ hT ξ μ A (t := t),law_probability hN hb hbound hM hL₁ hL₂ hT ξ μ A ht⟩

/-- The genuine projected Jacobian-flux source; A may be a coordinate marginal. -/
def source (u : Point (N*d) → Point (N*d)) (hu : MemLp u 2 μ) : Test m →ₗ[ℝ] ℝ :=
  PropagatedFlux.source (μ.prod ξ)
    (fun q => A (endpoint hN hb hbound hM hL₁ hL₂ hT (t := t) q))
    (A.continuous.comp (endpoint_continuous hN hb hbound hM hL₁ hL₂ hT ht)).measurable
    (((flux_memLp hN hb hbound hM hL₁ hL₂ hT ξ μ ht hu).continuousLinearMap_comp A).toLp
      (fun q => A (flux hN hb hbound hM hL₁ hL₂ hT (t := t) u q)))

/-- Exact literal pairing, retaining the original initial field and path probability. -/
theorem source_apply (u : Point (N*d) → Point (N*d)) (hu : MemLp u 2 μ) (φ : Test m) :
    source hN hb hbound hM hL₁ hL₂ hT ξ μ A ht u hu φ =
      ∫ q, fderiv ℝ (φ : Point m → ℝ) (A (endpoint hN hb hbound hM hL₁ hL₂ hT (t := t) q))
        (A (flux hN hb hbound hM hL₁ hL₂ hT (t := t) u q)) ∂μ.prod ξ := by
  rw [source,PropagatedFlux.source_apply]
  apply integral_congr_ae
  filter_upwards [((flux_memLp hN hb hbound hM hL₁ hL₂ hT ξ μ ht hu).continuousLinearMap_comp A).coeFn_toLp]
    with q hq
  rw [hq,inner_gradient_left]

theorem source_finiteEnergy (u : Point (N*d) → Point (N*d)) (hu : MemLp u 2 μ) :
    FiniteEnergy (law hN hb hbound hM hL₁ hL₂ hT ξ μ A (t := t))
      (source hN hb hbound hM hL₁ hL₂ hT ξ μ A ht u hu) :=
  PropagatedFlux.source_finiteEnergy _ _ _ _

include ht in
omit [MeasurableSpace (Point m)] [BorelSpace (Point m)] in
/-- Every projected compact-test pairing is an ordinary finite Bochner integral. -/
theorem pairing_integrable {F : Point m → ℝ} (hF : ContDiff ℝ 1 F) {L : ℝ≥0}
    (hL : ∀ y, ‖fderiv ℝ F y‖ ≤ L) {u : Point (N*d) → Point (N*d)} (hu : MemLp u 2 μ) :
    Integrable (fun q => fderiv ℝ F (A (endpoint hN hb hbound hM hL₁ hL₂ hT (t := t) q))
      (A (flux hN hb hbound hM hL₁ hL₂ hT (t := t) u q))) (μ.prod ξ) := by
  have hp := (flux_memLp hN hb hbound hM hL₁ hL₂ hT ξ μ ht hu).continuousLinearMap_comp A
  have hm : AEStronglyMeasurable
      (fun q => fderiv ℝ F (A (endpoint hN hb hbound hM hL₁ hL₂ hT (t := t) q))) (μ.prod ξ) :=
    ((hF.continuous_fderiv (by norm_num)).comp
      (A.continuous.comp (endpoint_continuous hN hb hbound hM hL₁ hL₂ hT ht))).aestronglyMeasurable
  apply Integrable.mono' ((hp.integrable (by norm_num)).norm.const_mul (L:ℝ))
    ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable (hm.prodMk hp.1))
  exact Eventually.of_forall (fun q => (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (hL _) (norm_nonneg _)))

end SharpWasserstein.PeriodicParticleTangentLimit
