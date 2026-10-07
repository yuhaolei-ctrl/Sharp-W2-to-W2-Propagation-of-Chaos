module

public import SharpWasserstein.Compat
public import SharpWasserstein.PeriodicParticleTangentLimitIdentification
public import SharpWasserstein.PeriodicMarginalCoefficientEvolutionConsistency

@[expose] public section

/-! Exact identification of the source used by the Brownian finite hierarchy
with the projected random Jacobian flux used by the sine-periodization limit.
The same initial L² field is used on both sides. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal Topology ContDiff InnerProductSpace
namespace SharpWasserstein.BrownianEnergyPeriodization
open WeightedTangent PropagatedSourceEquation PeriodicParticleTangentLimit
open InitialSourceMarginal PeriodicMarginalCoefficientEvolution

variable {d N m : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  [MeasurableSpace (Point m)] [BorelSpace (Point m)]
  {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
  (hN : 0 < N) (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
  (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) {T : ℝ} (hT : 0 ≤ T)
  (μ : Measure (Point (N*d))) [IsFiniteMeasure μ]

/-- Instance shortcut (port to Lean 4.35): typeclass search no longer unifies the continuity
proof `(drift_lipschitz ..).continuous.comp continuous_snd : Continuous (drift b ∘ Prod.snd)`
with the expected `Continuous (Function.uncurry ..)` at instance transparency, so the general
instance `Brownian.lawAt_isFiniteMeasure` is restated with the hypotheses in that form. -/
instance driftLawAt_isFiniteMeasure {b' : Position d → Position d → Position d} {M' K' : ℝ≥0}
    (hv' : Continuous (drift (N := N) b' ∘ Prod.snd))
    (hb' : ∀ (_ : ℝ) (y : Point (N*d)), ‖drift b' y‖ ≤ M')
    (hl' : ∀ _ : ℝ, LipschitzWith K' (drift (N := N) b')) {T' : ℝ} (hT' : 0 ≤ T')
    (ν : Measure (Point (N*d))) [IsFiniteMeasure ν] (t : ℝ) :
    IsFiniteMeasure (Brownian.lawAt hv' hb' hl' hT' ν t) :=
  Brownian.lawAt_isFiniteMeasure _ _ _ hT' ν t

instance projectedLaw_isFiniteMeasure
    (ξ : Measure C(Icc 0 T,Point (N*d))) [IsProbabilityMeasure ξ]
    (A : Point (N*d) →L[ℝ] Point m) (t : ℝ) :
    IsFiniteMeasure (law hN hb hbound hM hL₁ hL₂ hT ξ μ A (t := t)) := by
  unfold law
  infer_instance

omit [MeasurableSpace (Point m)] [BorelSpace (Point m)] in
/-- The full carrying law is exactly the clamped Brownian law at a valid time. -/
theorem fullLaw_eq_brownianLawAt {t : ℝ} (ht : t ∈ Icc 0 T) :
    law hN hb hbound hM hL₁ hL₂ hT (euclideanBrownianPathLaw d N T) μ
      (ContinuousLinearMap.id ℝ (Point (N*d))) (t := t) =
    Brownian.lawAt
      ((drift_lipschitz hN hb hbound hL₁ hL₂).continuous.comp continuous_snd)
      (fun _ => drift_norm_le hN hbound hM) (fun _ => drift_lipschitz hN hb hbound hL₁ hL₂)
      hT μ t := by
  simp only [law,Brownian.lawAt,projIcc_of_mem _ ht,ContinuousLinearMap.id_apply]
  rfl

/-- Projection of the random endpoint law is the actual projected carrying law. -/
theorem projectedLaw_eq_map_fullLaw
    (ξ : Measure C(Icc 0 T,Point (N*d))) [IsProbabilityMeasure ξ]
    (A : Point (N*d) →L[ℝ] Point m) {t : ℝ} (ht : t ∈ Icc 0 T) :
    law hN hb hbound hM hL₁ hL₂ hT ξ μ A (t := t) =
      (law hN hb hbound hM hL₁ hL₂ hT ξ μ (ContinuousLinearMap.id ℝ (Point (N*d))) (t := t)).map A := by
  simp only [law,ContinuousLinearMap.id_apply]
  rw [Measure.map_map A.continuous.measurable
    (endpoint_continuous hN hb hbound hM hL₁ hL₂ hT ht).measurable]
  rfl

/-- Canonical marginalization of the full random-flux source is exactly the
original projected random flux, by the proved bounded-cylinder pairing. -/
theorem projectedSource_eq_imageSource_full
    (ξ : Measure C(Icc 0 T,Point (N*d))) [IsProbabilityMeasure ξ]
    (A : Point (N*d) →L[ℝ] Point m) {t : ℝ} (ht : t ∈ Icc 0 T)
    (u : Point (N*d) → Point (N*d)) (hu : MemLp u 2 μ) :
    source hN hb hbound hM hL₁ hL₂ hT ξ μ A ht u hu =
      imageSource (law hN hb hbound hM hL₁ hL₂ hT ξ μ
        (ContinuousLinearMap.id ℝ (Point (N*d))) (t := t))
        (source hN hb hbound hM hL₁ hL₂ hT ξ μ
          (ContinuousLinearMap.id ℝ (Point (N*d))) ht u hu) A := by
  ext φ
  rw [source_apply,imageSource_apply]
  obtain ⟨hf,hfa,hfb⟩ := cylinder_bounds A φ
  have hV := flux_memLp hN hb hbound hM hL₁ hL₂ hT ξ μ ht hu
  have he := PropagatedFlux.representative_bounded_smooth_pairing (μ.prod ξ)
    (endpoint hN hb hbound hM hL₁ hL₂ hT (t := t))
    (endpoint_continuous hN hb hbound hM hL₁ hL₂ hT ht).measurable (hV.toLp _) hf hfa hfb
  change _ = ∫ x,⟪gradient (φ.val ∘ A) x,
    (WeightedTangent.representative ((μ.prod ξ).map (endpoint hN hb hbound hM hL₁ hL₂ hT (t := t)))
      (PropagatedFlux.source (μ.prod ξ) (endpoint hN hb hbound hM hL₁ hL₂ hT (t := t))
        (endpoint_continuous hN hb hbound hM hL₁ hL₂ hT ht).measurable (hV.toLp _))).val x⟫_ℝ
      ∂(μ.prod ξ).map (endpoint hN hb hbound hM hL₁ hL₂ hT (t := t))
  rw [he]
  apply integral_congr_ae
  filter_upwards [hV.coeFn_toLp] with q hq
  rw [hq,inner_gradient_left,fderiv_comp _ (test_differentiable φ _) A.differentiableAt,
    ContinuousLinearMap.fderiv]
  rfl

/-- Exact Brownian source identity used to transfer the hierarchy to the
existing genuine Jacobian convergence theorem. -/
theorem projectedSource_eq_brownianImage
    (A : Point (N*d) →L[ℝ] Point m) {t : ℝ} (ht : t ∈ Icc 0 T)
    (u : Point (N*d) → Point (N*d)) (hu : MemLp u 2 μ) :
    source hN hb hbound hM hL₁ hL₂ hT (euclideanBrownianPathLaw d N T) μ A ht u hu =
      imageSource (Brownian.lawAt
        ((drift_lipschitz hN hb hbound hL₁ hL₂).continuous.comp continuous_snd)
        (fun _ => drift_norm_le hN hbound hM) (fun _ => drift_lipschitz hN hb hbound hL₁ hL₂) hT μ t)
      (Brownian.sourceAt
        ((drift_lipschitz hN hb hbound hL₁ hL₂).continuous.comp continuous_snd)
        (fun _ => drift_norm_le hN hbound hM) (fun _ => drift_lipschitz hN hb hbound hL₁ hL₂)
        hT (particleDrift_smooth hb) (particleDrift_allDerivativesBounded hb) μ u hu t) A := by
  rw [projectedSource_eq_imageSource_full,fullSource_eq_brownianSourceAt]
  simp only [fullLaw_eq_brownianLawAt hN hb hbound hM hL₁ hL₂ hT μ ht]

/-- Exact Brownian carrying-law identity for every linear observation. -/
theorem projectedLaw_eq_brownianMap
    (A : Point (N*d) →L[ℝ] Point m) {t : ℝ} (ht : t ∈ Icc 0 T) :
    law hN hb hbound hM hL₁ hL₂ hT (euclideanBrownianPathLaw d N T) μ A (t := t) =
      (Brownian.lawAt
        ((drift_lipschitz hN hb hbound hL₁ hL₂).continuous.comp continuous_snd)
        (fun _ => drift_norm_le hN hbound hM) (fun _ => drift_lipschitz hN hb hbound hL₁ hL₂) hT μ t).map A := by
  rw [projectedLaw_eq_map_fullLaw hN hb hbound hM hL₁ hL₂ hT μ _ A ht,
    fullLaw_eq_brownianLawAt hN hb hbound hM hL₁ hL₂ hT μ ht]

end SharpWasserstein.BrownianEnergyPeriodization
