import SharpWasserstein.PrescribedSwitchMarginalSource
import SharpWasserstein.PrescribedSwitchContinuity

/-! The genuine marginal switch curve satisfies compact-distribution
continuity with its actual canonical marginal source. Source continuity and
the integrated equation are derived with bounded full-space cylinders. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal ContDiff InnerProductSpace Topology Interval
namespace SharpWasserstein.SwitchSourceDerivative
open WeightedTangent PropagatedSourceEquation PeriodicParticleTangentLimit InitialSourcePermutation
open NoiseAverage InitialSourceMarginal
variable {d N k : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  [MeasurableSpace (Point (k*d))] [BorelSpace (Point (k*d))]
  {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
  (hN : 0 < N) (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
  (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
  {μ : ℝ → Measure (Position d)} (hμ : IsLimitEvolution b μ)
  {T : ℝ} (hT : 0 ≤ T) (P : Measure (Configuration d N)) [IsProbabilityMeasure P]

def prescribedMarginalCurve (hk : k ≤ N) (s : ℝ) : ProbabilityMeasure (Point (k*d)) :=
  (prescribedEuclideanCurve hN hb hbound hM hL₁ hL₂ hμ hT P s).map
    (marginalProjection hk).continuous.measurable.aemeasurable

theorem prescribedMarginalCurve_continuous (hk : k ≤ N) :
    Continuous (prescribedMarginalCurve hN hb hbound hM hL₁ hL₂ hμ hT P hk) :=
  (ProbabilityMeasure.continuous_map (marginalProjection hk).continuous).comp
    (prescribedEuclideanCurve_continuous hN hb hbound hM hL₁ hL₂ hμ hT P)

/-- Exact physical-interval measure identity for the transport/source energy. -/
theorem prescribedMarginalCurve_coe (hk : k ≤ N) {s : ℝ} (hs : s ∈ Icc 0 T) :
    (prescribedMarginalCurve hN hb hbound hM hL₁ hL₂ hμ hT P hk s : Measure _) =
      (euclideanLaw (PrescribedSwitchCurve.law hN hb hbound hM hL₁ hL₂ hμ hT P s)).map
        (marginalProjection hk) := by
  simp only [prescribedMarginalCurve,ProbabilityMeasure.toMeasure_map,prescribedEuclideanCurve,
    projIcc_of_mem _ hs,ProbabilityMeasure.coe_mk]

/-- Genuine bounded C¹ cylinder data used by the actual switch equation. -/
theorem marginal_configuration_test_bounds (hk : k ≤ N) (φ : Test (k*d)) :
    let F := (φ.val ∘ marginalProjection hk) ∘ configurationEuclidean d N
    ContDiff ℝ 1 F ∧ ∃ (C : ℝ) (L : ℝ≥0),
      (∀ x,‖F x‖ ≤ C) ∧ (∀ x,‖fderiv ℝ F x‖ ≤ L) := by
  have hf := φ.property.1.comp (marginalProjection hk).contDiff
  have hF := hf.comp (configurationEuclidean d N).contDiff
  have hB := ((RoughEulerianSmoothing.allDerivativesBounded_of_compact
    φ.property.1 φ.property.2).comp_linear φ.property.1 (marginalProjection hk)).comp_linear
      hf (configurationEuclidean d N).toContinuousLinearMap
  obtain ⟨C,_,hC⟩ := hB.bounded
  obtain ⟨L,hL,hLf⟩ := hB.fderiv.bounded
  exact ⟨hF.of_le (by simp),C,⟨L,hL⟩,hC,hLf⟩

theorem prescribedMarginalSource_clamped_pairing (hk : k ≤ N) (s : ℝ) (φ : Test (k*d)) :
    prescribedMarginalSource hN hb hbound hM hL₁ hL₂ hμ hT P hk s φ =
      prescribedSourcePairing hN hb hbound hM hL₁ hL₂ hμ hT P
        ((φ.val ∘ marginalProjection hk) ∘ configurationEuclidean d N) (projIcc 0 T hT s) := by
  have he := prescribedMarginalSource_pairing hN hb hbound hM hL₁ hL₂ hμ hT P hk
    (projIcc 0 T hT s).property φ
  simpa only [prescribedMarginalSource,projIcc_of_mem _ (projIcc 0 T hT s).property] using he

theorem prescribedMarginalSource_continuous (hk : k ≤ N) (φ : Test (k*d)) :
    Continuous (fun s => prescribedMarginalSource hN hb hbound hM hL₁ hL₂ hμ hT P hk s φ) := by
  obtain ⟨hF,C,L,hC,hL⟩ := marginal_configuration_test_bounds hk φ
  have hc := sourcePairing_continuousOn (A := NNReal.mk M hM)
    (particleDrift_norm_bound hN hbound hM) (particleDrift_lipschitz hN hb hbound hL₁ hL₂)
    (DecoupledFlow.liftDrift_continuous N (PrescribedReference.singleDrift_continuous hb hbound hL₁ hμ))
    (DecoupledFlow.liftDrift_bound N (PrescribedReference.singleDrift_bound hbound hM hμ))
    (DecoupledFlow.liftDrift_lipschitz N (PrescribedReference.singleDrift_lipschitz hb hbound hL₁ hμ))
    hT (particleDrift_smooth hb) (particleDrift_allDerivativesBounded hb) P hF hC hL
  have hd := (continuousOn_iff_continuous_restrict.mp (hc.mono Icc_subset_Ici_self)).comp
    (continuous_projIcc (h := hT))
  convert hd using 1
  funext s
  exact prescribedMarginalSource_clamped_pairing hN hb hbound hM hL₁ hL₂ hμ hT P hk s φ

theorem prescribedMarginalCurve_integral (hk : k ≤ N) (φ : Test (k*d))
    {s : ℝ} (hs : s ∈ Icc 0 T) :
    (∫ y,φ.val y ∂(prescribedMarginalCurve hN hb hbound hM hL₁ hL₂ hμ hT P hk s : Measure _)) =
      ∫ x,((φ.val ∘ marginalProjection hk) ∘ configurationEuclidean d N) x
        ∂PrescribedSwitchCurve.law hN hb hbound hM hL₁ hL₂ hμ hT P s := by
  simp only [prescribedMarginalCurve,ProbabilityMeasure.toMeasure_map]
  rw [integral_map (marginalProjection hk).continuous.measurable.aemeasurable
    φ.property.1.continuous.aestronglyMeasurable]
  simp only [prescribedEuclideanCurve,projIcc_of_mem _ hs,ProbabilityMeasure.coe_mk,integral_euclideanLaw]
  rfl

/-- The marginal source equation includes both actual endpoints. -/
theorem prescribedMarginalCurve_sub_eq_integral (hk : k ≤ N) (φ : Test (k*d))
    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (hst : s ≤ t) :
    (∫ x,φ.val x ∂(prescribedMarginalCurve hN hb hbound hM hL₁ hL₂ hμ hT P hk t : Measure _))-
      (∫ x,φ.val x ∂(prescribedMarginalCurve hN hb hbound hM hL₁ hL₂ hμ hT P hk s : Measure _)) =
        ∫ r in s..t,prescribedMarginalSource hN hb hbound hM hL₁ hL₂ hμ hT P hk r φ := by
  obtain ⟨hF,C,L,hC,hL⟩ := marginal_configuration_test_bounds hk φ
  rw [prescribedMarginalCurve_integral hN hb hbound hM hL₁ hL₂ hμ hT P hk φ ht,
    prescribedMarginalCurve_integral hN hb hbound hM hL₁ hL₂ hμ hT P hk φ hs]
  have he := prescribed_switch_sub_eq_integral hN hb hbound hM hL₁ hL₂ hμ hT P hF hC hL hs ht hst
  refine he.trans ?_
  apply intervalIntegral.integral_congr
  intro r hr
  have hr' : r ∈ Icc 0 T := ⟨hs.1.trans ((uIcc_of_le hst ▸ hr).1),
    ((uIcc_of_le hst ▸ hr).2).trans ht.2⟩
  exact (prescribedMarginalSource_pairing hN hb hbound hM hL₁ hL₂ hμ hT P hk hr' φ).symm

/-- Actual narrow continuity and the genuine compact-test source equation,
ready for the finite-action Eulerian transport theorem. -/
theorem prescribed_marginal_compactDistributionContinuity (hk : k ≤ N) :
    RoughEulerianTransport.CompactDistributionContinuity
      (prescribedMarginalCurve hN hb hbound hM hL₁ hL₂ hμ hT P hk)
      (prescribedMarginalSource hN hb hbound hM hL₁ hL₂ hμ hT P hk) T := by
  refine ⟨prescribedMarginalCurve_continuous hN hb hbound hM hL₁ hL₂ hμ hT P hk,?_⟩
  intro φ s hs t ht
  refine ⟨(prescribedMarginalSource_continuous hN hb hbound hM hL₁ hL₂ hμ hT P hk φ).intervalIntegrable s t,?_⟩
  rcases le_total s t with hst | hts
  · exact prescribedMarginalCurve_sub_eq_integral hN hb hbound hM hL₁ hL₂ hμ hT P hk φ hs ht hst
  · have he := prescribedMarginalCurve_sub_eq_integral hN hb hbound hM hL₁ hL₂ hμ hT P hk φ ht hs hts
    rw [intervalIntegral.integral_symm]
    linarith

end SharpWasserstein.SwitchSourceDerivative
