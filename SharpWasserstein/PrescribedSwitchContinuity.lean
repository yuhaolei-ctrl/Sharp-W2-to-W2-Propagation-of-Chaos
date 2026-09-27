import SharpWasserstein.PrescribedSwitchBrownianLaw
import SharpWasserstein.SwitchCurveNarrow
import SharpWasserstein.RoughEulerianTransportContinuity

/-! The actual prescribed switch curve satisfies the compact-test continuity
equation with precisely the Brownian-propagated current whose energy is
estimated by the hierarchy. Time clamping supplies a continuous global curve. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal ContDiff Interval Topology
namespace SharpWasserstein.SwitchSourceDerivative
open WeightedTangent
variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
  (hN : 0 < N) (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
  (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
  {μ : ℝ → Measure (Position d)} (hμ : IsLimitEvolution b μ)
  {T : ℝ} (hT : 0 ≤ T) (P : Measure (Configuration d N)) [IsProbabilityMeasure P]

def prescribedEuclideanCurve (s : ℝ) : ProbabilityMeasure (Point (N*d)) := by
  let r := projIcc 0 T hT s
  letI : IsProbabilityMeasure (PrescribedSwitchCurve.law hN hb hbound hM hL₁ hL₂ hμ hT P r) :=
    SwitchCurve.law_probability hN hb hbound hM hL₁ hL₂ _ _ _ hT P r.property
  exact ⟨euclideanLaw (PrescribedSwitchCurve.law hN hb hbound hM hL₁ hL₂ hμ hT P r),inferInstance⟩

theorem prescribedEuclideanCurve_continuous :
    Continuous (prescribedEuclideanCurve hN hb hbound hM hL₁ hL₂ hμ hT P) := by
  exact (ProbabilityMeasure.continuous_map (configurationEuclidean d N).continuous).comp
    ((SwitchCurve.probabilityCurve_continuous hN hb hbound hM hL₁ hL₂
      (DecoupledFlow.liftDrift_continuous N (PrescribedReference.singleDrift_continuous hb hbound hL₁ hμ))
      (DecoupledFlow.liftDrift_bound N (PrescribedReference.singleDrift_bound hbound hM hμ))
      (DecoupledFlow.liftDrift_lipschitz N (PrescribedReference.singleDrift_lipschitz hb hbound hL₁ hμ)) hT P).comp
        (continuous_projIcc (h := hT)))

theorem prescribedBrownianSource_clamped_pairing (s : ℝ) (φ : Test (N*d)) :
    prescribedBrownianSource hN hb hbound hM hL₁ hL₂ hμ hT P s φ =
      prescribedSourcePairing hN hb hbound hM hL₁ hL₂ hμ hT P
        ((φ : Point (N*d) → ℝ) ∘ configurationEuclidean d N) (projIcc 0 T hT s) := by
  have he := prescribedBrownianSource_pairing hN hb hbound hM hL₁ hL₂ hμ hT P
    (projIcc 0 T hT s).property φ
  simpa only [prescribedBrownianSource,projIcc_of_mem _ (projIcc 0 T hT s).property] using he

theorem prescribedBrownianSource_continuous (φ : Test (N*d)) :
    Continuous (fun s => prescribedBrownianSource hN hb hbound hM hL₁ hL₂ hμ hT P s φ) := by
  let ψ := (configurationTestEuclidean d N).symm φ
  obtain ⟨C,L,hC,hL⟩ := configuration_compact_test_bounds ψ.property
  have hc := sourcePairing_continuousOn (A := NNReal.mk M hM)
    (particleDrift_norm_bound hN hbound hM) (particleDrift_lipschitz hN hb hbound hL₁ hL₂)
    (DecoupledFlow.liftDrift_continuous N (PrescribedReference.singleDrift_continuous hb hbound hL₁ hμ))
    (DecoupledFlow.liftDrift_bound N (PrescribedReference.singleDrift_bound hbound hM hμ))
    (DecoupledFlow.liftDrift_lipschitz N (PrescribedReference.singleDrift_lipschitz hb hbound hL₁ hμ))
    hT (particleDrift_smooth hb) (particleDrift_allDerivativesBounded hb) P
    (ψ.property.1.of_le (by simp)) hC hL
  have hd := (continuousOn_iff_continuous_restrict.mp (hc.mono Icc_subset_Ici_self)).comp
    (continuous_projIcc (h := hT))
  convert hd using 1
  funext s
  exact prescribedBrownianSource_clamped_pairing hN hb hbound hM hL₁ hL₂ hμ hT P s φ

theorem prescribedEuclideanCurve_sub_eq_integral (φ : Test (N*d))
    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (hst : s ≤ t) :
    (∫ x,(φ : Point (N*d) → ℝ) x ∂(prescribedEuclideanCurve hN hb hbound hM hL₁ hL₂ hμ hT P t : Measure _))-
      (∫ x,(φ : Point (N*d) → ℝ) x ∂(prescribedEuclideanCurve hN hb hbound hM hL₁ hL₂ hμ hT P s : Measure _)) =
        ∫ r in s..t,prescribedBrownianSource hN hb hbound hM hL₁ hL₂ hμ hT P r φ := by
  let ψ := (configurationTestEuclidean d N).symm φ
  have he := prescribed_switch_compact_sub_eq_integral hN hb hbound hM hL₁ hL₂ hμ hT P
    ψ.property hs ht hst
  simp only [prescribedEuclideanCurve,projIcc_of_mem _ hs,projIcc_of_mem _ ht,
    ProbabilityMeasure.coe_mk,integral_euclideanLaw]
  refine he.trans ?_
  apply intervalIntegral.integral_congr
  intro r hr
  have hr' : r ∈ Icc 0 T := ⟨hs.1.trans ((uIcc_of_le hst ▸ hr).1),
    ((uIcc_of_le hst ▸ hr).2).trans ht.2⟩
  exact (prescribedBrownianSource_pairing hN hb hbound hM hL₁ hL₂ hμ hT P hr' φ).symm

theorem prescribed_compactDistributionContinuity :
    RoughEulerianTransport.CompactDistributionContinuity
      (prescribedEuclideanCurve hN hb hbound hM hL₁ hL₂ hμ hT P)
      (prescribedBrownianSource hN hb hbound hM hL₁ hL₂ hμ hT P) T := by
  refine ⟨prescribedEuclideanCurve_continuous hN hb hbound hM hL₁ hL₂ hμ hT P,?_⟩
  intro φ s hs t ht
  refine ⟨(prescribedBrownianSource_continuous hN hb hbound hM hL₁ hL₂ hμ hT P φ).intervalIntegrable s t,?_⟩
  rcases le_total s t with hst | hts
  · exact prescribedEuclideanCurve_sub_eq_integral hN hb hbound hM hL₁ hL₂ hμ hT P φ hs ht hst
  · have he := prescribedEuclideanCurve_sub_eq_integral hN hb hbound hM hL₁ hL₂ hμ hT P φ ht hs hts
    rw [intervalIntegral.integral_symm]
    linarith

end SharpWasserstein.SwitchSourceDerivative
