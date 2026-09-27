import SharpWasserstein.RegularizedBrownianSourceBound
import SharpWasserstein.PrescribedSwitchBrownianLaw

/-! The singular source-energy bound on the actual prescribed switch curve,
with the actual source already identified as its scalar time derivative. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace NNReal ENNReal
namespace SharpWasserstein.RegularizedBrownianSource
open WeightedTangent InitialSourcePermutation InitialSourceMarginal
open PeriodicParticleTangentLimit SwitchSourceDerivative

/-- Energy of a genuine observed source respects equality of carrying laws. -/
theorem imageEnergy_measure_congr {n k : ℕ} (ν τ : Measure (Point n))
    [IsFiniteMeasure ν] [IsFiniteMeasure τ] (h : ν=τ)
    (σ : Test n →ₗ[ℝ] ℝ) (A : Point n →L[ℝ] Point k) :
    energy (ν.map A) (imageSource ν σ A) = energy (τ.map A) (imageSource τ σ A) := by
  subst τ
  rfl

variable {d N : ℕ} {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
  (hN : 0 < N) (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
  (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
  {μ : ℝ → Measure (Position d)} (hμ : IsLimitEvolution b μ)
  {T : ℝ} (hT : 0 ≤ T) (P : Measure (Configuration d N)) [IsProbabilityMeasure P]
  (hP : HasSecondMoment P)

/-- The energy carrying the actual switch derivative is the exact full
Euclidean propagated prefix energy bounded above. -/
theorem prescribed_marginal_energy_eq_prefix {s : ℝ} (hs : s ∈ Icc 0 T) {k : ℕ} (hk : k ≤ N) :
    letI : IsProbabilityMeasure (PrescribedSwitchCurve.law hN hb hbound hM hL₁ hL₂ hμ hT P s) :=
      SwitchCurve.law_probability hN hb hbound hM hL₁ hL₂ _ _ _ hT P hs
    letI : IsProbabilityMeasure (PrescribedReference.law hb hbound hM hL₁ hμ N P s) :=
      law_probability hb hbound hM hL₁ hμ P hP hs.1
    energy ((euclideanLaw (PrescribedSwitchCurve.law hN hb hbound hM hL₁ hL₂ hμ hT P s)).map (marginalProjection hk))
      (imageSource (euclideanLaw (PrescribedSwitchCurve.law hN hb hbound hM hL₁ hL₂ hμ hT P s))
        (prescribedBrownianSource hN hb hbound hM hL₁ hL₂ hμ hT P s) (marginalProjection hk)) =
    BrownianEnergyPeriodization.prefixEnergy hN hb hbound hM hL₁ hL₂ hT
      (euclideanLaw (PrescribedReference.law hb hbound hM hL₁ hμ N P s)) hk
      (euclideanFlux (initialCurrent b (μ s))) (current_memLp hb hbound hM hL₁ hμ P hP hN hs.1) (T-s) := by
  letI : IsProbabilityMeasure (PrescribedSwitchCurve.law hN hb hbound hM hL₁ hL₂ hμ hT P s) :=
    SwitchCurve.law_probability hN hb hbound hM hL₁ hL₂ _ _ _ hT P hs
  letI := law_probability hb hbound hM hL₁ hμ P hP hs.1
  have hσ : prescribedBrownianSource hN hb hbound hM hL₁ hL₂ hμ hT P s =
      BrownianEnergyPeriodization.propagatedSource hN hb hbound hM hL₁ hL₂ hT
        (euclideanLaw (PrescribedReference.law hb hbound hM hL₁ hμ N P s))
        (euclideanFlux (initialCurrent b (μ s))) (current_memLp hb hbound hM hL₁ hμ P hP hN hs.1) (T-s) := by
    unfold prescribedBrownianSource
    simp only [projIcc_of_mem _ hs]
    rfl
  rw [hσ]
  exact imageEnergy_measure_congr _ _
    (prescribedBrownianSource_lawAt hN hb hbound hM hL₁ hL₂ hμ hT P hs).symm _ _

include hP in
/-- Sharp energy bound for the actual marginal switch derivative at every
positive switch time. The initial Wasserstein profile is the only quantitative
initial assumption. -/
theorem prescribed_marginal_energy_le (hex : Exchangeable P) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hinit : ∀ j,∀ hj : j ≤ N,wassersteinSq (marginal hj P) (tensorLaw (μ 0) j) ≤
      ENNReal.ofReal (C₀*(j:ℝ)^2/(N:ℝ)^2))
    {s : ℝ} (hs : 0 < s) (hsT : s ≤ T) {k : ℕ} (hkpos : 1 ≤ k) (hk : k ≤ N) :
    letI : IsProbabilityMeasure (PrescribedSwitchCurve.law hN hb hbound hM hL₁ hL₂ hμ hT P s) :=
      SwitchCurve.law_probability hN hb hbound hM hL₁ hL₂ _ _ _ hT P ⟨hs.le,hsT⟩
    energy ((euclideanLaw (PrescribedSwitchCurve.law hN hb hbound hM hL₁ hL₂ hμ hT P s)).map (marginalProjection hk))
      (imageSource (euclideanLaw (PrescribedSwitchCurve.law hN hb hbound hM hL₁ hL₂ hμ hT P s))
        (prescribedBrownianSource hN hb hbound hM hL₁ hL₂ hμ hT P s) (marginalProjection hk)) ≤
      propagationConstant d M L₁ L₂ C₀ T*(1+1/s)*(k:ℝ)^2/(N:ℝ)^2 := by
  letI : IsProbabilityMeasure (PrescribedSwitchCurve.law hN hb hbound hM hL₁ hL₂ hμ hT P s) :=
    SwitchCurve.law_probability hN hb hbound hM hL₁ hL₂ _ _ _ hT P ⟨hs.le,hsT⟩
  rw [prescribed_marginal_energy_eq_prefix hN hb hbound hM hL₁ hL₂ hμ hT P hP ⟨hs.le,hsT⟩ hk]
  exact prefixEnergy_le hN hb hbound hM hL₁ hL₂ hμ hT P hP hex hC₀ hinit hs hsT hkpos hk

end SharpWasserstein.RegularizedBrownianSource
