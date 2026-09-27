import SharpWasserstein.RegularizedBrownianSourceData
import SharpWasserstein.BrownianEnergyPeriodization

/-! Sharp full Euclidean source bound for the actual regularized current,
propagated by the original interaction for the remaining switch time. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace NNReal ENNReal
namespace SharpWasserstein.RegularizedBrownianSource
open WeightedTangent InitialSourcePermutation BrownianPeriodicHierarchy

/-- The horizon coefficient depends only on d, the stated kernel bounds,
the original Wasserstein profile constant, and the time horizon. -/
def propagationConstant (d : ℕ) (M L₁ L₂ C₀ T : ℝ) : ℝ :=
  RegularizationRates.sourceHorizonConstant d M C₀ (Real.sqrt (d:ℝ)*L₁) T*
    Real.exp (4*comparisonConstant d M L₁ L₂*T)

theorem sourceHorizonConstant_nonneg (d : ℕ) {M L₁ C₀ T : ℝ}
    (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hC₀ : 0 ≤ C₀) (hT : 0 ≤ T) :
    0 ≤ RegularizationRates.sourceHorizonConstant d M C₀ (Real.sqrt (d:ℝ)*L₁) T := by
  have hi := internalSourceConstant_nonneg hM
  unfold RegularizationRates.sourceHorizonConstant RegularizationRates.bridgeHorizonFactor
  positivity

theorem propagationConstant_nonneg (d : ℕ) {M L₁ L₂ C₀ T : ℝ}
    (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hC₀ : 0 ≤ C₀) (hT : 0 ≤ T) :
    0 ≤ propagationConstant d M L₁ L₂ C₀ T :=
  mul_nonneg (sourceHorizonConstant_nonneg d hM hL₁ hC₀ hT) (Real.exp_pos _).le

variable {d N : ℕ} {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
  (hN : 0 < N) (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
  (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
  {μ : ℝ → Measure (Position d)} (hμ : IsLimitEvolution b μ)
  {T : ℝ} (hT : 0 ≤ T) (P : Measure (Configuration d N)) [IsProbabilityMeasure P]
  (hP : HasSecondMoment P) (hex : Exchangeable P)

include hex in
/-- The source bound at every positive switch time follows from the original
all-level transport profile. No entropy, source-energy or evolution premise
is imposed at that positive time. -/
theorem prefixEnergy_le {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hinit : ∀ j,∀ hj : j ≤ N,wassersteinSq (marginal hj P) (tensorLaw (μ 0) j) ≤
      ENNReal.ofReal (C₀*(j:ℝ)^2/(N:ℝ)^2))
    {s : ℝ} (hs : 0 < s) (hsT : s ≤ T) {k : ℕ} (hkpos : 1 ≤ k) (hk : k ≤ N) :
    let R := PrescribedReference.law hb hbound hM hL₁ hμ N P s
    letI : IsProbabilityMeasure R := law_probability hb hbound hM hL₁ hμ P hP hs.le
    let u : Point (N*d) → Point (N*d) := euclideanFlux (initialCurrent b (μ s))
    let hu := current_memLp hb hbound hM hL₁ hμ P hP hN hs.le
    BrownianEnergyPeriodization.prefixEnergy hN hb hbound hM hL₁ hL₂ hT (euclideanLaw R) hk u hu (T-s) ≤
      propagationConstant d M L₁ L₂ C₀ T*(1+1/s)*(k:ℝ)^2/(N:ℝ)^2 := by
  let R := PrescribedReference.law hb hbound hM hL₁ hμ N P s
  letI := law_probability hb hbound hM hL₁ hμ P hP hs.le
  let u : Point (N*d) → Point (N*d) := euclideanFlux (initialCurrent b (μ s))
  let hu := current_memLp hb hbound hM hL₁ hμ P hP hN hs.le
  obtain ⟨σ₀,hσ₀,hσfinite,hprofile⟩ := exists_initial_profile hb hbound hM hL₁ hμ P hP hN hex hC₀ hs hsT hinit
  have hA := mul_nonneg (sourceHorizonConstant_nonneg d hM hL₁ hC₀ hT)
    (show 0 ≤ 1+1/s by positivity)
  have hh := BrownianEnergyPeriodization.prefixEnergy_quadratic_bound hN hb hbound hM hL₁ hL₂ hT R
    (law_secondMoment hb hbound hM hL₁ hμ P hP hs.le) hu
    (law_exchangeable hb hbound hM hL₁ hμ P hex hs)
    (current_covariant hb hbound hM hL₁ hμ P s) hA σ₀ hσ₀ hprofile hkpos hk
    (show T-s ∈ Icc 0 T from ⟨sub_nonneg.mpr hsT,sub_le_self _ hs.le⟩)
  apply hh.trans
  have he : Real.exp (4*comparisonConstant d M L₁ L₂*(T-s)) ≤
      Real.exp (4*comparisonConstant d M L₁ L₂*T) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (sub_le_self _ hs.le)
      (mul_nonneg (by norm_num) (comparisonConstant_nonneg d M L₁ L₂))
  calc
    _ ≤ (RegularizationRates.sourceHorizonConstant d M C₀ (Real.sqrt (d:ℝ)*L₁) T*(1+1/s))*
        Real.exp (4*comparisonConstant d M L₁ L₂*T)*(k:ℝ)^2/(N:ℝ)^2 := by
      gcongr
    _ = _ := by unfold propagationConstant; ring

end SharpWasserstein.RegularizedBrownianSource
