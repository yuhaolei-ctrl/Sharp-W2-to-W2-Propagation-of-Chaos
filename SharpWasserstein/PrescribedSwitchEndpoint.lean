import SharpWasserstein.WassersteinEndpointConstants
import SharpWasserstein.ParticleWeakIdentification

/-! Actual endpoint identification and final Wasserstein triangle assembly.
The remaining endpoint-length estimate is stated explicitly for the genuine
switch curve; it is not substituted by an assumed target transport bound. -/
noncomputable section
open Set MeasureTheory
open scoped NNReal ENNReal
namespace SharpWasserstein.WassersteinEndpoint
open RegularizedBrownianSource
variable {d N : ℕ} {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
  (hN : 0 < N) (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
  (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
  {μ : ℝ → Measure (Position d)} (hμ : IsLimitEvolution b μ)
  {P : ℝ → Measure (Configuration d N)} (hP : IsParticleEvolution b P)
include hP

/-- The zero-switch endpoint is the supplied arbitrary weak particle law. -/
theorem switch_zero_eq_supplied {t : ℝ} (ht : 0 ≤ t) :
    PrescribedSwitchCurve.law hN hb hbound hM hL₁ hL₂ hμ ht (P 0) 0 = P t := by
  letI := hP.1.probability 0 le_rfl
  rw [PrescribedSwitchCurve.law_zero]
  exact (BrownianParticle.eq_globalLaw_of_weakEvolution hN hb hbound hM hL₁ hL₂ hP.1 ht).symm

/-- Actual transport to the tensor reference, with one horizon-uniform
constant, once the genuine switch endpoint length has been established. -/
theorem bound_of_switch_length (hd : 1 ≤ d) {C₀ T : ℝ} (hC₀ : 0 ≤ C₀) (hT : 0 ≤ T)
    {k : ℕ} (hk : k ≤ N)
    (hinit : wassersteinSq (marginal hk (P 0)) (tensorLaw (μ 0) k) ≤
      ENNReal.ofReal (C₀*(k:ℝ)^2/(N:ℝ)^2))
    {t : ℝ} (ht : t ∈ Icc 0 T)
    (hswitch : Real.sqrt (wassersteinSq
      (marginal hk (PrescribedSwitchCurve.law hN hb hbound hM hL₁ hL₂ hμ ht.1 (P 0) 0))
      (marginal hk (PrescribedSwitchCurve.law hN hb hbound hM hL₁ hL₂ hμ ht.1 (P 0) t))).toReal ≤
      Real.sqrt (propagationConstant d M L₁ L₂ C₀ T)*(T+3*Real.sqrt T)*((k:ℝ)/N)) :
    wassersteinSq (marginal hk (P t)) (tensorLaw (μ t) k) ≤
      ENNReal.ofReal (coefficient d M L₁ L₂ C₀ T*(k:ℝ)^2/(N:ℝ)^2) := by
  letI := hP.1.probability 0 le_rfl
  letI := hP.1.probability t ht.1
  letI := hμ.1 t ht.1
  let R := PrescribedReference.law hb hbound hM hL₁ hμ N (P 0) t
  have hR := PrescribedReference.law_weakEvolution hb hbound hM hL₁ hμ N (P 0) (hP.1.secondMoment 0 le_rfl)
  letI : IsProbabilityMeasure R := hR.probability t ht.1
  have hleft : Real.sqrt (wassersteinSq (marginal hk (P t)) (marginal hk R)).toReal ≤
      Real.sqrt (propagationConstant d M L₁ L₂ C₀ T)*(T+3*Real.sqrt T)*((k:ℝ)/N) := by
    rw [switch_zero_eq_supplied hN hb hbound hM hL₁ hL₂ hμ hP ht.1,
      PrescribedSwitchCurve.law_terminal] at hswitch
    exact hswitch
  have hright := PrescribedDecoupledTransport.marginal_profile_uniform hb hbound hM hL₁ hμ (P 0)
    hd hC₀ hT hk hinit ht
  have hh := transport_triangle_bound (marginal hk (P t)) (marginal hk R) (tensorLaw (μ t) k)
    (hasSecondMoment_marginal hk (hP.1.secondMoment t ht.1))
    (hasSecondMoment_marginal hk (hR.secondMoment t ht.1))
    ((PrescribedReference.supplied_tensor_weakEvolution hb hbound hM hL₁ hμ k).secondMoment t ht.1)
    (S := Real.sqrt (propagationConstant d M L₁ L₂ C₀ T)*(T+3*Real.sqrt T))
    (D := PrescribedDecoupledTransport.coefficient d L₁ C₀ T) (r := (k:ℝ)/N)
    (by positivity) (PrescribedDecoupledTransport.coefficient_nonneg d hC₀)
    (by positivity) hleft (by simpa only [div_pow,mul_div_assoc] using hright)
  apply hh.trans
  apply ENNReal.ofReal_le_ofReal
  have hp := propagationConstant_nonneg d (L₂ := L₂) hM hL₁ hC₀ hT
  rw [mul_pow,Real.sq_sqrt hp]
  unfold coefficient
  apply le_of_eq
  ring

/-- A length estimate at each observation time gives the same fixed-horizon
endpoint bound, using proved monotonicity of the explicit source constant. -/
theorem bound_of_local_switch_length (hd : 1 ≤ d) {C₀ T : ℝ} (hC₀ : 0 ≤ C₀) (hT : 0 ≤ T)
    {k : ℕ} (hk : k ≤ N)
    (hinit : wassersteinSq (marginal hk (P 0)) (tensorLaw (μ 0) k) ≤
      ENNReal.ofReal (C₀*(k:ℝ)^2/(N:ℝ)^2))
    {t : ℝ} (ht : t ∈ Icc 0 T)
    (hswitch : Real.sqrt (wassersteinSq
      (marginal hk (PrescribedSwitchCurve.law hN hb hbound hM hL₁ hL₂ hμ ht.1 (P 0) 0))
      (marginal hk (PrescribedSwitchCurve.law hN hb hbound hM hL₁ hL₂ hμ ht.1 (P 0) t))).toReal ≤
      Real.sqrt (propagationConstant d M L₁ L₂ C₀ t)*(t+3*Real.sqrt t)*((k:ℝ)/N)) :
    wassersteinSq (marginal hk (P t)) (tensorLaw (μ t) k) ≤
      ENNReal.ofReal (coefficient d M L₁ L₂ C₀ T*(k:ℝ)^2/(N:ℝ)^2) := by
  apply bound_of_switch_length hN hb hbound hM hL₁ hL₂ hμ hP hd hC₀ hT hk hinit ht
  exact hswitch.trans (mul_le_mul_of_nonneg_right
    (switchLengthCoefficient_mono hM hL₁ hC₀ ht.1 ht.2) (by positivity))

end SharpWasserstein.WassersteinEndpoint

namespace SharpWasserstein.WassersteinEndpoint
/-- The exact original family-level target follows from actual switch-length
estimates. All reference/particle endpoint identifications and initial-level
quantifiers are discharged by the previous theorems. -/
theorem propagatedHierarchy_of_switch_lengths {d : ℕ} (hd : 1 ≤ d)
    {C₀ T M L₁ L₂ : ℝ} (hC₀ : 0 ≤ C₀) (hT : 0 ≤ T)
    (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    {b : Position d → Position d → Position d} (hb : BoundedSmoothKernel b)
    (hbound : KernelBounds b M L₁ L₂)
    {μ : ℝ → Measure (Position d)} (hμ : IsLimitEvolution b μ)
    {P : (N : ℕ) → ℝ → Measure (Configuration d N)}
    (hP : ∀ N,1 ≤ N → IsParticleEvolution b (P N))
    (hinit : InitialHierarchy C₀ (μ 0) (fun N => P N 0))
    (hswitch : ∀ N,∀ hN : 1 ≤ N,∀ k,1 ≤ k → ∀ hk : k ≤ N,∀ t,∀ ht : t ∈ Icc 0 T,
      Real.sqrt (wassersteinSq
        (marginal hk (PrescribedSwitchCurve.law hN hb hbound hM hL₁ hL₂ hμ ht.1 (P N 0) 0))
        (marginal hk (PrescribedSwitchCurve.law hN hb hbound hM hL₁ hL₂ hμ ht.1 (P N 0) t))).toReal ≤
      Real.sqrt (RegularizedBrownianSource.propagationConstant d M L₁ L₂ C₀ t)*
        (t+3*Real.sqrt t)*((k:ℝ)/N)) :
    PropagatedHierarchy (coefficient d M L₁ L₂ C₀ T) T μ P := by
  intro N hN k hkpos hk t ht
  exact bound_of_local_switch_length hN hb hbound hM hL₁ hL₂ hμ (hP N hN)
    hd hC₀ hT hk (hinit N hN k hkpos hk) ht (hswitch N hN k hkpos hk t ht)

end SharpWasserstein.WassersteinEndpoint
