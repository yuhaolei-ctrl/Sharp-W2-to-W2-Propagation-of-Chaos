module

public import SharpWasserstein.Compat
public import SharpWasserstein.PrescribedEntropyProfile
public import SharpWasserstein.SwitchCurveProperties

@[expose] public section

/-! The terminal decoupled part of the proof uses the actual unnormalized
Wasserstein cost, exact marginal commutation and the supplied reference law.
Its horizon coefficient is independent of both particle counts. -/
noncomputable section
open Set MeasureTheory
open scoped NNReal ENNReal
namespace SharpWasserstein.PrescribedDecoupledTransport

/-- Uniform coefficient for the actual synchronous reference-flow estimate. -/
def coefficient (d : ℕ) (L₁ C₀ T : ℝ) : ℝ :=
  (d:ℝ)*Real.exp (L₁*T)^2*C₀

theorem coefficient_nonneg (d : ℕ) {L₁ C₀ T : ℝ} (hC₀ : 0 ≤ C₀) :
    0 ≤ coefficient d L₁ C₀ T := by unfold coefficient; positivity

theorem initial_le_coefficient {d : ℕ} (hd : 1 ≤ d) {L₁ C₀ T : ℝ}
    (hL₁ : 0 ≤ L₁) (hC₀ : 0 ≤ C₀) (hT : 0 ≤ T) : C₀ ≤ coefficient d L₁ C₀ T := by
  have he : 1 ≤ Real.exp (L₁*T) := Real.one_le_exp (mul_nonneg hL₁ hT)
  have hd' : (1:ℝ) ≤ d := by exact_mod_cast hd
  unfold coefficient
  nlinarith [sq_nonneg (Real.exp (L₁*T)-1),mul_nonneg (sub_nonneg.mpr hd') (sq_nonneg (Real.exp (L₁*T))),
    mul_le_mul_of_nonneg_right (show (1:ℝ) ≤ (d:ℝ)*Real.exp (L₁*T)^2 by nlinarith) hC₀]

variable {d N : ℕ} {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
  (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
  (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁)
  {μ : ℝ → Measure (Position d)} (hμ : IsLimitEvolution b μ)
  (P : Measure (Configuration d N)) [IsProbabilityMeasure P]

/-- Positive-time synchronous stability relative to the supplied reference. -/
theorem marginal_wassersteinSq_le {k : ℕ} (hk : k ≤ N) {t : ℝ} (ht : 0 < t) :
    wassersteinSq (marginal hk (PrescribedReference.law hb hbound hM hL₁ hμ N P t))
      (tensorLaw (μ t) k) ≤
    ENNReal.ofReal ((d:ℝ)*Real.exp (L₁*t)^2)*wassersteinSq (marginal hk P) (tensorLaw (μ 0) k) := by
  letI := hμ.1 0 le_rfl
  have hh := DecoupledFlow.law_wassersteinSq_le
    (PrescribedReference.singleDrift_continuous hb hbound hL₁ hμ)
    (PrescribedReference.singleDrift_bound hbound hM hμ)
    (PrescribedReference.singleDrift_lipschitz hb hbound hL₁ hμ)
    ht.le (marginal hk P) (tensorLaw (μ 0) k) (BrownianNoise.positionLaw d t)
    (show t ∈ Icc 0 t from ⟨ht.le,le_rfl⟩)
  change wassersteinSq (DecoupledFlow.brownianLaw _ _ _ ht.le (marginal hk P))
    (DecoupledFlow.brownianLaw _ _ _ ht.le (tensorLaw (μ 0) k)) ≤ _ at hh
  rw [DecoupledFlow.brownianLaw_tensor,
    PrescribedReference.singleBrownianLaw_eq_supplied hb hbound hM hL₁ hμ ht] at hh
  rw [PrescribedReference.law_eq_decoupled hb hbound hM hL₁ hμ N P ht]
  change wassersteinSq (marginal hk (DecoupledFlow.brownianLaw _ _ _ ht.le P)) _ ≤ _
  rw [DecoupledFlow.brownianLaw_marginal]
  exact hh

/-- The actual decoupled marginal bound is uniform on the closed horizon,
including the original initial law at time zero. -/
theorem marginal_profile_uniform (hd : 1 ≤ d) {C₀ T : ℝ} (hC₀ : 0 ≤ C₀) (hT : 0 ≤ T)
    {k : ℕ} (hk : k ≤ N)
    (hinit : wassersteinSq (marginal hk P) (tensorLaw (μ 0) k) ≤
      ENNReal.ofReal (C₀*(k:ℝ)^2/(N:ℝ)^2))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    wassersteinSq (marginal hk (PrescribedReference.law hb hbound hM hL₁ hμ N P t))
      (tensorLaw (μ t) k) ≤
      ENNReal.ofReal (coefficient d L₁ C₀ T*(k:ℝ)^2/(N:ℝ)^2) := by
  by_cases ht0 : t=0
  · subst t
    rw [PrescribedReference.law_initial]
    apply hinit.trans (ENNReal.ofReal_le_ofReal ?_)
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (initial_le_coefficient hd hL₁ hC₀ hT) (sq_nonneg _)) (sq_nonneg _)
  have htp : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have hh := marginal_wassersteinSq_le hb hbound hM hL₁ hμ P hk htp
  apply hh.trans
  calc
    _ ≤ ENNReal.ofReal ((d:ℝ)*Real.exp (L₁*t)^2)*
        ENNReal.ofReal (C₀*(k:ℝ)^2/(N:ℝ)^2) := mul_le_mul_right hinit _
    _ = ENNReal.ofReal (((d:ℝ)*Real.exp (L₁*t)^2)*(C₀*(k:ℝ)^2/(N:ℝ)^2)) :=
      (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hL₁)
      unfold coefficient
      calc
        _ ≤ ((d:ℝ)*Real.exp (L₁*T)^2)*(C₀*(k:ℝ)^2/(N:ℝ)^2) := by gcongr
        _ = _ := by ring

end SharpWasserstein.PrescribedDecoupledTransport
