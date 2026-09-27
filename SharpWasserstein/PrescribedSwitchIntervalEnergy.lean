import SharpWasserstein.PrescribedSwitchMarginalSourceContinuity
import SharpWasserstein.RegularizedBrownianSourceSwitch
import SharpWasserstein.RoughEulerianIntervalRestriction

/-! Actual compact-test action bounds on positive switch-time intervals.
The only quantitative input is the original Wasserstein hierarchy; the
energy, entropy regularization and propagation have all been proved. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal ENNReal
namespace SharpWasserstein.SwitchSourceDerivative
open WeightedTangent InitialSourceMarginal RegularizedBrownianSource
variable {d N k : ℕ}
  {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
  (hN : 0 < N) (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
  (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
  {μ : ℝ → Measure (Position d)} (hμ : IsLimitEvolution b μ)
  {T : ℝ} (hT : 0 ≤ T) (P : Measure (Configuration d N)) [IsProbabilityMeasure P]

theorem prescribedMarginalSource_finite (hk : k ≤ N) {s : ℝ} (hs : s ∈ Icc 0 T) :
    FiniteEnergy (prescribedMarginalCurve hN hb hbound hM hL₁ hL₂ hμ hT P hk s : Measure _)
      (prescribedMarginalSource hN hb hbound hM hL₁ hL₂ hμ hT P hk s) := by
  letI : IsProbabilityMeasure (PrescribedSwitchCurve.law hN hb hbound hM hL₁ hL₂ hμ hT P s) :=
    SwitchCurve.law_probability hN hb hbound hM hL₁ hL₂ _ _ _ hT P hs
  rw [prescribedMarginalCurve_coe hN hb hbound hM hL₁ hL₂ hμ hT P hk hs,
    prescribedMarginalSource_eq hN hb hbound hM hL₁ hL₂ hμ hT P hk hs]
  exact imageSource_finite _ _ _

variable (hP : HasSecondMoment P) (hex : Exchangeable P) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
  (hinit : ∀ j,∀ hj : j ≤ N,wassersteinSq (marginal hj P) (tensorLaw (μ 0) j) ≤
    ENNReal.ofReal (C₀*(j:ℝ)^2/(N:ℝ)^2)) (hkpos : 1 ≤ k) (hk : k ≤ N)

include hP hex hC₀ hinit hkpos

theorem prescribedMarginalCurve_energy_le {s : ℝ} (hs : 0 < s) (hsT : s ≤ T) :
    energy (prescribedMarginalCurve hN hb hbound hM hL₁ hL₂ hμ hT P hk s : Measure _)
      (prescribedMarginalSource hN hb hbound hM hL₁ hL₂ hμ hT P hk s) ≤
        propagationConstant d M L₁ L₂ C₀ T*(1+1/s)*(k:ℝ)^2/(N:ℝ)^2 := by
  letI : IsProbabilityMeasure (PrescribedSwitchCurve.law hN hb hbound hM hL₁ hL₂ hμ hT P s) :=
    SwitchCurve.law_probability hN hb hbound hM hL₁ hL₂ _ _ _ hT P ⟨hs.le,hsT⟩
  rw [prescribedMarginalCurve_coe hN hb hbound hM hL₁ hL₂ hμ hT P hk ⟨hs.le,hsT⟩,
    prescribedMarginalSource_eq hN hb hbound hM hL₁ hL₂ hμ hT P hk ⟨hs.le,hsT⟩]
  exact prescribed_marginal_energy_le hN hb hbound hM hL₁ hL₂ hμ hT P hP hex hC₀ hinit hs hsT hkpos hk

/-- A single finite bound controls every compact test on every positive
subinterval, in exactly the form required by rough finite-action transport. -/
theorem prescribedMarginalCurve_testObjective_le {a s : ℝ}
    (ha : 0 < a) (has : a ≤ s) (hsT : s ≤ T) (φ : Test (k*d)) :
    testObjective (prescribedMarginalCurve hN hb hbound hM hL₁ hL₂ hμ hT P hk s : Measure _)
      (prescribedMarginalSource hN hb hbound hM hL₁ hL₂ hμ hT P hk s) φ ≤
        propagationConstant d M L₁ L₂ C₀ T*(1+1/a)*(k:ℝ)^2/(N:ℝ)^2 := by
  have hs := ha.trans_le has
  have he := prescribedMarginalCurve_energy_le hN hb hbound hM hL₁ hL₂ hμ hT P hP hex hC₀ hinit hkpos hk hs hsT
  have hfin := prescribedMarginalSource_finite hN hb hbound hM hL₁ hL₂ hμ hT P hk ⟨hs.le,hsT⟩
  apply (le_csSup hfin (mem_range_self φ)).trans (he.trans ?_)
  have hC := propagationConstant_nonneg d hM hL₁ hC₀ hT (L₂ := L₂)
  have hi : 1/s ≤ 1/a := one_div_le_one_div_of_le ha has
  gcongr

end SharpWasserstein.SwitchSourceDerivative
