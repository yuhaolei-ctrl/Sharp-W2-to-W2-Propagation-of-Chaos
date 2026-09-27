import SharpWasserstein.PrescribedSwitchLengthFromAction
import SharpWasserstein.PrescribedSwitchEndpoint

/-! Reduction of the exact original manuscript proposition to a single
explicit general rough finite-action theorem. This conditional theorem does
not assert MainTheorem: an inhabitant of UniformFiniteActionTransport remains
necessary, and is being constructed separately without new axioms. -/
noncomputable section
open Set MeasureTheory
namespace SharpWasserstein

/-- All manuscript-specific analytic estimates and quantifier adapters have
been discharged; the sole remaining premise is the explicitly defined rough
continuity-equation transport principle. -/
theorem main_of_uniform_finite_action_transport
    (htransport : RoughEulerianTransport.UniformFiniteActionTransport) : MainTheorem := by
  intro d hd C₀ T M L₁ L₂ hC₀ hT hM hL₁ hL₂
  refine ⟨WassersteinEndpoint.coefficient d M L₁ L₂ C₀ T,
    WassersteinEndpoint.coefficient_nonneg d hM hL₁ hC₀ hT.le,?_⟩
  intro b μ P hb hbound hμ hP hinit
  apply WassersteinEndpoint.propagatedHierarchy_of_switch_lengths hd hC₀ hT.le hM hL₁ hL₂ hb hbound hμ hP hinit
  intro N hN k hkpos hk t ht
  letI := (hP N hN).1.probability 0 le_rfl
  letI := hμ.1 0 le_rfl
  exact SwitchSourceDerivative.prescribed_switch_length_of_finiteAction htransport hN hb hbound hM hL₁ hL₂ hμ ht.1
    (P N 0) ((hP N hN).1.secondMoment 0 le_rfl) (hP N hN).2 hC₀
    (WassersteinEndpoint.initialHierarchy_allLevels (μ 0) (fun N => P N 0) hN hinit) hkpos hk

end SharpWasserstein
