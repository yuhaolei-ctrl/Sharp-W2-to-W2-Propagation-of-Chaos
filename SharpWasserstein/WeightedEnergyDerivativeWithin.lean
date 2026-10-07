module

public import SharpWasserstein.Compat
public import SharpWasserstein.WeightedEnergyDerivative

@[expose] public section

/-! Endpoint differentiation of the actual coercive inverse energy on a
closed time interval. No extension of the evolution past its endpoints is
assumed. -/
noncomputable section
namespace SharpWasserstein.WeightedEnergyDerivative
open scoped InnerProductSpace Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem hasDerivWithinAt_inverseSolution {A : ℝ → H →L[ℝ] H} {A' : H →L[ℝ] H}
    {f : ℝ → H} {f' : H} {s : Set ℝ} {t : ℝ}
    (hA : HasDerivWithinAt A A' s t) (hf : HasDerivWithinAt f f' s t)
    (a : (H →L[ℝ] H)ˣ) (ha : A t = a) :
    HasDerivWithinAt (inverseSolution A f)
      ((↑a⁻¹ : H →L[ℝ] H) (f' - A' (inverseSolution A f t))) s t := by
  have hi : HasFDerivAt (@Ring.inverse (H →L[ℝ] H) _)
      (-ContinuousLinearMap.mulLeftRight ℝ (H →L[ℝ] H) (↑a⁻¹) (↑a⁻¹)) (A t) := by
    rw [ha]
    exact hasFDerivAt_ringInverse a
  have hd := (hi.comp_hasDerivWithinAt t hA).clm_apply hf
  convert hd using 1
  · rfl
  · simp [inverseSolution,ha,sub_eq_add_neg,add_comm,ContinuousLinearMap.mulLeftRight_apply]

theorem hasDerivWithinAt_optimizedEnergy {A : ℝ → H →L[ℝ] H} {A' : H →L[ℝ] H}
    {f : ℝ → H} {f' : H} {s : Set ℝ} {t : ℝ}
    (hA : HasDerivWithinAt A A' s t) (hf : HasDerivWithinAt f f' s t)
    (a : (H →L[ℝ] H)ˣ) (ha : A t = a)
    (hsymm : ∀ v w : H,⟪A t v,w⟫_ℝ = ⟪v,A t w⟫_ℝ) :
    HasDerivWithinAt (fun r => ⟪f r,inverseSolution A f r⟫_ℝ)
      (2*⟪f',inverseSolution A f t⟫_ℝ-
        ⟪A' (inverseSolution A f t),inverseSolution A f t⟫_ℝ) s t := by
  have hu := hasDerivWithinAt_inverseSolution hA hf a ha
  have he := hf.inner ℝ hu
  convert! he using 1
  let u := inverseSolution A f t
  let u' := (↑a⁻¹ : H →L[ℝ] H) (f'-A' u)
  have hAu : A t u = f t := inverseSolution_equation a ha
  have hAu' : A t u' = f'-A' u := inverseSolution_derivative_equation a ha
  have hp : ⟪f t,u'⟫_ℝ = ⟪f',u⟫_ℝ-⟪A' u,u⟫_ℝ := by
    rw [← hAu,hsymm,hAu',inner_sub_right,real_inner_comm u f',real_inner_comm u (A' u)]
  change 2*⟪f',u⟫_ℝ-⟪A' u,u⟫_ℝ = ⟪f t,u'⟫_ℝ+⟪f',u⟫_ℝ
  rw [hp]
  ring

end SharpWasserstein.WeightedEnergyDerivative
