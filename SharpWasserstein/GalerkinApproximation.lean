module

public import SharpWasserstein.Compat
public import SharpWasserstein.WeightedEnergyDerivative
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

@[expose] public section

/-! Coercive Galerkin solutions are constructed by genuine projected operators.
The exact residual equation and best-approximation estimate are proved rather
than assumed. Specialization to actual smooth test gradients is separate. -/

noncomputable section
namespace SharpWasserstein.GalerkinApproximation
open scoped InnerProductSpace Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (S : Submodule ℝ H) [CompleteSpace S]

/-- Restrict a genuine operator by orthogonal projection onto the trial space. -/
def restrictedOperator (A : H →L[ℝ] H) : S →L[ℝ] S :=
  S.orthogonalProjectionOnto.comp (A.comp S.subtypeL)

theorem restrictedOperator_inner (A : H →L[ℝ] H) (v w : S) :
    ⟪restrictedOperator S A v, w⟫_ℝ = ⟪A (v : H), (w : H)⟫_ℝ := by
  change ⟪S.orthogonalProjectionOnto (A (v : H)), w⟫_ℝ = _
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]

/-- Coercivity is inherited by every closed trial space, with the same lower bound. -/
theorem restrictedOperator_isUnit (A : H →L[ℝ] H) {a : ℝ} (ha : 0 < a)
    (hA : ∀ v : H, a * ‖v‖ ^ 2 ≤ ⟪A v, v⟫_ℝ) :
    IsUnit (restrictedOperator S A) := by
  have hc : IsCoercive ((innerSL ℝ).comp (restrictedOperator S A)) := by
    refine ⟨a, ha, fun v => ?_⟩
    change a * ‖v‖ * ‖v‖ ≤ ⟪restrictedOperator S A v, v⟫_ℝ
    rw [restrictedOperator_inner]
    change a * ‖(v : H)‖ * ‖(v : H)‖ ≤ _
    simpa only [pow_two, mul_assoc] using hA (v : H)
  refine ⟨hc.continuousLinearEquivOfBilin.toUnit, ?_⟩
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_right ℝ
  intro w
  exact hc.continuousLinearEquivOfBilin_apply v w

/-- The Galerkin optimizer is the actual inverse of the finite/closed-space operator. -/
def solution (A : H →L[ℝ] H) (f : H) : S :=
  Ring.inverse (restrictedOperator S A) (S.orthogonalProjectionOnto f)

/-- The constructed optimizer satisfies the tested equation exactly on its trial space. -/
theorem solution_equation (A : H →L[ℝ] H) (f : H) {a : ℝ} (ha : 0 < a)
    (hA : ∀ v : H, a * ‖v‖ ^ 2 ≤ ⟪A v, v⟫_ℝ) (w : S) :
    ⟪A (solution S A f : H), (w : H)⟫_ℝ = ⟪f, (w : H)⟫_ℝ := by
  obtain ⟨u, hu⟩ := restrictedOperator_isUnit S A ha hA
  have he : restrictedOperator S A (solution S A f) = S.orthogonalProjectionOnto f := by
    simp [solution, ← hu, ← mul_apply_eq_comp]
  rw [← restrictedOperator_inner, he]
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]

/-- The error is genuinely orthogonal in the weighted bilinear form. -/
theorem error_orthogonal (A : H →L[ℝ] H) (f u : H) {a : ℝ} (ha : 0 < a)
    (hA : ∀ v : H, a * ‖v‖ ^ 2 ≤ ⟪A v, v⟫_ℝ) (hu : A u = f) (w : S) :
    ⟪A (u - (solution S A f : H)), (w : H)⟫_ℝ = 0 := by
  rw [map_sub, inner_sub_left, hu, solution_equation S A f ha hA, sub_self]

/-- Céa's bound follows from the actual variational equations and operator norm. -/
theorem solution_error_le (A : H →L[ℝ] H) (f u : H) {a : ℝ} (ha : 0 < a)
    (hA : ∀ v : H, a * ‖v‖ ^ 2 ≤ ⟪A v, v⟫_ℝ) (hu : A u = f) (w : S) :
    ‖u - (solution S A f : H)‖ ≤ (‖A‖ / a) * ‖u - (w : H)‖ := by
  let e := u - (solution S A f : H)
  have ho := error_orthogonal S A f u ha hA hu (w - solution S A f)
  have he : ⟪A e, e⟫_ℝ = ⟪A e, u - (w : H)⟫_ℝ := by
    change ⟪A e, (w : H) - (solution S A f : H)⟫_ℝ = 0 at ho
    simp only [inner_sub_right] at ho ⊢
    change ⟪A e, u - (solution S A f : H)⟫_ℝ = _
    rw [inner_sub_right]
    linarith
  have hb : a * ‖e‖ ^ 2 ≤ ‖A‖ * ‖e‖ * ‖u - (w : H)‖ := by
    calc
      _ ≤ ⟪A e, e⟫_ℝ := hA e
      _ = _ := he
      _ ≤ ‖A e‖ * ‖u - (w : H)‖ := real_inner_le_norm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (A.le_opNorm e) (norm_nonneg _)
  by_cases hz : ‖e‖ = 0
  · change ‖e‖ ≤ _
    rw [hz]
    positivity
  · have hepos : 0 < ‖e‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have hn : a * ‖e‖ ≤ ‖A‖ * ‖u - (w : H)‖ := by nlinarith
    change ‖e‖ ≤ _
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ ha).mpr
    nlinarith

/-- Exact energy error; no limiting optimizer regularity is needed for this identity. -/
theorem energy_error_eq (A : H →L[ℝ] H) (f u : H) {a : ℝ} (ha : 0 < a)
    (hA : ∀ v : H, a * ‖v‖ ^ 2 ≤ ⟪A v, v⟫_ℝ) (hu : A u = f)
    (hsymm : ∀ v w : H, ⟪A v, w⟫_ℝ = ⟪v, A w⟫_ℝ) :
    ⟪f, u⟫_ℝ - ⟪f, (solution S A f : H)⟫_ℝ =
      ⟪A (u - (solution S A f : H)), u - (solution S A f : H)⟫_ℝ := by
  have he := error_orthogonal S A f u ha hA hu (solution S A f)
  simp only [map_sub, inner_sub_left, inner_sub_right, hu] at he ⊢
  have hs := hsymm (solution S A f : H) u
  rw [hu, real_inner_comm f] at hs
  linarith

/-- Operator restriction is itself a genuine continuous linear map. -/
def restrictionMap : (H →L[ℝ] H) →L[ℝ] (S →L[ℝ] S) :=
  let R : (H →L[ℝ] H) →L[ℝ] (S →L[ℝ] H) :=
    (ContinuousLinearMap.flipₗᵢ ℝ (H →L[ℝ] H) (S →L[ℝ] H) (S →L[ℝ] H)
      (ContinuousLinearMap.compL ℝ S H H)) S.subtypeL
  (ContinuousLinearMap.compL ℝ S H S S.orthogonalProjectionOnto).comp R

@[simp] theorem restrictionMap_apply (A : H →L[ℝ] H) :
    restrictionMap S A = restrictedOperator S A := rfl

/-- Finite/closed-space energy is differentiable because the projected operator
is coercive and invertible; differentiability of its optimizer is not assumed. -/
theorem hasDerivAt_energy {A : ℝ → H →L[ℝ] H} {A' : H →L[ℝ] H}
    {f : ℝ → H} {f' : H} {t a : ℝ}
    (hA : HasDerivAt A A' t) (hf : HasDerivAt f f' t) (ha : 0 < a)
    (hpos : ∀ v : H, a * ‖v‖ ^ 2 ≤ ⟪A t v, v⟫_ℝ)
    (hsymm : ∀ v w : H, ⟪A t v, w⟫_ℝ = ⟪v, A t w⟫_ℝ) :
    HasDerivAt (fun r => ⟪f r, (solution S (A r) (f r) : H)⟫_ℝ)
      (2 * ⟪f', (solution S (A t) (f t) : H)⟫_ℝ -
        ⟪A' (solution S (A t) (f t) : H), (solution S (A t) (f t) : H)⟫_ℝ) t := by
  have hAr : HasDerivAt (fun r => restrictedOperator S (A r)) (restrictedOperator S A') t :=
    HasFDerivAt.comp_hasDerivAt (F := H →L[ℝ] H) (E := S →L[ℝ] S) t
      (restrictionMap S).hasFDerivAt hA
  have hfr := S.orthogonalProjectionOnto.hasFDerivAt.comp_hasDerivAt t hf
  obtain ⟨u, hu⟩ := restrictedOperator_isUnit S (A t) ha hpos
  have hs : ∀ v w : S, ⟪restrictedOperator S (A t) v, w⟫_ℝ =
      ⟪v, restrictedOperator S (A t) w⟫_ℝ := by
    intro v w
    rw [restrictedOperator_inner, real_inner_comm (restrictedOperator S (A t) w) v, restrictedOperator_inner]
    exact (hsymm (v : H) (w : H)).trans (real_inner_comm _ _)
  have h := WeightedEnergyDerivative.hasDerivAt_optimizedEnergy hAr hfr u hu.symm hs
  simpa only [WeightedEnergyDerivative.inverseSolution, solution, Function.comp_apply,
    restrictedOperator_inner, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right] using h

end SharpWasserstein.GalerkinApproximation
