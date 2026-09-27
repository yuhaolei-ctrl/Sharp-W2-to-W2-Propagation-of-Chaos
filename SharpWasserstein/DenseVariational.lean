import SharpWasserstein.TangentEnergy
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Tactic.FunProp

/-! Dense-range variational representation, used by the actual compact-test
weighted gradient construction in `WeightedTangent`. The test vector space
need not already carry a norm. Boundedness and annihilation of the gradient
kernel are derived from the quadratic variational hypothesis. -/

noncomputable section
namespace SharpWasserstein.DenseVariational
open scoped InnerProductSpace

variable {V H : Type*} [AddCommGroup V] [Module ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The quadratic test objective, before quotienting by the gradient kernel. -/
def objective (σ : V →ₗ[ℝ] ℝ) (e : V →ₗ[ℝ] H) (φ : V) : ℝ :=
  2 * σ φ - ‖e φ‖ ^ 2

/-- A finite quadratic supremum supplies the norm bound needed for completion. -/
theorem bound_of_bounded_objective (σ : V →ₗ[ℝ] ℝ) (e : V →ₗ[ℝ] H)
    (hfin : BddAbove (Set.range (objective σ e))) :
    ∃ C : ℝ, ∀ φ, ‖σ φ‖ ≤ C * ‖e φ‖ := by
  obtain ⟨A, hA⟩ := hfin
  have hobj (φ : V) : 2 * σ φ - ‖e φ‖ ^ 2 ≤ A := hA ⟨φ, rfl⟩
  have hA0 : 0 ≤ A := by simpa using hobj 0
  refine ⟨(A + 1) / 2, ?_⟩
  intro φ
  by_cases hzero : e φ = 0
  · have hs : σ φ = 0 := by
      by_contra hσ
      have hscale : σ (((A + 1) / σ φ) • φ) = A + 1 := by
        rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hσ]
      have hh := hobj (((A + 1) / σ φ) • φ)
      rw [hscale, map_smul, hzero, smul_zero, norm_zero, zero_pow (by decide),
        sub_zero] at hh
      linarith
    simp [hs, hzero]
  · have hn : 0 < ‖e φ‖ := norm_pos_iff.mpr hzero
    let ψ : V := ‖e φ‖⁻¹ • φ
    have hψnorm : ‖e ψ‖ = 1 := by
      simp only [ψ, map_smul, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
    have hp := hobj ψ
    have hm := hobj (-ψ)
    simp only [map_neg, norm_neg] at hm
    have ha : |σ ψ| ≤ (A + 1) / 2 := by
      apply abs_le.mpr
      constructor <;> nlinarith [hp, hm]
    calc
      ‖σ φ‖ = ‖e φ‖ * |σ ψ| := by
        simp only [ψ, map_smul, smul_eq_mul, abs_mul,
          abs_of_pos (inv_pos.mpr hn), Real.norm_eq_abs]
        rw [← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul]
      _ ≤ ‖e φ‖ * ((A + 1) / 2) := mul_le_mul_of_nonneg_left ha hn.le
      _ = ((A + 1) / 2) * ‖e φ‖ := mul_comm _ _

/-- The bounded functional extended from the dense test gradients. -/
def extension (σ : V →ₗ[ℝ] ℝ) (e : V →ₗ[ℝ] H) : H →L[ℝ] ℝ :=
  σ.extendOfNorm e

theorem extension_apply (σ : V →ₗ[ℝ] ℝ) (e : V →ₗ[ℝ] H)
    (hdense : DenseRange e) (hfin : BddAbove (Set.range (objective σ e))) (φ : V) :
    extension σ e (e φ) = σ φ :=
  LinearMap.extendOfNorm_eq hdense (bound_of_bounded_objective σ e hfin) φ

variable [CompleteSpace H]

/-- Riesz vector in the completed tangent space. -/
def representative (σ : V →ₗ[ℝ] ℝ) (e : V →ₗ[ℝ] H) : H :=
  TangentEnergy.rieszRepresentative (extension σ e)

theorem representative_pairing (σ : V →ₗ[ℝ] ℝ) (e : V →ₗ[ℝ] H)
    (hdense : DenseRange e) (hfin : BddAbove (Set.range (objective σ e))) (φ : V) :
    ⟪representative σ e, e φ⟫_ℝ = σ φ := by
  rw [representative, TangentEnergy.inner_rieszRepresentative,
    extension_apply σ e hdense hfin]

/-- Pairings on the dense test space uniquely determine the Riesz vector. -/
theorem representative_unique (σ : V →ₗ[ℝ] ℝ) (e : V →ₗ[ℝ] H)
    (hdense : DenseRange e) (hfin : BddAbove (Set.range (objective σ e)))
    (v : H) (hv : ∀ φ, ⟪v, e φ⟫_ℝ = σ φ) :
    v = representative σ e := by
  apply (InnerProductSpace.toDual ℝ H).injective
  apply ContinuousLinearMap.ext
  intro z
  refine hdense.induction_on z
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro φ
  simpa only [InnerProductSpace.toDual_apply_apply] using
    (hv φ).trans (representative_pairing σ e hdense hfin φ).symm

/-- Density preserves the exact variational supremum, not merely an upper bound. -/
theorem energy_eq_norm_sq (σ : V →ₗ[ℝ] ℝ) (e : V →ₗ[ℝ] H)
    (hdense : DenseRange e) (hfin : BddAbove (Set.range (objective σ e))) :
    sSup (Set.range (objective σ e)) = ‖representative σ e‖ ^ 2 := by
  apply IsLUB.csSup_eq _ (Set.range_nonempty _)
  constructor
  · rintro y ⟨φ, rfl⟩
    have h := (TangentEnergy.dualObjective_isGreatest (extension σ e)).2
      ⟨e φ, rfl⟩
    simpa only [TangentEnergy.dualObjective, extension_apply σ e hdense hfin,
      representative, objective] using h
  · intro C hC
    have hbound : ∀ z : H, TangentEnergy.dualObjective (extension σ e) z ≤ C := by
      intro z
      refine hdense.induction_on z (isClosed_le (by
        unfold TangentEnergy.dualObjective
        fun_prop) continuous_const) ?_
      intro φ
      simpa only [TangentEnergy.dualObjective, extension_apply σ e hdense hfin,
        objective] using hC ⟨φ, rfl⟩
    have h := hbound (representative σ e)
    simpa [TangentEnergy.dualObjective_eq_sub_sq, representative] using h

end SharpWasserstein.DenseVariational
