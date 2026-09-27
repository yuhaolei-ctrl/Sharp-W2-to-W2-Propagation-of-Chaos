import SharpWasserstein.WeightedEnergyDerivative
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Coefficient-regularized Galerkin energy from an actual trial-gradient
operator. The coefficient penalty makes the Gram operator invertible even
when the underlying measure is singular or the trigonometric atoms are
linearly dependent. The residual gap and recovery estimate are exact. -/
noncomputable section
open scoped InnerProductSpace
namespace SharpWasserstein.RegularizedTrialEnergy
variable {C H : Type*} [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (T : C →L[ℝ] H) (δ : ℝ)

def gram : C →L[ℝ] C := T.adjoint.comp T + δ • ContinuousLinearMap.id ℝ C

theorem gram_inner (c d : C) :
    ⟪gram T δ c,d⟫_ℝ = ⟪T c,T d⟫_ℝ + δ*⟪c,d⟫_ℝ := by
  simp only [gram,add_apply,ContinuousLinearMap.comp_apply,
    smul_apply,ContinuousLinearMap.id_apply,inner_add_left,
    real_inner_smul_left,ContinuousLinearMap.adjoint_inner_left]

theorem gram_symmetric (c d : C) : ⟪gram T δ c,d⟫_ℝ = ⟪c,gram T δ d⟫_ℝ := by
  rw [← real_inner_comm c (gram T δ d),gram_inner,gram_inner]
  simp only [real_inner_comm]

theorem gram_coercive (_hδ : 0 < δ) (c : C) : δ*‖c‖^2 ≤ ⟪gram T δ c,c⟫_ℝ := by
  rw [gram_inner,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]
  exact le_add_of_nonneg_left (sq_nonneg _)

theorem gram_isUnit (hδ : 0 < δ) : IsUnit (gram T δ) := by
  have hc : IsCoercive ((innerSL ℝ).comp (gram T δ)) := by
    refine ⟨δ,hδ,fun c => ?_⟩
    change δ*‖c‖*‖c‖ ≤ ⟪gram T δ c,c⟫_ℝ
    simpa only [pow_two,mul_assoc] using gram_coercive T δ hδ c
  refine ⟨hc.continuousLinearEquivOfBilin.toUnit,?_⟩
  apply ContinuousLinearMap.ext
  intro c
  apply ext_inner_right ℝ
  intro d
  exact hc.continuousLinearEquivOfBilin_apply c d

def solution (U : H) : C := Ring.inverse (gram T δ) (T.adjoint U)

theorem solution_equation (hδ : 0 < δ) (U : H) : gram T δ (solution T δ U) = T.adjoint U := by
  obtain ⟨a,ha⟩ := gram_isUnit T δ hδ
  simp [solution,← ha,← mul_apply_eq_comp]

def energy (U : H) : ℝ := ⟪U,T (solution T δ U)⟫_ℝ

theorem solution_tested (hδ : 0 < δ) (U : H) (c : C) :
    ⟪T (solution T δ U),T c⟫_ℝ + δ*⟪solution T δ U,c⟫_ℝ = ⟪U,T c⟫_ℝ := by
  rw [← gram_inner,solution_equation T δ hδ,ContinuousLinearMap.adjoint_inner_left]

theorem energy_eq_penalized_norm (hδ : 0 < δ) (U : H) :
    energy T δ U = ‖T (solution T δ U)‖^2 + δ*‖solution T δ U‖^2 := by
  have h := solution_tested T δ hδ U (solution T δ U)
  simpa only [real_inner_self_eq_norm_sq,energy] using h.symm

theorem energy_nonneg (hδ : 0 < δ) (U : H) : 0 ≤ energy T δ U := by
  rw [energy_eq_penalized_norm T δ hδ]
  positivity

/-- The exact unweighted residual plus coefficient penalty is the energy
lost by the genuine regularized optimizer. -/
theorem energy_gap (hδ : 0 < δ) (U : H) :
    ‖U‖^2-energy T δ U = ‖U-T (solution T δ U)‖^2 + δ*‖solution T δ U‖^2 := by
  have he := energy_eq_penalized_norm T δ hδ U
  rw [norm_sub_sq_real]
  change ‖U‖^2-energy T δ U =
    ‖U‖^2-2*energy T δ U+‖T (solution T δ U)‖^2+δ*‖solution T δ U‖^2
  linarith

theorem energy_le (hδ : 0 < δ) (U : H) : energy T δ U ≤ ‖U‖^2 := by
  have h := energy_gap T δ hδ U
  have hp : 0 ≤ δ*‖solution T δ U‖^2 := mul_nonneg hδ.le (sq_nonneg _)
  linarith [sq_nonneg ‖U-T (solution T δ U)‖]

/-- Every concrete trial coefficient supplies a recovery bound. Thus dense
trial ranges suffice for the limit, even with singular measures. -/
theorem energy_gap_le_trial (hδ : 0 < δ) (U : H) (c : C) :
    ‖U‖^2-energy T δ U ≤ ‖U-T c‖^2 + δ*‖c‖^2 := by
  have hc := WeightedEnergyDerivative.operatorObjective_complete_square
    (gram T δ) (T.adjoint U) (solution T δ U) (solution_equation T δ hδ U)
    (gram_symmetric T δ) c
  rw [WeightedEnergyDerivative.operatorObjective,gram_inner,
    ContinuousLinearMap.adjoint_inner_left,ContinuousLinearMap.adjoint_inner_left,
    real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at hc
  change 2*⟪U,T c⟫_ℝ-(‖T c‖^2+δ*‖c‖^2) = energy T δ U-
    ⟪gram T δ (c-solution T δ U),c-solution T δ U⟫_ℝ at hc
  have hp := gram_coercive T δ hδ (c-solution T δ U)
  have hp' : 0 ≤ δ*‖c-solution T δ U‖^2 := mul_nonneg hδ.le (sq_nonneg _)
  rw [norm_sub_sq_real]
  linarith

end SharpWasserstein.RegularizedTrialEnergy
