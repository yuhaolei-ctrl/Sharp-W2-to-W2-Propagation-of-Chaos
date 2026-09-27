import SharpWasserstein.PhysicalFourierTrialExternal

/-! A genuine finite physical Fourier hierarchy estimate. The full diffusion
absorbs both internal trial residual and external Hessian losses; the sole
remaining auxiliary drift bound multiplies the vanishing own-energy gap. -/
noncomputable section
open MeasureTheory
open scoped ContDiff InnerProductSpace BigOperators
namespace SharpWasserstein.PhysicalFourierTrialHierarchy
open WeightedTangent WeightedMarginal PeriodicFourierTests BochnerIdentity
open WeightedPeriodicFourierPhysical RegularizedTrialConvergencePhysical
open FiniteGradientTrial ExternalInteraction NoiseAverage
variable {d m : ℕ} [MeasurableSpace (Point (m*d))] [BorelSpace (Point (m*d))]
  [MeasurableSpace (Point (m*d+d))] [BorelSpace (Point (m*d+d))]
  (P : ℝ) (μ : Measure (Point (m*d+d))) [IsFiniteMeasure μ]

theorem finite_hierarchy_le (σ : Test (m*d+d) →ₗ[ℝ] ℝ)
    (s : Finset ((Fin (m*d) → ℤ) × Bool)) {δ : ℝ} (hδ : 0 < δ)
    {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
    (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
    (hm : 1 ≤ m) (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    {B : Point (m*d) → Point (m*d)} (hB : ContDiff ℝ ∞ B)
    (hBB : AllDerivativesBounded B) {L A : ℝ} (hL : 0 ≤ L) (hA : 0 ≤ A)
    (hBL : ∀ x,‖fderiv ℝ B x‖ ≤ L) (hBA : ∀ x,‖B x‖ ≤ A)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    let T := trial P (marginalLaw μ) s
    let U := (WeightedPeriodicTangentPhysical.representative P (marginalLaw μ)
      (marginalDistribution μ σ)).val.val
    let V := (WeightedPeriodicTangentPhysical.representative P μ σ).val.val
    let c := RegularizedTrialEnergy.solution T δ U
    let f := potential (fun p : s => physicalPotential P (atom p.val)) c
    let e := RegularizedTrialEnergy.energy T δ U
    let q := 2*θ*gradientConstant d M L₁ L₂*(m:ℝ)
    (2*(∫ x,⟪gradient (FiniteGeneratorCalculus.generator B f) x,U x⟫_ℝ ∂marginalLaw μ)-
      (∫ x,FiniteGeneratorCalculus.generator B (fun y => ‖gradient f y‖^2) x ∂marginalLaw μ))+
      θ*(2*(∫ z,⟪V z,gradient (interaction b f) z⟫_ℝ ∂μ)-
        (∫ z,⟪liftedForce b z,
          gradient (fun w => ‖gradient f (prefixProjection (m*d) d w)‖^2) z⟫_ℝ ∂μ)) ≤
      (2*L+2*(d:ℝ)*L₁+1-q)*e+q*WeightedPeriodicTangentPhysical.energy P μ σ+
      4*(L^2+A^2)*(WeightedPeriodicTangentPhysical.energy P (marginalLaw μ)
        (marginalDistribution μ σ)-e) := by
  dsimp only
  let a := fun p : s => physicalPotential P (atom p.val)
  have ha : ∀ p,ContDiff ℝ ∞ (a p) := fun p => physicalPotential_smooth P (smooth_atom p.val)
  have hBa : ∀ p,AllDerivativesBounded (a p) := fun p =>
    physicalPotential_allDerivativesBounded P (smooth_atom p.val) (periodic_atom p.val)
  have hGa : ∀ p,∃ C : ℝ,∀ x,‖gradient (a p) x‖ ≤ C := fun p =>
    physicalPotential_gradient_bound P _ (smooth_atom p.val) (periodic_atom p.val)
  let T := trial P (marginalLaw μ) s
  let U := (WeightedPeriodicTangentPhysical.representative P (marginalLaw μ)
    (marginalDistribution μ σ)).val.val
  let V := (WeightedPeriodicTangentPhysical.representative P μ σ).val.val
  let c := RegularizedTrialEnergy.solution T δ U
  let f := potential a c
  let e := RegularizedTrialEnergy.energy T δ U
  let H := ∫ x,HierarchyAlgebra.frobeniusSq (hessian f x) ∂marginalLaw μ
  have hi := solution_generator_le (marginalLaw μ) a ha hGa δ hδ U hBa
    (fun p => eigenvalue p.val.1/P^2) (fun p x => physicalAtom_laplacian P p.val x)
    (fun p => physicalAtom_eigenvalue_nonneg P p.val) hB hBB hL hA hBL hBA
    (show (0:ℝ)<1/2 by norm_num)
  have he := PhysicalFourierTrialExternal.integral_external_trial_le P μ σ s hδ
    hb hbound hm hM hL₁ hL₂ (show (0:ℝ)<1/2 by norm_num)
  have heθ := mul_le_mul_of_nonneg_left he hθ
  have hEn : 0 ≤ e := RegularizedTrialEnergy.energy_nonneg T δ hδ U
  have hHn : 0 ≤ H := integral_nonneg (fun _ => HierarchyAlgebra.frobeniusSq_nonneg _)
  have hco : 0 ≤ 2*(d:ℝ)*L₁+(1:ℝ)/2 := by positivity
  have hc := mul_le_mul_of_nonneg_right hθ1 (mul_nonneg hco hEn)
  have hh := mul_le_mul_of_nonneg_right hθ1 hHn
  have hUn : ‖U‖^2 = WeightedPeriodicTangentPhysical.energy P (marginalLaw μ)
      (marginalDistribution μ σ) := by
    rw [WeightedPeriodicTangentPhysical.energy_eq_norm_sq]
    rfl
  dsimp only at hi heθ
  change 2*(∫ x,⟪gradient (FiniteGeneratorCalculus.generator B f) x,U x⟫_ℝ ∂marginalLaw μ)-
    (∫ x,FiniteGeneratorCalculus.generator B (fun y => ‖gradient f y‖^2) x ∂marginalLaw μ) ≤
    (2*L+1/2)*e-(2-1/2)*H+(2*(L^2+A^2)/(1/2))*(‖U‖^2-e) at hi
  rw [hUn] at hi
  change θ*(2*(∫ z,⟪V z,gradient (interaction b f) z⟫_ℝ ∂μ)-
    (∫ z,⟪liftedForce b z,gradient (fun w => ‖gradient f (prefixProjection (m*d) d w)‖^2) z⟫_ℝ ∂μ)) ≤
    θ*((2*(d:ℝ)*L₁+1/2)*e+(1/2)*H+
      (gradientConstant d M L₁ L₂*(m:ℝ)/(1/2))*(WeightedPeriodicTangentPhysical.energy P μ σ-e)) at heθ
  change _ ≤ (2*L+2*(d:ℝ)*L₁+1-2*θ*gradientConstant d M L₁ L₂*(m:ℝ))*e+
    (2*θ*gradientConstant d M L₁ L₂*(m:ℝ))*WeightedPeriodicTangentPhysical.energy P μ σ+
    4*(L^2+A^2)*(WeightedPeriodicTangentPhysical.energy P (marginalLaw μ) (marginalDistribution μ σ)-e)
  nlinarith

end SharpWasserstein.PhysicalFourierTrialHierarchy

namespace SharpWasserstein.PhysicalFourierTrialHierarchy
open WeightedTangent PeriodicFourierTests BochnerIdentity NoiseAverage
open WeightedPeriodicFourierPhysical RegularizedTrialConvergencePhysical FiniteGradientTrial
variable {n : ℕ} [MeasurableSpace (Point n)] [BorelSpace (Point n)]
  (P : ℝ) (μ : Measure (Point n)) [IsFiniteMeasure μ]

/-- The full level has no external term; its actual finite energy has a
uniform drift coefficient and the same vanishing regularization gap. -/
theorem finite_terminal_le (σ : Test n →ₗ[ℝ] ℝ)
    (s : Finset ((Fin n → ℤ) × Bool)) {δ : ℝ} (hδ : 0 < δ)
    {B : Point n → Point n} (hB : ContDiff ℝ ∞ B) (hBB : AllDerivativesBounded B)
    {L A : ℝ} (hL : 0 ≤ L) (hA : 0 ≤ A)
    (hBL : ∀ x,‖fderiv ℝ B x‖ ≤ L) (hBA : ∀ x,‖B x‖ ≤ A) :
    let T := trial P μ s
    let U := (WeightedPeriodicTangentPhysical.representative P μ σ).val.val
    let c := RegularizedTrialEnergy.solution T δ U
    let f := potential (fun p : s => physicalPotential P (atom p.val)) c
    let e := RegularizedTrialEnergy.energy T δ U
    2*(∫ x,⟪gradient (FiniteGeneratorCalculus.generator B f) x,U x⟫_ℝ ∂μ)-
      (∫ x,FiniteGeneratorCalculus.generator B (fun y => ‖gradient f y‖^2) x ∂μ) ≤
      (2*L+1)*e+4*(L^2+A^2)*(WeightedPeriodicTangentPhysical.energy P μ σ-e) := by
  dsimp only
  let a := fun p : s => physicalPotential P (atom p.val)
  have ha : ∀ p,ContDiff ℝ ∞ (a p) := fun p => physicalPotential_smooth P (smooth_atom p.val)
  have hBa : ∀ p,AllDerivativesBounded (a p) := fun p =>
    physicalPotential_allDerivativesBounded P (smooth_atom p.val) (periodic_atom p.val)
  have hGa : ∀ p,∃ C : ℝ,∀ x,‖gradient (a p) x‖ ≤ C := fun p =>
    physicalPotential_gradient_bound P _ (smooth_atom p.val) (periodic_atom p.val)
  let T := trial P μ s
  let U := (WeightedPeriodicTangentPhysical.representative P μ σ).val.val
  let c := RegularizedTrialEnergy.solution T δ U
  let f := potential a c
  let e := RegularizedTrialEnergy.energy T δ U
  have hi := solution_generator_le μ a ha hGa δ hδ U hBa
    (fun p => eigenvalue p.val.1/P^2) (fun p x => physicalAtom_laplacian P p.val x)
    (fun p => physicalAtom_eigenvalue_nonneg P p.val) hB hBB hL hA hBL hBA
    (show (0:ℝ)<1/2 by norm_num)
  have hEn : 0 ≤ e := RegularizedTrialEnergy.energy_nonneg T δ hδ U
  have hHn : 0 ≤ ∫ x,HierarchyAlgebra.frobeniusSq (hessian f x) ∂μ :=
    integral_nonneg (fun _ => HierarchyAlgebra.frobeniusSq_nonneg _)
  have hUn : ‖U‖^2 = WeightedPeriodicTangentPhysical.energy P μ σ := by
    rw [WeightedPeriodicTangentPhysical.energy_eq_norm_sq]
    rfl
  dsimp only at hi
  change 2*(∫ x,⟪gradient (FiniteGeneratorCalculus.generator B f) x,U x⟫_ℝ ∂μ)-
    (∫ x,FiniteGeneratorCalculus.generator B (fun y => ‖gradient f y‖^2) x ∂μ) ≤
    (2*L+1/2)*e-(2-1/2)*(∫ x,HierarchyAlgebra.frobeniusSq (hessian f x) ∂μ)+
    (2*(L^2+A^2)/(1/2))*(‖U‖^2-e) at hi
  rw [hUn] at hi
  change 2*(∫ x,⟪gradient (FiniteGeneratorCalculus.generator B f) x,U x⟫_ℝ ∂μ)-
    (∫ x,FiniteGeneratorCalculus.generator B (fun y => ‖gradient f y‖^2) x ∂μ) ≤
    (2*L+1)*e+4*(L^2+A^2)*(WeightedPeriodicTangentPhysical.energy P μ σ-e)
  nlinarith

end SharpWasserstein.PhysicalFourierTrialHierarchy
