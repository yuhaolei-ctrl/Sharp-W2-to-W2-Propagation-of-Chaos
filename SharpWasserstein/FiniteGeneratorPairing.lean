module

public import SharpWasserstein.Compat
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import SharpWasserstein.FiniteGeneratorCalculus
public import SharpWasserstein.FiniteCoefficientEnergy

@[expose] public section

/-! Identification of the actual coefficient derivative forms with literal
Euclidean generator integrals. Finite-sum interchange includes its genuine
integrability hypotheses. -/
noncomputable section
open MeasureTheory
open scoped ContDiff InnerProductSpace BigOperators
namespace SharpWasserstein.FiniteGeneratorCalculus
open WeightedTangent FiniteGradientTrial FiniteCoefficientMatrix
variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace (Point n)] [BorelSpace (Point n)]
  (μ : Measure (Point n)) [IsFiniteMeasure μ]
  (b : Point n → Point n) (a : ι → Point n → ℝ) (ha : ∀ i,ContDiff ℝ ∞ (a i))

include ha in
omit [BorelSpace (Point n)] [IsFiniteMeasure μ] in
theorem matrixGenerator_quadratic
    (hI : ∀ i j,Integrable (generator b (fun x => ⟪gradient (a i) x,gradient (a j) x⟫_ℝ)) μ)
    (c : EuclideanSpace ℝ ι) :
    ⟪matrixOperator (fun i j => ∫ x,generator b
      (fun y => ⟪gradient (a i) y,gradient (a j) y⟫_ℝ) x ∂μ) c,c⟫_ℝ =
    ∫ x,generator b (fun y => ‖gradient (potential a c) y‖^2) x ∂μ := by
  simp_rw [generator_gradientSquare_potential b a ha c]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => (hI i j).const_mul (c i*c j)))]
  simp_rw [integral_finsetSum _ (fun j _ => (hI _ j).const_mul (c _*c j)),integral_const_mul]
  simp only [PiLp.inner_apply,RCLike.inner_apply,RCLike.conj_to_real,matrixOperator_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

include ha in
theorem sourceGenerator_pairing (U : Lp (Point n) 2 μ)
    (hG : ∀ i,ContDiff ℝ ∞ (generator b (a i)))
    (hBG : ∀ i,∃ B : ℝ,∀ x,‖gradient (generator b (a i)) x‖ ≤ B)
    (c : EuclideanSpace ℝ ι) :
    ⟪coefficientVector (fun i => ∫ x,⟪gradient (generator b (a i)) x,U x⟫_ℝ ∂μ),c⟫_ℝ =
      ∫ x,⟪gradient (generator b (potential a c)) x,U x⟫_ℝ ∂μ := by
  rw [generator_potential b a ha]
  rw [← gradientMap_source_pairing μ _ hG hBG U c,← ContinuousLinearMap.adjoint_inner_left]
  congr 1
  ext i
  rw [coefficientVector_apply,adjoint_source_coefficient]

end SharpWasserstein.FiniteGeneratorCalculus
