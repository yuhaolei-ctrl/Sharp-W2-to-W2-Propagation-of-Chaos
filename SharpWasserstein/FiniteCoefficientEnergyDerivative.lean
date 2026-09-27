import SharpWasserstein.FiniteCoefficientEnergy
import SharpWasserstein.WeightedEnergyDerivativeWithin

/-! Genuine differentiability of the regularized finite energy in a fixed
coefficient Hilbert space. The underlying measures may change or be singular;
only literal scalar Gram/source derivatives enter the intermediate lemma. -/
noncomputable section
open MeasureTheory
open scoped ContDiff InnerProductSpace
namespace SharpWasserstein.FiniteCoefficientEnergy
open WeightedTangent FiniteCoefficientMatrix
variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace (Point n)] [BorelSpace (Point n)]

omit [BorelSpace (Point n)] in
/-- Scalar matrix entries assemble to a true operator-norm derivative. -/
theorem gramMatrix_hasDerivWithinAt (μ : ℝ → Measure (Point n))
    (a : ι → Point n → ℝ) (δ : ℝ) {G : ι → ι → ℝ} {s : Set ℝ} {t : ℝ}
    (hG : ∀ i j,HasDerivWithinAt
      (fun r => ∫ x,⟪gradient (a i) x,gradient (a j) x⟫_ℝ ∂μ r) (G i j) s t) :
    HasDerivWithinAt (fun r => gramMatrix (μ r) a δ) (matrixOperator G) s t := by
  exact matrixOperator_hasDerivWithinAt (fun i j => (hG i j).add_const _)

/-- The optimizer is constructed by the inverse of the actual weighted
Gram matrix. Its derivative is cancelled algebraically, never postulated. -/
theorem optimizedEnergy_hasDerivWithinAt (μ : ℝ → Measure (Point n))
    (a : ι → Point n → ℝ) (ha : ∀ i,ContDiff ℝ ∞ (a i))
    (hB : ∀ i,∃ B : ℝ,∀ x,‖gradient (a i) x‖ ≤ B)
    {δ : ℝ} (hδ : 0 < δ) {v : ℝ → ι → ℝ} {v' : ι → ℝ}
    {G : ι → ι → ℝ} {s : Set ℝ} {t : ℝ} [IsFiniteMeasure (μ t)]
    (hG : ∀ i j,HasDerivWithinAt
      (fun r => ∫ x,⟪gradient (a i) x,gradient (a j) x⟫_ℝ ∂μ r) (G i j) s t)
    (hv : ∀ i,HasDerivWithinAt (fun r => v r i) (v' i) s t) :
    let c := Ring.inverse (gramMatrix (μ t) a δ) (coefficientVector (v t))
    HasDerivWithinAt (fun r => optimizedEnergy (μ r) a δ (coefficientVector (v r)))
      (2*⟪coefficientVector v',c⟫_ℝ-⟪matrixOperator G c,c⟫_ℝ) s t := by
  obtain ⟨u,hu⟩ := gramMatrix_isUnit (μ t) a ha hB hδ
  exact WeightedEnergyDerivative.hasDerivWithinAt_optimizedEnergy
    (gramMatrix_hasDerivWithinAt μ a δ hG) (coefficientVector_hasDerivWithinAt hv)
    u hu.symm (gramMatrix_symmetric (μ t) a ha hB δ)

end SharpWasserstein.FiniteCoefficientEnergy
