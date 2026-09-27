import SharpWasserstein.FiniteCoefficientMatrix

/-! The actual finite weighted Gram matrix is coercive for every finite
measure, including singular measures. Its inverse energy equals the energy
of the constructed weighted trial gradient, with literal source entries. -/
noncomputable section
open MeasureTheory
open scoped ContDiff InnerProductSpace BigOperators
namespace SharpWasserstein.FiniteCoefficientEnergy
open WeightedTangent FiniteCoefficientMatrix FiniteGradientTrial
variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace (Point n)] [BorelSpace (Point n)]

def gramMatrix (μ : Measure (Point n)) (a : ι → Point n → ℝ) (δ : ℝ) :
    EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  matrixOperator (fun i j => (∫ x,⟪gradient (a i) x,gradient (a j) x⟫_ℝ ∂μ) +
    δ*(if i=j then 1 else 0))

def sourceVector (μ : Measure (Point n)) (a : ι → Point n → ℝ) (U : Lp (Point n) 2 μ) :
    EuclideanSpace ℝ ι := coefficientVector (fun i => ∫ x,⟪gradient (a i) x,U x⟫_ℝ ∂μ)

def optimizedEnergy (μ : Measure (Point n)) (a : ι → Point n → ℝ) (δ : ℝ)
    (s : EuclideanSpace ℝ ι) : ℝ := ⟪s,Ring.inverse (gramMatrix μ a δ) s⟫_ℝ

variable (μ : Measure (Point n)) [IsFiniteMeasure μ]
  (a : ι → Point n → ℝ) (ha : ∀ i,ContDiff ℝ ∞ (a i))
  (hB : ∀ i,∃ B : ℝ,∀ x,‖gradient (a i) x‖ ≤ B)

theorem gramMatrix_eq (δ : ℝ) :
    gramMatrix μ a δ = RegularizedTrialEnergy.gram (gradientMap μ a ha hB) δ := by
  rw [← matrixOperator_entries (RegularizedTrialEnergy.gram (gradientMap μ a ha hB) δ)]
  unfold gramMatrix
  congr 1
  funext i j
  exact (gram_matrix_entry μ a ha hB δ i j).symm

theorem sourceVector_eq (U : Lp (Point n) 2 μ) :
    sourceVector μ a U = (gradientMap μ a ha hB).adjoint U := by
  ext i
  rw [adjoint_source_coefficient]
  exact coefficientVector_apply _ i

include ha hB in
theorem gramMatrix_isUnit {δ : ℝ} (hδ : 0 < δ) : IsUnit (gramMatrix μ a δ) := by
  rw [gramMatrix_eq μ a ha hB]
  exact RegularizedTrialEnergy.gram_isUnit _ _ hδ

include ha hB in
theorem gramMatrix_symmetric (δ : ℝ) (c d : EuclideanSpace ℝ ι) :
    ⟪gramMatrix μ a δ c,d⟫_ℝ = ⟪c,gramMatrix μ a δ d⟫_ℝ := by
  rw [gramMatrix_eq μ a ha hB]
  exact RegularizedTrialEnergy.gram_symmetric _ _ _ _

theorem optimizedEnergy_eq (δ : ℝ) (U : Lp (Point n) 2 μ) :
    optimizedEnergy μ a δ (sourceVector μ a U) =
      RegularizedTrialEnergy.energy (gradientMap μ a ha hB) δ U := by
  unfold optimizedEnergy
  rw [gramMatrix_eq μ a ha hB,sourceVector_eq μ a ha hB,
    ContinuousLinearMap.adjoint_inner_left]
  rfl

end SharpWasserstein.FiniteCoefficientEnergy
