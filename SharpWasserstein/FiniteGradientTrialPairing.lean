module

public import SharpWasserstein.Compat
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import SharpWasserstein.FiniteGradientTrial

@[expose] public section

/-! The finite coefficient operator has the literal weighted Gram entries
and source coefficients. These formulas connect coercive inversion to the
actual weak probability and source equations. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace BigOperators
namespace SharpWasserstein.FiniteGradientTrial
open WeightedTangent
variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace (Point n)] [BorelSpace (Point n)]
  (μ : Measure (Point n)) [IsFiniteMeasure μ]
  (a : ι → Point n → ℝ) (ha : ∀ i, ContDiff ℝ ∞ (a i))
  (hB : ∀ i, ∃ B : ℝ, ∀ x, ‖gradient (a i) x‖ ≤ B)

theorem gradientMap_single (i : ι) :
    gradientMap μ a ha hB (EuclideanSpace.single i 1) = atomGradient μ a ha hB i := by
  classical
  rw [gradientMap_apply]
  simp [PiLp.single_apply]

omit [DecidableEq ι] in
theorem gradientMap_pairing (c d : EuclideanSpace ℝ ι) :
    ⟪gradientMap μ a ha hB c,gradientMap μ a ha hB d⟫_ℝ =
      ∫ x,⟪gradient (potential a c) x,gradient (potential a d) x⟫_ℝ ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [gradientMap_ae μ a ha hB c,gradientMap_ae μ a ha hB d] with x hx hy
  rw [hx,hy]

omit [DecidableEq ι] in
theorem gradientMap_source_pairing (U : Lp (Point n) 2 μ) (c : EuclideanSpace ℝ ι) :
    ⟪U,gradientMap μ a ha hB c⟫_ℝ =
      ∫ x,⟪gradient (potential a c) x,U x⟫_ℝ ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [gradientMap_ae μ a ha hB c] with x hx
  rw [hx,real_inner_comm]

theorem adjoint_source_coefficient (U : Lp (Point n) 2 μ) (i : ι) :
    (gradientMap μ a ha hB).adjoint U i = ∫ x,⟪gradient (a i) x,U x⟫_ℝ ∂μ := by
  have he := (gradientMap μ a ha hB).adjoint_inner_left (EuclideanSpace.single i 1) U
  rw [gradientMap_single,L2.inner_def] at he
  simp only [EuclideanSpace.inner_single_right,RCLike.conj_to_real,one_mul] at he
  rw [he]
  apply integral_congr_ae
  filter_upwards [atomGradient_ae μ a ha hB i] with x hx
  rw [hx,real_inner_comm]

theorem gram_coefficient (δ : ℝ) (c : EuclideanSpace ℝ ι) (i : ι) :
    RegularizedTrialEnergy.gram (gradientMap μ a ha hB) δ c i =
      (∫ x,⟪gradient (a i) x,gradient (potential a c) x⟫_ℝ ∂μ) + δ*c i := by
  have he := RegularizedTrialEnergy.gram_inner (gradientMap μ a ha hB) δ c (EuclideanSpace.single i 1)
  rw [gradientMap_single,L2.inner_def] at he
  simp only [EuclideanSpace.inner_single_right,RCLike.conj_to_real,one_mul] at he
  rw [he]
  congr 1
  apply integral_congr_ae
  filter_upwards [gradientMap_ae μ a ha hB c,atomGradient_ae μ a ha hB i] with x hx hy
  rw [hx,hy,real_inner_comm]

theorem gram_matrix_entry (δ : ℝ) (i j : ι) :
    RegularizedTrialEnergy.gram (gradientMap μ a ha hB) δ (EuclideanSpace.single j 1) i =
      (∫ x,⟪gradient (a i) x,gradient (a j) x⟫_ℝ ∂μ) + δ*(if i=j then 1 else 0) := by
  rw [gram_coefficient]
  have hp : potential a (EuclideanSpace.single j 1) = a j := by
    funext x
    simp only [potential,Finset.sum_apply,Pi.smul_apply]
    simp [PiLp.single_apply]
  rw [hp]
  simp [PiLp.single_apply]

end SharpWasserstein.FiniteGradientTrial
