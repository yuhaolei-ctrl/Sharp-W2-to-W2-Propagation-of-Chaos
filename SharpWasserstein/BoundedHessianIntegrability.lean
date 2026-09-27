import SharpWasserstein.BochnerIdentity
import SharpWasserstein.BoundedDerivativeLinear

/-! True Hessian-square integrability for bounded smooth potentials under
arbitrary finite measures, including singular ones. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ContDiff InnerProductSpace BigOperators
namespace SharpWasserstein.BochnerIdentity
open WeightedTangent PDEPairings NoiseAverage
variable {n : ℕ}

theorem hessian_entry_continuous {f : Point n → ℝ} (hf : ContDiff ℝ ∞ f) (i j : Fin n) :
    Continuous (fun x => hessian f x i j) :=
  (smooth_directionDeriv (smooth_directionDeriv hf _) _).continuous

theorem hessian_entry_norm_bound {f : Point n → ℝ} (hf : ContDiff ℝ ∞ f)
    {D : ℝ} (hD : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ D) (x : Point n) (i j : Fin n) :
    ‖hessian f x i j‖ ≤ D := by
  rw [hessian,directionDeriv_twice_eq_fderiv (contDiff_two_of_smooth hf)]
  calc
    _ ≤ ‖fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1)‖ * ‖EuclideanSpace.single j (1:ℝ)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ (‖fderiv ℝ (fderiv ℝ f) x‖*‖EuclideanSpace.single i (1:ℝ)‖)*‖EuclideanSpace.single j (1:ℝ)‖ :=
      mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ ≤ D := by simpa using hD x

variable [MeasurableSpace (Point n)] [BorelSpace (Point n)]
  (μ : Measure (Point n)) [IsFiniteMeasure μ]

theorem hessian_square_integrable {f : Point n → ℝ} (hf : ContDiff ℝ ∞ f)
    (hB : AllDerivativesBounded f) :
    Integrable (fun x => HierarchyAlgebra.frobeniusSq (hessian f x)) μ := by
  obtain ⟨D,hD,hbound⟩ := hB.fderiv.fderiv.bounded
  unfold HierarchyAlgebra.frobeniusSq
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  apply Integrable.of_bound ((hessian_entry_continuous hf i j).pow 2).aestronglyMeasurable (D^2)
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    change (hessian f x i j)^2 ≤ D^2
    simpa only [Real.norm_eq_abs,sq_abs] using
      (sq_le_sq₀ (norm_nonneg (hessian f x i j)) hD).mpr (hessian_entry_norm_bound hf hbound x i j)

end SharpWasserstein.BochnerIdentity
