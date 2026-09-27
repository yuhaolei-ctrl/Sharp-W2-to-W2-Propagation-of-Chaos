import SharpWasserstein.SinePeriodizationDerivative
import SharpWasserstein.WeightedTangent

/-! Smooth bounded-range compressions of actual Euclidean space, with exact
one-Lipschitz and Jacobian bounds. No sup-norm conversion loss enters the energy. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators ContDiff
namespace SharpWasserstein.RoughEulerianCompression
open WeightedTangent
variable {d : ℕ}

def euclideanCoordinates : Point d ≃L[ℝ] Position d :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)

/-- The smooth bounded-range coordinate sine map, in the genuine Euclidean norm. -/
def compression (R : ℝ) (x : Point d) : Point d :=
  euclideanCoordinates.symm (SinePeriodization.coordinates R (euclideanCoordinates x))

@[simp] theorem compression_apply (R : ℝ) (x : Point d) (i : Fin d) :
    compression R x i = SinePeriodization.scalar R (x i) := rfl

@[simp] theorem compression_zero (R : ℝ) : compression (d := d) R 0 = 0 := by
  ext i
  simp [compression_apply,SinePeriodization.scalar]

theorem compression_contDiff (R : ℝ) : ContDiff ℝ ∞ (compression (d := d) R) :=
  euclideanCoordinates.symm.contDiff.comp
    ((SinePeriodization.coordinates_contDiff R).comp euclideanCoordinates.contDiff)

/-- Summing scalar contractions in squares gives constant one in Euclidean norm. -/
theorem compression_lipschitz {R : ℝ} (hR : R ≠ 0) :
    LipschitzWith 1 (compression (d := d) R) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one,one_mul,dist_eq_norm]
  have hs : ‖compression R x-compression R y‖^2 ≤ ‖x-y‖^2 := by
    simp only [EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_le_sum
    intro i _
    change (SinePeriodization.scalar R (x i)-SinePeriodization.scalar R (y i))^2 ≤ (x i-y i)^2
    have hi := (SinePeriodization.scalar_lipschitz hR).norm_sub_le (x i) (y i)
    simp only [NNReal.coe_one,one_mul,Real.norm_eq_abs] at hi
    exact (sq_le_sq).2 hi
  nlinarith [norm_nonneg (compression R x-compression R y),norm_nonneg (x-y)]

theorem compression_norm_le {R : ℝ} (hR : R ≠ 0) (x : Point d) : ‖compression R x‖ ≤ ‖x‖ := by
  simpa only [compression_zero,sub_zero,NNReal.coe_one,one_mul] using
    (compression_lipschitz (d := d) hR).norm_sub_le x 0

/-- The range lies in an explicit compact Euclidean ball. -/
theorem compression_range_bound (R : ℝ) (x : Point d) :
    ‖compression R x‖ ≤ Real.sqrt (d : ℝ)*|R| := by
  have hs : ‖compression R x‖^2 ≤ (d : ℝ)*|R|^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _i : Fin d, |R|^2 := by
        apply Finset.sum_le_sum
        intro i _
        have ha : |SinePeriodization.scalar R (x i)| ≤ |R| := by
          simpa only [SinePeriodization.scalar,abs_mul,mul_one] using
            mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (x i/R)) (abs_nonneg R)
        change (SinePeriodization.scalar R (x i))^2 ≤ |R|^2
        exact (sq_le_sq).2 (by simpa only [abs_abs] using ha)
      _ = _ := by simp
  have hh : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
  have he : (Real.sqrt (d : ℝ)*|R|)^2 = (d : ℝ)*|R|^2 := by rw [mul_pow,Real.sq_sqrt hh]
  nlinarith [norm_nonneg (compression R x),mul_nonneg (Real.sqrt_nonneg (d : ℝ)) (abs_nonneg R)]

theorem compression_range_subset (R : ℝ) :
    Set.range (compression (d := d) R) ⊆ Metric.closedBall 0 (Real.sqrt (d : ℝ)*|R|) := by
  rintro y ⟨x,rfl⟩
  simpa only [Metric.mem_closedBall,dist_zero_right] using compression_range_bound R x

/-- The actual Fréchet Jacobian is an operator contraction, with no dimension factor. -/
theorem compression_fderiv_norm_le {R : ℝ} (hR : R ≠ 0) (x : Point d) :
    ‖fderiv ℝ (compression R) x‖ ≤ 1 := by
  simpa only [NNReal.coe_one] using norm_fderiv_le_of_lipschitz ℝ
    (compression_lipschitz (d := d) hR) (x₀ := x)

theorem compression_fderiv_apply_norm_le {R : ℝ} (hR : R ≠ 0) (x u : Point d) :
    ‖fderiv ℝ (compression R) x u‖ ≤ ‖u‖ := by
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    ((mul_le_mul_of_nonneg_right (compression_fderiv_norm_le hR x) (norm_nonneg u)).trans_eq (one_mul _))

/-- The compressions tend pointwise to the identity. -/
theorem compression_tendsto (x : Point d) :
    Tendsto (fun k : ℕ => compression ((k : ℝ)+1) x) atTop (𝓝 x) := by
  have ht := euclideanCoordinates.symm.continuous.continuousAt.tendsto.comp
    (SinePeriodization.coordinates_tendsto (euclideanCoordinates x))
  simpa only [ContinuousLinearEquiv.symm_apply_apply,Function.comp_def,compression] using ht

/-- Quadratic displacement domination used by the actual endpoint coupling. -/
theorem compression_displacement_bound {R : ℝ} (hR : R ≠ 0) (x : Point d) :
    ‖compression R x-x‖^2 ≤ 4*‖x‖^2 := by
  have hh := (norm_sub_le (compression R x) x).trans (add_le_add (compression_norm_le hR x) le_rfl)
  nlinarith [norm_nonneg (compression R x-x),norm_nonneg x]

end SharpWasserstein.RoughEulerianCompression
