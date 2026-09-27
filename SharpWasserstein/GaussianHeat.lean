import SharpWasserstein.GaussianCovariance
import SharpWasserstein.Dynamics

/-!
# Heat convolution for the Gaussian sharpness example

The explicit particle laws evolve by convolution with independent centered
Gaussians of variance 2t. This is a genuine measure convolution identity;
identification with the weak heat equation is a separate analytic step.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace SharpWasserstein.GaussianSharpness

theorem charFunDual_matrixLaw {m k : ℕ} (A : Fin k → Fin m → ℝ)
    (L : StrongDual ℝ (Fin k → ℝ)) :
    charFunDual (matrixLaw A) L = Complex.exp
      (-((∑ i, ∑ j, (L (Pi.single i 1) * L (Pi.single j 1)) *
        (∑ l, A i l * A j l) : ℝ) : ℂ) / 2) := by
  unfold matrixLaw
  rw [charFunDual_map, charFunDual_standardLabels]
  have he (l : Fin m) : (L.comp (matrixMap A)) (Pi.single l 1) =
      ∑ i, L (Pi.single i 1) * A i l := by
    simp only [ContinuousLinearMap.comp_apply]
    rw [dual_eq_weightedSum]
    simp [Pi.single_apply]
  simp_rw [he, matrix_quadraticForm]

/-- Gaussian convolution adds the actual covariance matrices. -/
theorem matrixLaw_conv_eq {m n p k : ℕ}
    (A : Fin k → Fin m → ℝ) (B : Fin k → Fin n → ℝ) (C : Fin k → Fin p → ℝ)
    (hC : ∀ i j, (∑ l, C i l * C j l) =
      (∑ l, A i l * A j l) + (∑ l, B i l * B j l)) :
    matrixLaw A ∗ matrixLaw B = matrixLaw C := by
  letI := matrixLaw_probability A
  letI := matrixLaw_probability B
  letI := matrixLaw_probability C
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_conv, charFunDual_matrixLaw, charFunDual_matrixLaw,
    charFunDual_matrixLaw, ← Complex.exp_add]
  congr 1
  simp_rw [hC, mul_add, Finset.sum_add_distrib]
  push_cast
  ring

def diagonalMatrix (k : ℕ) (v : ℝ) (i j : Fin k) : ℝ :=
  if i = j then Real.sqrt v else 0

theorem diagonalMatrix_gram (k : ℕ) {v : ℝ} (hv : 0 ≤ v) (i j : Fin k) :
    (∑ l, diagonalMatrix k v i l * diagonalMatrix k v j l) = if i = j then v else 0 := by
  have h := diagonal_constant_gram (Real.sqrt v) 0 i j
  simpa only [diagonalMatrix, add_zero, mul_zero, zero_pow (by norm_num : 2 ≠ 0),
    Real.sq_sqrt hv] using h

theorem independentLaw_eq_diagonalMatrix (k : ℕ) (v : ℝ) :
    independentLaw k v = (matrixLaw (diagonalMatrix k v)).map (scalarPositions k) := by
  unfold independentLaw matrixLaw
  rw [Measure.map_map (scalarPositions k).continuous.measurable (matrixMap _).continuous.measurable]
  congr 1
  funext ω i j
  simp only [Function.comp_apply, scalarPositions_apply, matrixMap_apply]
  change Real.sqrt v * ω i = ∑ l, diagonalMatrix k v i l * ω l
  simp [diagonalMatrix, ite_mul]

/-- The constructed correlated laws are the free heat convolution of their initial laws. -/
theorem commonNoiseLaw_heat_convolution (k : ℕ) {a s v : ℝ}
    (ha : 0 ≤ a) (hs : 0 ≤ s) (hv : 0 ≤ v) :
    commonNoiseLaw k a s ∗ independentLaw k v = commonNoiseLaw k (a+v) s := by
  rw [independentLaw_eq_diagonalMatrix]
  unfold commonNoiseLaw
  letI := matrixLaw_probability (commonNoiseMatrix k a s)
  letI := matrixLaw_probability (diagonalMatrix k v)
  rw [← Measure.map_conv_continuousLinearMap]
  congr 1
  apply matrixLaw_conv_eq
  intro i j
  rw [commonNoiseMatrix_gram k (by positivity) hs, commonNoiseMatrix_gram k ha hs,
    diagonalMatrix_gram k hv]
  by_cases hij : i = j <;> simp [hij]
  ring

/-- Variance 2t gives precisely the diffusion normalization Δ of the manuscript. -/
theorem particleGaussianLaw_heat_convolution (N : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    particleGaussianLaw N 1 ∗ tensorLaw (oneParticleGaussian (2*t)) N =
      particleGaussianLaw N (1 + 2*t) := by
  rw [← independentLaw_tensor]
  exact commonNoiseLaw_heat_convolution N (by norm_num) (by positivity) (by positivity)

/-- The sharpness data satisfy the exact initial-hierarchy predicate of the main target. -/
theorem gaussian_initialHierarchy :
    InitialHierarchy (1 / 4) (oneParticleGaussian 1) (fun N => particleGaussianLaw N 1) := by
  intro N hN k hk hkN
  have h := (particleGaussianLaw_initial_allLevels hN).2 k hk hkN
  simpa only [localRate, mul_div_assoc] using h

end SharpWasserstein.GaussianSharpness
