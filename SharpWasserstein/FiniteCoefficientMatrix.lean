import SharpWasserstein.FiniteGradientTrialPairing
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Actual assembly of finite scalar matrix entries into bounded Euclidean
operators. Entrywise derivatives give genuine operator-norm derivatives. -/
noncomputable section
open scoped InnerProductSpace BigOperators Topology
namespace SharpWasserstein.FiniteCoefficientMatrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def matrixOperator (A : ι → ι → ℝ) : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  ∑ i, ∑ j, A i j • (EuclideanSpace.proj (𝕜 := ℝ) j).smulRight (EuclideanSpace.single i (1 : ℝ))

theorem matrixOperator_apply (A : ι → ι → ℝ) (c : EuclideanSpace ℝ ι) (i : ι) :
    matrixOperator A c i = ∑ j,A i j*c j := by
  simp only [matrixOperator,sum_apply,smul_apply,ContinuousLinearMap.smulRight_apply]
  simp [Pi.single_apply]

theorem matrixOperator_single (A : ι → ι → ℝ) (i j : ι) :
    matrixOperator A (EuclideanSpace.single j 1) i = A i j := by
  rw [matrixOperator_apply]
  simp [PiLp.single_apply]

theorem matrixOperator_entries (G : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) :
    matrixOperator (fun i j => G (EuclideanSpace.single j 1) i) = G := by
  ext c i
  rw [matrixOperator_apply]
  have hc : (∑ j,c j • EuclideanSpace.single j (1 : ℝ)) = c := by
    ext j
    simp [Pi.single_apply]
  conv_rhs => rw [← hc]
  simp [mul_comm]

/-- Finitely many actual scalar derivatives control the full operator norm,
as needed to differentiate its inverse without a separate matrix assumption. -/
theorem matrixOperator_hasDerivAt {A : ℝ → ι → ι → ℝ} {A' : ι → ι → ℝ} {t : ℝ}
    (h : ∀ i j, HasDerivAt (fun r => A r i j) (A' i j) t) :
    HasDerivAt (fun r => matrixOperator (A r)) (matrixOperator A') t := by
  exact HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
      (h i j).smul_const ((EuclideanSpace.proj (𝕜 := ℝ) j).smulRight (EuclideanSpace.single i (1 : ℝ)))

theorem matrixOperator_hasDerivWithinAt {A : ℝ → ι → ι → ℝ} {A' : ι → ι → ℝ}
    {s : Set ℝ} {t : ℝ}
    (h : ∀ i j, HasDerivWithinAt (fun r => A r i j) (A' i j) s t) :
    HasDerivWithinAt (fun r => matrixOperator (A r)) (matrixOperator A') s t := by
  exact HasDerivWithinAt.fun_sum (u := Finset.univ) fun i _ =>
    HasDerivWithinAt.fun_sum (u := Finset.univ) fun j _ =>
      (h i j).smul_const ((EuclideanSpace.proj (𝕜 := ℝ) j).smulRight (EuclideanSpace.single i (1 : ℝ)))

def coefficientVector (v : ι → ℝ) : EuclideanSpace ℝ ι := ∑ i,v i • EuclideanSpace.single i (1 : ℝ)

theorem coefficientVector_apply (v : ι → ℝ) (i : ι) : coefficientVector v i = v i := by
  simp [coefficientVector,Pi.single_apply]

theorem coefficientVector_hasDerivAt {v : ℝ → ι → ℝ} {v' : ι → ℝ} {t : ℝ}
    (h : ∀ i, HasDerivAt (fun r => v r i) (v' i) t) :
    HasDerivAt (fun r => coefficientVector (v r)) (coefficientVector v') t :=
  HasDerivAt.fun_sum (u := Finset.univ) fun i _ => (h i).smul_const (EuclideanSpace.single i (1 : ℝ))

theorem coefficientVector_hasDerivWithinAt {v : ℝ → ι → ℝ} {v' : ι → ℝ}
    {s : Set ℝ} {t : ℝ}
    (h : ∀ i, HasDerivWithinAt (fun r => v r i) (v' i) s t) :
    HasDerivWithinAt (fun r => coefficientVector (v r)) (coefficientVector v') s t :=
  HasDerivWithinAt.fun_sum (u := Finset.univ) fun i _ => (h i).smul_const (EuclideanSpace.single i (1 : ℝ))

end SharpWasserstein.FiniteCoefficientMatrix
