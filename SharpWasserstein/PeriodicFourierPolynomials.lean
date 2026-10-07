module

public import SharpWasserstein.Compat
public import SharpWasserstein.PeriodicFourierDerivative

@[expose] public section

/-! Concrete real Fourier partial sums with differentiation compatibility.
All coefficients are the actual fundamental-cube integrals. -/

noncomputable section
namespace SharpWasserstein.PeriodicFourierPolynomials
open MeasureTheory PeriodicIntegrationByParts PeriodicFourierTests PeriodicFourierDerivative
open scoped BigOperators ContDiff

/-- Both real Fourier atoms are retained for each frequency in the cutoff. -/
def frequencySet {n : ℕ} (s : Finset (Fin n → ℤ)) : Finset ((Fin n → ℤ) × Bool) :=
  s.product Finset.univ

/-- Actual finite real Fourier sum, with the normalization of complex Fourier series. -/
def polynomial {n : ℕ} (s : Finset (Fin n → ℤ)) (f : Coordinates n → ℝ) : Coordinates n → ℝ :=
  ∑ k ∈ s, (cosineCoefficient f k • cosine k + sineCoefficient f k • sine k)

theorem polynomial_mem {n : ℕ} (s : Finset (Fin n → ℤ)) (f : Coordinates n → ℝ) :
    polynomial s f ∈ frequencySpace (frequencySet s) := by
  classical
  unfold polynomial
  apply Submodule.sum_mem
  intro k hk
  apply Submodule.add_mem
  · apply Submodule.smul_mem
    exact Submodule.subset_span ⟨(k, false), Finset.mem_product.mpr ⟨hk, Finset.mem_univ _⟩, rfl⟩
  · apply Submodule.smul_mem
    exact Submodule.subset_span ⟨(k, true), Finset.mem_product.mpr ⟨hk, Finset.mem_univ _⟩, rfl⟩

theorem smooth_polynomial {n : ℕ} (s : Finset (Fin n → ℤ)) (f : Coordinates n → ℝ) :
    ContDiff ℝ ∞ (polynomial s f) :=
  (frequencySpace_properties (frequencySet s) (polynomial_mem s f)).1

theorem periodic_polynomial {n : ℕ} (s : Finset (Fin n → ℤ)) (f : Coordinates n → ℝ) :
    Periodic (polynomial s f) :=
  (frequencySpace_properties (frequencySet s) (polynomial_mem s f)).2.1

/-- Differentiate the actual smooth partial sum term by term. -/
theorem coordinatePartial_polynomial {n : ℕ} (s : Finset (Fin n → ℤ))
    (f : Coordinates n → ℝ) (i : Fin n) (x : Coordinates n) :
    coordinatePartial (polynomial s f) i x =
      ∑ k ∈ s, (-(2 * Real.pi * (k i : ℝ)) * cosineCoefficient f k * sine k x +
        (2 * Real.pi * (k i : ℝ)) * sineCoefficient f k * cosine k x) := by
  classical
  have hd : ∀ k ∈ s, DifferentiableAt ℝ
      (cosineCoefficient f k • cosine k + sineCoefficient f k • sine k) x := by
    intro k _
    exact (((smooth_cosine k).const_smul (cosineCoefficient f k)).add ((smooth_sine k).const_smul (sineCoefficient f k))).differentiable
      (by simp) x
  unfold coordinatePartial polynomial
  rw [fderiv_sum hd, sum_apply]
  apply Finset.sum_congr rfl
  intro k hk
  change coordinatePartial (cosineCoefficient f k • cosine k + sineCoefficient f k • sine k) i x = _
  rw [coordinatePartial_add (f := cosineCoefficient f k • cosine k)
    (g := sineCoefficient f k • sine k)
    (((smooth_cosine k).const_smul (cosineCoefficient f k)).differentiable (by simp))
    (((smooth_sine k).const_smul (sineCoefficient f k)).differentiable (by simp)),
    Pi.add_apply, coordinatePartial_smul, coordinatePartial_smul, partial_cosine, partial_sine]
  ring

/-- The same finite cutoff simultaneously approximates a potential and its gradients:
its derivative is exactly the Fourier partial sum of the actual derivative. -/
theorem coordinatePartial_polynomial_eq {n : ℕ} (s : Finset (Fin n → ℤ))
    {f : Coordinates n → ℝ} (hf : ContDiff ℝ 1 f) (hp : Periodic f) (i : Fin n) :
    coordinatePartial (polynomial s f) i = polynomial s (coordinatePartial f i) := by
  funext x
  rw [coordinatePartial_polynomial]
  simp only [polynomial, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    cosineCoefficient_coordinatePartial hf hp, sineCoefficient_coordinatePartial hf hp]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Each real partial sum is the real part of the genuine complex Fourier series. -/
theorem polynomial_eq_re {n : ℕ} (s : Finset (Fin n → ℤ)) (f : Coordinates n → ℝ)
    (x : Coordinates n) :
    polynomial s f x = (∑ k ∈ s, coefficient f k *
      ((cosine k x : ℂ) + Complex.I * (sine k x : ℂ))).re := by
  simp only [polynomial, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Complex.re_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp [coefficient, Complex.mul_re]

end SharpWasserstein.PeriodicFourierPolynomials
