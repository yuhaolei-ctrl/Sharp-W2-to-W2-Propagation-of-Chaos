import SharpWasserstein.PeriodicFourierTests
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Genuine periodic derivative identities for Fourier coefficients, obtained
from integration by parts on the actual fundamental cube. These are the
compatibility identities required for simultaneous approximation of a smooth
potential and all of its coordinate gradients. -/

noncomputable section
namespace SharpWasserstein.PeriodicFourierDerivative
open MeasureTheory PeriodicIntegrationByParts PeriodicFourierTests
open scoped BigOperators ContDiff

/-- The actual real cosine coefficient on the fundamental cube. -/
def cosineCoefficient {n : ℕ} (f : Coordinates n → ℝ) (k : Fin n → ℤ) : ℝ :=
  ∫ x, f x * cosine k x ∂cube n

/-- The actual real sine coefficient on the fundamental cube. -/
def sineCoefficient {n : ℕ} (f : Coordinates n → ℝ) (k : Fin n → ℤ) : ℝ :=
  ∫ x, f x * sine k x ∂cube n

/-- Complex coefficient with the standard negative-frequency convention. -/
def coefficient {n : ℕ} (f : Coordinates n → ℝ) (k : Fin n → ℤ) : ℂ :=
  (cosineCoefficient f k : ℂ) - Complex.I * (sineCoefficient f k : ℂ)

/-- The cosine coefficient of the actual derivative is the corresponding sine coefficient. -/
theorem cosineCoefficient_coordinatePartial {n : ℕ} {f : Coordinates n → ℝ}
    (hf : ContDiff ℝ 1 f) (hp : Periodic f) (k : Fin n → ℤ) (i : Fin n) :
    cosineCoefficient (coordinatePartial f i) k =
      (2 * Real.pi * (k i : ℝ)) * sineCoefficient f k := by
  have h := integral_mul_coordinatePartial hf
    ((smooth_cosine k).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)) hp (periodic_cosine k) i
  simp_rw [partial_cosine] at h
  have he : (∫ x, f x * (-(2 * Real.pi * (k i : ℝ)) * sine k x) ∂cube n) =
      -(2 * Real.pi * (k i : ℝ)) * sineCoefficient f k := by
    rw [sineCoefficient, ← integral_const_mul]
    congr 1
    funext x
    ring
  rw [he] at h
  simp_rw [mul_comm (cosine k _) (coordinatePartial f i _)] at h
  change _ = -cosineCoefficient (coordinatePartial f i) k at h
  linarith

/-- The sine coefficient of the actual derivative has the opposite cosine sign. -/
theorem sineCoefficient_coordinatePartial {n : ℕ} {f : Coordinates n → ℝ}
    (hf : ContDiff ℝ 1 f) (hp : Periodic f) (k : Fin n → ℤ) (i : Fin n) :
    sineCoefficient (coordinatePartial f i) k =
      -(2 * Real.pi * (k i : ℝ)) * cosineCoefficient f k := by
  have h := integral_mul_coordinatePartial hf
    ((smooth_sine k).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)) hp (periodic_sine k) i
  simp_rw [partial_sine] at h
  have he : (∫ x, f x * ((2 * Real.pi * (k i : ℝ)) * cosine k x) ∂cube n) =
      (2 * Real.pi * (k i : ℝ)) * cosineCoefficient f k := by
    rw [cosineCoefficient, ← integral_const_mul]
    congr 1
    funext x
    ring
  rw [he] at h
  simp_rw [mul_comm (sine k _) (coordinatePartial f i _)] at h
  change _ = -sineCoefficient (coordinatePartial f i) k at h
  linarith

/-- The actual coordinate derivative multiplies Fourier coefficients by `2π i kᵢ`. -/
theorem coefficient_coordinatePartial {n : ℕ} {f : Coordinates n → ℝ}
    (hf : ContDiff ℝ 1 f) (hp : Periodic f) (k : Fin n → ℤ) (i : Fin n) :
    coefficient (coordinatePartial f i) k =
      ((2 * Real.pi * (k i : ℝ) : ℝ) : ℂ) * Complex.I * coefficient f k := by
  rw [coefficient, cosineCoefficient_coordinatePartial hf hp,
    sineCoefficient_coordinatePartial hf hp, coefficient]
  apply Complex.ext <;> simp

/-- The constant Fourier coefficient of each genuine periodic derivative is zero. -/
theorem coefficient_coordinatePartial_zero {n : ℕ} {f : Coordinates n → ℝ}
    (hf : ContDiff ℝ 1 f) (hp : Periodic f) (i : Fin n) :
    coefficient (coordinatePartial f i) 0 = 0 := by
  rw [coefficient_coordinatePartial hf hp]
  simp

end SharpWasserstein.PeriodicFourierDerivative
