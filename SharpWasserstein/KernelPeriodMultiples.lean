import SharpWasserstein.ExternalInteractionPeriodic

/-! Genuine periodic interaction kernels remain periodic at every positive
integer multiple of their physical period. This is used before recovering
full Euclidean energy by enlarging the test period. -/
noncomputable section
namespace SharpWasserstein.KernelPeriodMultiples
variable {d : ℕ} {P : ℝ} {b : Position d → Position d → Position d}

theorem first (h : ∀ i x y,b (x+Pi.single i P) y = b x y) (j : ℕ) :
    ∀ i x y,b (x+Pi.single i ((j:ℝ)*P)) y = b x y := by
  intro i x y
  have hp : Function.Periodic (fun z => b z y) (Pi.single i P) := fun z => h i z y
  have he : j • (Pi.single i P : Position d) = (Pi.single i ((j:ℝ)*P) : Position d) := by
    ext r
    by_cases hr : r=i <;> simp [hr,nsmul_eq_mul]
  simpa only [he] using hp.nsmul j x

theorem second (h : ∀ i x y,b x (y+Pi.single i P) = b x y) (j : ℕ) :
    ∀ i x y,b x (y+Pi.single i ((j:ℝ)*P)) = b x y := by
  intro i x y
  have hp : Function.Periodic (b x) (Pi.single i P) := fun z => h i x z
  have he : j • (Pi.single i P : Position d) = (Pi.single i ((j:ℝ)*P) : Position d) := by
    ext r
    by_cases hr : r=i <;> simp [hr,nsmul_eq_mul]
  simpa only [he] using hp.nsmul j y

end SharpWasserstein.KernelPeriodMultiples
