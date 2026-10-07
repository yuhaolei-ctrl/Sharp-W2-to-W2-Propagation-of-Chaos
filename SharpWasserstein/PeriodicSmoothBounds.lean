module

public import SharpWasserstein.Compat
public import SharpWasserstein.PeriodicTorusBridge
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

/-! Global derivative bounds for actual smooth coordinate-periodic functions.
Compactness belongs to the genuine quotient torus, with explicit descent. -/
noncomputable section
open Set
open scoped ContDiff NNReal
namespace SharpWasserstein.PeriodicSmoothBounds
open PeriodicIntegrationByParts PeriodicTorusBridge

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ F] in
theorem norm_bound {f : Coordinates n → F}
    (hp : ∀ i, Function.Periodic f (Pi.single i 1)) (hf : Continuous f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C := by
  have hc := (isCompact_univ : IsCompact (univ : Set (UnitAddTorus (Fin n)))).image
    (lift_continuous hp hf)
  obtain ⟨C,hC⟩ := hc.isBounded.exists_norm_le
  refine ⟨max C 0,le_max_right _ _,fun x => ?_⟩
  rw [← lift_toTorus hp x]
  exact (hC _ ⟨toTorus x,mem_univ _,rfl⟩).trans (le_max_left _ _)

theorem periodic_iteratedFDeriv {f : Coordinates n → F}
    (hp : ∀ i, Function.Periodic f (Pi.single i 1)) (m : ℕ) :
    ∀ i, Function.Periodic (iteratedFDeriv ℝ m f) (Pi.single i 1) := by
  intro i x
  have he : (fun y => f (y+Pi.single i 1)) = f := funext (hp i)
  have hd := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := f) m (Pi.single i 1) x
  rw [he] at hd
  exact hd.symm

theorem periodic_fderiv {f : Coordinates n → F}
    (hp : ∀ i, Function.Periodic f (Pi.single i 1)) :
    ∀ i, Function.Periodic (fderiv ℝ f) (Pi.single i 1) := by
  intro i x
  have he : (fun y => f (y+Pi.single i 1)) = f := funext (hp i)
  have hd := fderiv_comp_add_right (𝕜 := ℝ) (f := f) (x := x) (Pi.single i 1)
  rw [he] at hd
  exact hd.symm

theorem iteratedFDeriv_bound {f : Coordinates n → F}
    (hp : ∀ i, Function.Periodic f (Pi.single i 1)) (hf : ContDiff ℝ ∞ f) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ m f x‖ ≤ C :=
  norm_bound (periodic_iteratedFDeriv hp m)
    (ContDiff.continuous_iteratedFDeriv (by exact_mod_cast (show (m : ℕ∞) ≤ ⊤ from le_top)) hf)

theorem exists_lipschitz {f : Coordinates n → F}
    (hp : ∀ i, Function.Periodic f (Pi.single i 1)) (hf : ContDiff ℝ ∞ f) :
    ∃ L : ℝ≥0, LipschitzWith L f := by
  obtain ⟨C,hC,hb⟩ := norm_bound (periodic_fderiv hp) (hf.continuous_fderiv (by simp))
  exact ⟨⟨C,hC⟩,lipschitzWith_of_nnnorm_fderiv_le (hf.differentiable (by simp))
    (fun x => by exact_mod_cast hb x)⟩

end SharpWasserstein.PeriodicSmoothBounds
