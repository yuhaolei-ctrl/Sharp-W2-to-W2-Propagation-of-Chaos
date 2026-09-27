import SharpWasserstein.SinePeriodization
import Mathlib.Algebra.Order.Floor.Ring

/-! All derivatives of the smooth sine-periodized interaction are globally
bounded. The proof reduces every derivative to a compact fundamental domain
by genuine translation invariance; no derivative bound is postulated. -/
noncomputable section
open Set
namespace SharpWasserstein.SinePeriodization

def latticeVector {d : ℕ} (P : ℝ) (k : Fin d → ℤ) : Position d := fun i => (k i : ℝ)*P

def representative {d : ℕ} (P : ℝ) (x : Position d) : Position d :=
  fun i => Int.fract (x i/P)*P

def latticeIndex {d : ℕ} (P : ℝ) (x : Position d) : Fin d → ℤ := fun i => ⌊x i/P⌋

theorem representative_mem {d : ℕ} {P : ℝ} (hP : 0 < P) (x : Position d) :
    representative P x ∈ Set.pi Set.univ (fun _ : Fin d => Icc (0 : ℝ) P) := by
  intro i _
  exact Ico_subset_Icc_self (Int.fract_div_mul_self_mem_Ico P (x i) hP)

theorem representative_add_lattice {d : ℕ} {P : ℝ} (hP : P ≠ 0) (x : Position d) :
    representative P x+latticeVector P (latticeIndex P x) = x := by
  ext i
  simpa only [representative,latticeVector,latticeIndex,Pi.add_apply,zsmul_eq_mul] using
    Int.fract_div_mul_self_add_zsmul_eq P (x i) hP

theorem coordinates_lattice {d : ℕ} {R : ℝ} (hR : R ≠ 0)
    (k : Fin d → ℤ) (x : Position d) :
    coordinates R (x+latticeVector (2*Real.pi*R) k) = coordinates R x := by
  ext i
  exact (scalar_periodic hR).int_mul (k i) (x i)

theorem kernel_lattice_periodic {d : ℕ} {R : ℝ} (hR : R ≠ 0)
    (b : Position d → Position d → Position d) (k l : Fin d → ℤ) :
    Function.Periodic (Function.uncurry (kernel R b))
      (latticeVector (2*Real.pi*R) k,latticeVector (2*Real.pi*R) l) := by
  intro z
  change b (coordinates R (z.1+latticeVector (2*Real.pi*R) k))
    (coordinates R (z.2+latticeVector (2*Real.pi*R) l)) = b (coordinates R z.1) (coordinates R z.2)
  rw [coordinates_lattice hR,coordinates_lattice hR]

theorem kernel_derivative_lattice_periodic {d : ℕ} {R : ℝ} (hR : R ≠ 0)
    (b : Position d → Position d → Position d) (n : ℕ) (k l : Fin d → ℤ) :
    Function.Periodic (iteratedFDeriv ℝ n (Function.uncurry (kernel R b)))
      (latticeVector (2*Real.pi*R) k,latticeVector (2*Real.pi*R) l) := by
  intro z
  have he := funext (kernel_lattice_periodic hR b k l)
  have hd := iteratedFDeriv_comp_add_right (𝕜 := ℝ)
    (f := Function.uncurry (kernel R b)) n
    (latticeVector (2*Real.pi*R) k,latticeVector (2*Real.pi*R) l) z
  rw [he] at hd
  exact hd.symm

theorem kernel_boundedSmooth {d : ℕ} {R : ℝ} (hR : 0 < R)
    {b : Position d → Position d → Position d}
    (hb : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry b)) : BoundedSmoothKernel (kernel R b) := by
  refine ⟨kernel_contDiff R hb, ?_⟩
  intro n
  let P := 2*Real.pi*R
  have hP : 0 < P := by dsimp [P]; positivity
  let S : Set (Position d) := Set.pi Set.univ (fun _ : Fin d => Icc (0 : ℝ) P)
  have hS : IsCompact S := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hc : Continuous (iteratedFDeriv ℝ n (Function.uncurry (kernel R b))) :=
    ContDiff.continuous_iteratedFDeriv (by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top))
      (kernel_contDiff R hb)
  obtain ⟨C,hC⟩ := ((hS.prod hS).image hc).isBounded.exists_norm_le
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro z
  let y : Position d × Position d := (representative P z.1,representative P z.2)
  have hy : y ∈ S ×ˢ S := ⟨representative_mem hP z.1,representative_mem hP z.2⟩
  have he : y+(latticeVector P (latticeIndex P z.1),latticeVector P (latticeIndex P z.2)) = z := by
    apply Prod.ext
    · exact representative_add_lattice hP.ne' z.1
    · exact representative_add_lattice hP.ne' z.2
  have hp := kernel_derivative_lattice_periodic hR.ne' b n
    (latticeIndex P z.1) (latticeIndex P z.2) y
  change iteratedFDeriv ℝ n (Function.uncurry (kernel R b))
    (y+(latticeVector P (latticeIndex P z.1),latticeVector P (latticeIndex P z.2))) = _ at hp
  rw [he] at hp
  rw [hp]
  exact (hC _ ⟨y,hy,rfl⟩).trans (le_max_left _ _)

end SharpWasserstein.SinePeriodization
