import SharpWasserstein.PeriodicIntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Real Fourier trial functions on the actual periodic cube. Their genuine
coordinate Laplacians stay in the finite trial space, the property needed to
eliminate the diffusion residual in a Galerkin energy argument. -/

noncomputable section
namespace SharpWasserstein.PeriodicFourierTests
open PeriodicIntegrationByParts
open scoped BigOperators ContDiff

/-- Integer-frequency linear phase in unit-period coordinates. -/
def phase {n : ℕ} (k : Fin n → ℤ) : Coordinates n →L[ℝ] ℝ :=
  (2 * Real.pi) • ∑ i : Fin n, (k i : ℝ) • ContinuousLinearMap.proj i

theorem phase_apply {n : ℕ} (k : Fin n → ℤ) (x : Coordinates n) :
    phase k x = 2 * Real.pi * ∑ i : Fin n, (k i : ℝ) * x i := by
  simp [phase]

theorem phase_single {n : ℕ} (k : Fin n → ℤ) (i : Fin n) :
    phase k (Pi.single i 1) = 2 * Real.pi * (k i : ℝ) := by
  classical
  rw [phase_apply]
  simp [Pi.single_apply]

def cosine {n : ℕ} (k : Fin n → ℤ) (x : Coordinates n) : ℝ := Real.cos (phase k x)
def sine {n : ℕ} (k : Fin n → ℤ) (x : Coordinates n) : ℝ := Real.sin (phase k x)

theorem smooth_cosine {n : ℕ} (k : Fin n → ℤ) : ContDiff ℝ ∞ (cosine k) :=
  Real.contDiff_cos.comp (phase k).contDiff

theorem smooth_sine {n : ℕ} (k : Fin n → ℤ) : ContDiff ℝ ∞ (sine k) :=
  Real.contDiff_sin.comp (phase k).contDiff

theorem periodic_cosine {n : ℕ} (k : Fin n → ℤ) : Periodic (cosine k) := by
  intro i x
  simp only [cosine, map_add, phase_single]
  rw [mul_comm (2 * Real.pi) (k i : ℝ), Real.cos_add_int_mul_two_pi]

theorem periodic_sine {n : ℕ} (k : Fin n → ℤ) : Periodic (sine k) := by
  intro i x
  simp only [sine, map_add, phase_single]
  rw [mul_comm (2 * Real.pi) (k i : ℝ), Real.sin_add_int_mul_two_pi]

theorem partial_cosine {n : ℕ} (k : Fin n → ℤ) (i : Fin n) (x : Coordinates n) :
    coordinatePartial (cosine k) i x = -(2 * Real.pi * (k i : ℝ)) * sine k x := by
  change fderiv ℝ (fun y => Real.cos (phase k y)) x (Pi.single i 1) = _
  rw [((phase k).hasFDerivAt.cos).fderiv]
  simp only [smul_apply, smul_eq_mul, phase_single, sine]
  ring

theorem partial_sine {n : ℕ} (k : Fin n → ℤ) (i : Fin n) (x : Coordinates n) :
    coordinatePartial (sine k) i x = (2 * Real.pi * (k i : ℝ)) * cosine k x := by
  change fderiv ℝ (fun y => Real.sin (phase k y)) x (Pi.single i 1) = _
  rw [((phase k).hasFDerivAt.sin).fderiv]
  simp only [smul_apply, smul_eq_mul, phase_single, cosine]
  ring

theorem coordinatePartial_smul {n : ℕ} (c : ℝ) (f : Coordinates n → ℝ)
    (i : Fin n) (x : Coordinates n) :
    coordinatePartial (c • f) i x = c * coordinatePartial f i x := by
  unfold coordinatePartial
  rw [congrFun (fderiv_const_smul_field (𝕜 := ℝ) (E := Coordinates n) (F := ℝ) c) x]
  rfl

theorem partial_cosine_twice {n : ℕ} (k : Fin n → ℤ) (i : Fin n) (x : Coordinates n) :
    coordinatePartial (coordinatePartial (cosine k) i) i x =
      -(2 * Real.pi * (k i : ℝ)) ^ 2 * cosine k x := by
  rw [show coordinatePartial (cosine k) i = -(2 * Real.pi * (k i : ℝ)) • sine k from
    funext (partial_cosine k i)]
  rw [coordinatePartial_smul, partial_sine]
  ring

theorem partial_sine_twice {n : ℕ} (k : Fin n → ℤ) (i : Fin n) (x : Coordinates n) :
    coordinatePartial (coordinatePartial (sine k) i) i x =
      -(2 * Real.pi * (k i : ℝ)) ^ 2 * sine k x := by
  rw [show coordinatePartial (sine k) i = (2 * Real.pi * (k i : ℝ)) • cosine k from
    funext (partial_sine k i)]
  rw [coordinatePartial_smul, partial_cosine]
  ring

def eigenvalue {n : ℕ} (k : Fin n → ℤ) : ℝ := ∑ i : Fin n, (2 * Real.pi * (k i : ℝ)) ^ 2

theorem laplacian_cosine {n : ℕ} (k : Fin n → ℤ) :
    PeriodicIntegrationByParts.laplacian (cosine k) = (-eigenvalue k) • cosine k := by
  funext x
  simp only [PeriodicIntegrationByParts.laplacian, partial_cosine_twice, eigenvalue, Pi.smul_apply, smul_eq_mul,
    ← Finset.sum_mul, ← Finset.sum_neg_distrib]

theorem laplacian_sine {n : ℕ} (k : Fin n → ℤ) :
    PeriodicIntegrationByParts.laplacian (sine k) = (-eigenvalue k) • sine k := by
  funext x
  simp only [PeriodicIntegrationByParts.laplacian, partial_sine_twice, eigenvalue, Pi.smul_apply, smul_eq_mul,
    ← Finset.sum_mul, ← Finset.sum_neg_distrib]

theorem smooth_coordinatePartial {n : ℕ} {f : Coordinates n → ℝ}
    (hf : ContDiff ℝ ∞ f) (i : Fin n) : ContDiff ℝ ∞ (coordinatePartial f i) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

theorem coordinatePartial_add {n : ℕ} {f g : Coordinates n → ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (i : Fin n) :
    coordinatePartial (f + g) i = coordinatePartial f i + coordinatePartial g i := by
  funext x
  simp only [coordinatePartial, fderiv_add (hf x) (hg x), add_apply, Pi.add_apply]

theorem laplacian_add {n : ℕ} {f g : Coordinates n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    PeriodicIntegrationByParts.laplacian (f + g) = PeriodicIntegrationByParts.laplacian f + PeriodicIntegrationByParts.laplacian g := by
  funext x
  unfold PeriodicIntegrationByParts.laplacian
  simp_rw [coordinatePartial_add (hf.differentiable (by simp)) (hg.differentiable (by simp)),
    coordinatePartial_add ((smooth_coordinatePartial hf _).differentiable (by simp))
      ((smooth_coordinatePartial hg _).differentiable (by simp)), Pi.add_apply]
  exact Finset.sum_add_distrib

theorem laplacian_smul {n : ℕ} (c : ℝ) (f : Coordinates n → ℝ) :
    PeriodicIntegrationByParts.laplacian (c • f) = c • PeriodicIntegrationByParts.laplacian f := by
  funext x
  have he (i : Fin n) : coordinatePartial (c • f) i = c • coordinatePartial f i :=
    funext (coordinatePartial_smul c f i)
  simp_rw [PeriodicIntegrationByParts.laplacian, he, coordinatePartial_smul]
  simp only [Pi.smul_apply, smul_eq_mul, PeriodicIntegrationByParts.laplacian, Finset.mul_sum]

/-- Real sine/cosine Fourier generators, indexed by frequency and phase. -/
def atom {n : ℕ} (p : (Fin n → ℤ) × Bool) : Coordinates n → ℝ :=
  if p.2 then sine p.1 else cosine p.1

theorem smooth_atom {n : ℕ} (p : (Fin n → ℤ) × Bool) : ContDiff ℝ ∞ (atom p) := by
  rcases p with ⟨k, c⟩
  cases c
  · exact smooth_cosine k
  · exact smooth_sine k

theorem periodic_atom {n : ℕ} (p : (Fin n → ℤ) × Bool) : Periodic (atom p) := by
  rcases p with ⟨k, c⟩
  cases c
  · exact periodic_cosine k
  · exact periodic_sine k

theorem laplacian_atom {n : ℕ} (p : (Fin n → ℤ) × Bool) :
    PeriodicIntegrationByParts.laplacian (atom p) = (-eigenvalue p.1) • atom p := by
  rcases p with ⟨k, c⟩
  cases c
  · exact laplacian_cosine k
  · exact laplacian_sine k

/-- A concrete finite space of periodic smooth Fourier functions. -/
def frequencySpace {n : ℕ} (s : Finset ((Fin n → ℤ) × Bool)) :
    Submodule ℝ (Coordinates n → ℝ) := Submodule.span ℝ (atom '' (s : Set _))

instance frequencySpace_finiteDimensional {n : ℕ} (s : Finset ((Fin n → ℤ) × Bool)) :
    FiniteDimensional ℝ (frequencySpace s) :=
  FiniteDimensional.span_of_finite ℝ (s.finite_toSet.image _)

/-- Every finite Fourier trial function is genuinely smooth and periodic, and its
actual Laplacian stays in the same trial space. -/
theorem frequencySpace_properties {n : ℕ} (s : Finset ((Fin n → ℤ) × Bool))
    {f : Coordinates n → ℝ} (hf : f ∈ frequencySpace s) :
    ContDiff ℝ ∞ f ∧ Periodic f ∧ PeriodicIntegrationByParts.laplacian f ∈ frequencySpace s := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      rcases hf with ⟨p, hp, rfl⟩
      refine ⟨smooth_atom p, periodic_atom p, ?_⟩
      rw [laplacian_atom]
      exact (frequencySpace s).smul_mem _ (Submodule.subset_span ⟨p, hp, rfl⟩)
  | zero =>
      refine ⟨contDiff_const, fun _ _ => rfl, ?_⟩
      have he : PeriodicIntegrationByParts.laplacian (0 : Coordinates n → ℝ) = 0 := by
        have hz (i : Fin n) : coordinatePartial (0 : Coordinates n → ℝ) i = 0 := by
          funext x
          simp [coordinatePartial]
        funext x
        simp [PeriodicIntegrationByParts.laplacian, hz]
      rw [he]
      exact (frequencySpace s).zero_mem
  | add f g _ _ hf hg =>
      refine ⟨hf.1.add hg.1, fun i x => congrArg₂ (· + ·) (hf.2.1 i x) (hg.2.1 i x), ?_⟩
      rw [laplacian_add hf.1 hg.1]
      exact (frequencySpace s).add_mem hf.2.2 hg.2.2
  | smul c f _ hf =>
      refine ⟨hf.1.const_smul c, fun i x => congrArg (c • ·) (hf.2.1 i x), ?_⟩
      rw [laplacian_smul]
      exact (frequencySpace s).smul_mem c hf.2.2

end SharpWasserstein.PeriodicFourierTests
