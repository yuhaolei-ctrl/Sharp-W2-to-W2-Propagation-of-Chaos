module

public import SharpWasserstein.Compat
public import SharpWasserstein.GaussianHeatCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

@[expose] public section

/-! Genuine integration by parts on the unit periodic cube, with ordinary
Fréchet coordinate derivatives and the actual finite product of interval
Lebesgue measures. Periodicity cancels the boundary terms. -/

noncomputable section
namespace SharpWasserstein.PeriodicIntegrationByParts
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology

abbrev Coordinates (n : ℕ) := Fin n → ℝ

/-- Lebesgue probability measure on one period. -/
def unitInterval : Measure ℝ := volume.restrict (Ioc 0 1)

instance unitInterval_isProbabilityMeasure : IsProbabilityMeasure unitInterval := by
  apply isProbabilityMeasure_iff.mpr
  simp [unitInterval, Real.volume_Ioc]

/-- The genuine periodic fundamental-domain measure. -/
def cube (n : ℕ) : Measure (Coordinates n) := Measure.pi (fun _ => unitInterval)

instance cube_isProbabilityMeasure (n : ℕ) : IsProbabilityMeasure (cube n) := by
  unfold cube
  infer_instance

/-- Actual first coordinate derivative on the finite-dimensional ambient space. -/
def coordinatePartial {n : ℕ} (f : Coordinates n → ℝ) (i : Fin n) (x : Coordinates n) : ℝ :=
  fderiv ℝ f x (Pi.single i 1)

/-- Unit-periodicity in every coordinate. -/
def Periodic {n : ℕ} (f : Coordinates n → ℝ) : Prop :=
  ∀ i : Fin n, Function.Periodic f (Pi.single i 1)

theorem continuous_coordinatePartial {n : ℕ} {f : Coordinates n → ℝ}
    (hf : ContDiff ℝ 1 f) (i : Fin n) : Continuous (coordinatePartial f i) :=
  (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const

/-- Compactness of the actual fundamental domain, used only for integrability. -/
theorem cube_ae_mem (n : ℕ) :
    ∀ᵐ x ∂cube n, x ∈ Set.pi Set.univ (fun _ : Fin n => Icc (0 : ℝ) 1) := by
  apply (ae_iff_prob_eq_one (by measurability)).mpr
  change Measure.pi (fun _ : Fin n => unitInterval) (Set.pi Set.univ (fun _ => Icc (0 : ℝ) 1)) = 1
  rw [Measure.pi_pi]
  have he : Icc (0 : ℝ) 1 ∩ Ioc 0 1 = Ioc 0 1 := inter_eq_right.mpr Ioc_subset_Icc_self
  simp [unitInterval, Measure.restrict_apply, measurableSet_Icc, he, Real.volume_Ioc]

/-- Every continuous ambient function is genuinely integrable over a period cube. -/
theorem continuous_integrable_cube {n : ℕ} {f : Coordinates n → ℝ} (hf : Continuous f) :
    Integrable f (cube n) := by
  have hc : IsCompact (Set.pi Set.univ (fun _ : Fin n => Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  obtain ⟨C, hC⟩ := (hc.image hf).isBounded.exists_norm_le
  exact Integrable.of_bound hf.aestronglyMeasurable C ((cube_ae_mem n).mono
    (fun x hx => hC _ ⟨x, hx, rfl⟩))

/-- Integrating a genuine coordinate derivative over a period gives zero. -/
theorem integral_coordinatePartial_eq_zero {n : ℕ} {f : Coordinates n → ℝ}
    (hf : ContDiff ℝ 1 f) (hp : Periodic f) (i : Fin n) :
    ∫ x, coordinatePartial f i x ∂cube n = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := i.isLt; omega : n ≠ 0)
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+1) => ℝ) i).symm
  have hmp : MeasurePreserving e (unitInterval.prod (cube k)) (cube (k+1)) :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (k+1) => unitInterval) i).symm
  have hi := continuous_integrable_cube (continuous_coordinatePartial hf i)
  rw [← hmp.integral_comp' (coordinatePartial f i)]
  have hic : Integrable (fun p => coordinatePartial f i (e p)) (unitInterval.prod (cube k)) :=
    (hmp.integrable_comp hi.aestronglyMeasurable).mpr hi
  rw [integral_prod_symm _ hic]
  have hinner (z : Coordinates k) : ∫ r, coordinatePartial f i (i.insertNth r z) ∂unitInterval = 0 := by
    have hd (r : ℝ) : HasDerivAt (fun t => f (i.insertNth t z))
        (coordinatePartial f i (i.insertNth r z)) r :=
      ((hf.differentiable (by norm_num) (i.insertNth r z)).hasFDerivAt).comp_hasDerivAt r
        (GaussianSharpness.insertNth_hasDerivAt i z r)
    have hc : Continuous (fun r => coordinatePartial f i (i.insertNth r z)) :=
      (continuous_coordinatePartial hf i).comp (continuous_iff_continuousAt.mpr
        (fun r => (GaussianSharpness.insertNth_hasDerivAt i z r).continuousAt))
    change (∫ r in Ioc (0 : ℝ) 1, coordinatePartial f i (i.insertNth r z)) = 0
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r) (hc.intervalIntegrable 0 1)]
    have he : i.insertNth (1 : ℝ) z =
        i.insertNth (α := fun _ : Fin (k+1) => ℝ) (0 : ℝ) z + Pi.single i 1 := by
      simpa only [one_smul] using GaussianSharpness.insertNth_affine i z 1
    rw [he, hp i, sub_self]
  change (∫ z, ∫ r, coordinatePartial f i (i.insertNth r z) ∂unitInterval ∂cube k) = 0
  simp_rw [hinner]
  simp

/-- The actual derivatives inherit periodicity; no derivative periodicity is assumed separately. -/
theorem periodic_coordinatePartial {n : ℕ} {f : Coordinates n → ℝ}
    (hp : Periodic f) (i : Fin n) : Periodic (coordinatePartial f i) := by
  intro j x
  have he : (fun y => f (y + Pi.single j 1)) = f := funext (hp j)
  have hd := fderiv_comp_add_right (𝕜 := ℝ) (f := f) (x := x) (Pi.single j 1)
  rw [he] at hd
  exact congrArg (fun A : Coordinates n →L[ℝ] ℝ => A (Pi.single i 1)) hd.symm

/-- Genuine product rule for periodic coordinate derivatives. -/
theorem coordinatePartial_mul {n : ℕ} {f g : Coordinates n → ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (i : Fin n) (x : Coordinates n) :
    coordinatePartial (fun y => f y * g y) i x =
      f x * coordinatePartial g i x + g x * coordinatePartial f i x := by
  simp only [coordinatePartial, fderiv_fun_mul (hf x) (hg x), add_apply,
    smul_apply, smul_eq_mul]

/-- Actual periodic integration by parts with no boundary or integrability assumptions hidden. -/
theorem integral_mul_coordinatePartial {n : ℕ} {f g : Coordinates n → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (hpf : Periodic f) (hpg : Periodic g)
    (i : Fin n) :
    (∫ x, f x * coordinatePartial g i x ∂cube n) =
      -(∫ x, g x * coordinatePartial f i x ∂cube n) := by
  have he := integral_coordinatePartial_eq_zero (hf.mul hg)
    (fun j x => by exact congrArg₂ (· * ·) (hpf j x) (hpg j x)) i
  simp_rw [coordinatePartial_mul (hf.differentiable (by norm_num))
    (hg.differentiable (by norm_num))] at he
  rw [integral_add (f := fun x => f x * coordinatePartial g i x)
    (g := fun x => g x * coordinatePartial f i x)
    (continuous_integrable_cube (hf.continuous.mul (continuous_coordinatePartial hg i)))
    (continuous_integrable_cube (hg.continuous.mul (continuous_coordinatePartial hf i)))] at he
  linarith

/-- The coordinate Laplacian on a periodic cube uses the genuine second derivatives. -/
def laplacian {n : ℕ} (f : Coordinates n → ℝ) (x : Coordinates n) : ℝ :=
  ∑ i : Fin n, coordinatePartial (coordinatePartial f i) i x

theorem contDiff_coordinatePartial {n : ℕ} {f : Coordinates n → ℝ}
    (hf : ContDiff ℝ 2 f) (i : Fin n) : ContDiff ℝ 1 (coordinatePartial f i) :=
  (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply contDiff_const

/-- Integration of the periodic Laplacian gives the exact Dirichlet form. -/
theorem integral_mul_laplacian {n : ℕ} {f g : Coordinates n → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 2 g) (hpf : Periodic f) (hpg : Periodic g) :
    (∫ x, f x * laplacian g x ∂cube n) =
      -(∫ x, ∑ i : Fin n, coordinatePartial f i x * coordinatePartial g i x ∂cube n) := by
  have hi1 (i : Fin n) := continuous_integrable_cube
    (hf.continuous.mul (continuous_coordinatePartial (contDiff_coordinatePartial hg i) i))
  have hi2 (i : Fin n) := continuous_integrable_cube
    ((continuous_coordinatePartial hf i).mul
      (continuous_coordinatePartial (hg.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)) i))
  simp only [laplacian, Finset.mul_sum]
  rw [integral_finsetSum (f := fun i x => f x * coordinatePartial (coordinatePartial g i) i x)
      _ (fun i _ => hi1 i),
    integral_finsetSum (f := fun i x => coordinatePartial f i x * coordinatePartial g i x)
      _ (fun i _ => hi2 i),
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_mul_coordinatePartial hf (contDiff_coordinatePartial hg i) hpf
    (periodic_coordinatePartial hpg i)]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  ring

/-- The genuine periodic Laplacian is symmetric under the fundamental-domain integral. -/
theorem integral_mul_laplacian_swap {n : ℕ} {f g : Coordinates n → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hpf : Periodic f) (hpg : Periodic g) :
    (∫ x, f x * laplacian g x ∂cube n) = ∫ x, g x * laplacian f x ∂cube n := by
  rw [integral_mul_laplacian (hf.of_le (by norm_num)) hg hpf hpg,
    integral_mul_laplacian (hg.of_le (by norm_num)) hf hpg hpf]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  apply Finset.sum_congr rfl
  intro i _
  ring

end SharpWasserstein.PeriodicIntegrationByParts
