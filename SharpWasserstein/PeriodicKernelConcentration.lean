module

public import SharpWasserstein.Compat
public import SharpWasserstein.PeriodicConvolutionDensity
public import Mathlib.MeasureTheory.Integral.PeakFunction

@[expose] public section

/-! The concrete positive product kernel is an actual approximation of the
identity on the quotient torus. Its concentration follows from the unique
maximum of the cosine potential and Mathlib's proved peak-function theorem. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace SharpWasserstein.PeriodicPositiveKernel
open PeriodicIntegrationByParts PeriodicTorusBridge

def peak {n : ℕ} (x : Coordinates n) : ℝ := Real.exp (∑ i, Real.cos (2*Real.pi*x i))

theorem peak_continuous (n : ℕ) : Continuous (peak (n := n)) := by
  unfold peak
  fun_prop

theorem peak_periodic (n : ℕ) : Periodic (peak (n := n)) := by
  intro i x
  unfold peak
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j = i
  · subst j
    simp only [Pi.add_apply,Pi.single_eq_same]
    have he : 2*Real.pi*(x i+1) = 2*Real.pi*x i+2*Real.pi := by ring
    rw [he,Real.cos_add_two_pi]
  · simp [Pi.single_eq_of_ne hj]

theorem cos_eq_one_iff_circle_zero (x : ℝ) :
    Real.cos (2*Real.pi*x) = 1 ↔ (x : UnitAddCircle) = 0 := by
  rw [Real.cos_eq_one_iff,AddCircle.coe_eq_zero_iff]
  constructor
  · rintro ⟨k,hk⟩
    refine ⟨k,?_⟩
    simp only [zsmul_eq_mul,mul_one]
    nlinarith [Real.pi_pos]
  · rintro ⟨k,hk⟩
    refine ⟨k,?_⟩
    simp only [zsmul_eq_mul,mul_one] at hk
    rw [← hk]
    ring

theorem peak_lt_at_zero {n : ℕ} (x : Coordinates n) (hx : toTorus x ≠ 0) : peak x < peak (0 : Coordinates n) := by
  obtain ⟨i,hi⟩ : ∃ i : Fin n, (x i : UnitAddCircle) ≠ 0 := by
    by_contra! h
    apply hx
    ext i
    exact h i
  apply Real.exp_lt_exp.mpr
  change (∑ i, Real.cos (2*Real.pi*x i)) < ∑ i : Fin n, Real.cos (2*Real.pi*(0 : Coordinates n) i)
  simp only [Pi.zero_apply,mul_zero,Real.cos_zero]
  apply Finset.sum_lt_sum (fun j _ => Real.cos_le_one _)
  exact ⟨i,Finset.mem_univ i,lt_of_le_of_ne (Real.cos_le_one _) (mt (cos_eq_one_iff_circle_zero _).mp hi)⟩

theorem peak_pow {n : ℕ} (m : ℕ) (x : Coordinates n) :
    peak x^m = ∏ i, weight (m : ℝ) (x i) := by
  unfold peak weight
  rw [← Real.exp_nat_mul,Finset.mul_sum,Real.exp_sum]

theorem peak_pow_integral (n m : ℕ) :
    (∫ x, peak x^m ∂cube n) = normalizer (m : ℝ)^n := by
  simp_rw [peak_pow]
  unfold cube
  rw [integral_fintype_prod_eq_prod]
  simp only [normalizer,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

theorem kernel_eq_peak_normalized {n : ℕ} (m : ℕ) (x : Coordinates n) :
    kernel (m : ℝ) x = peak x^m / (∫ z, peak z^m ∂cube n) := by
  rw [peak_pow_integral,peak_pow]
  simp only [kernel,scalar,Finset.prod_div_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

theorem integral_kernel_tendsto {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E]
    {f : Coordinates n → E} (hp : ∀ i, Function.Periodic f (Pi.single i 1)) (hf : Continuous f) :
    Tendsto (fun m : ℕ => ∫ x, kernel (m : ℝ) x • f x ∂cube n) atTop (𝓝 (f 0)) := by
  let c : UnitAddTorus (Fin n) → ℝ := lift (peak (n := n))
  have hc : Continuous c := lift_continuous (peak_periodic n) (peak_continuous n)
  have hzero : toTorus (0 : Coordinates n) = 0 := by ext i; simp [toTorus]
  have hc0 : c 0 = peak (0 : Coordinates n) := by rw [← hzero]; exact lift_toTorus (peak_periodic n) 0
  have hmax : ∀ y ∈ (univ : Set (UnitAddTorus (Fin n))), y ≠ 0 → c y < c 0 := by
    intro y _ hy
    obtain ⟨x,rfl⟩ := toTorus_surjective n y
    rw [show c (toTorus x) = peak x from lift_toTorus (peak_periodic n) x,hc0]
    exact peak_lt_at_zero x hy
  have hpos (y : UnitAddTorus (Fin n)) : 0 < c y := by
    obtain ⟨x,rfl⟩ := toTorus_surjective n y
    rw [show c (toTorus x) = peak x from lift_toTorus (peak_periodic n) x]
    exact Real.exp_pos _
  have h := tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_continuousOn
    (μ := (volume : Measure (UnitAddTorus (Fin n)))) (g := lift f)
    isCompact_univ hc.continuousOn hmax (fun y _ => (hpos y).le) (hpos 0)
    (by simp) (lift_continuous hp hf).continuousOn
  simp only [Measure.restrict_univ] at h
  have hnorm (m : ℕ) : (∫ z, c z^m ∂(volume : Measure (UnitAddTorus (Fin n)))) =
      ∫ x, peak x^m ∂cube n := by
    rw [torus_volume_eq_haar,← integral_toTorus (fun z => c z^m)
      (show AEStronglyMeasurable (fun z => c z^m) (haar n) from (hc.pow m).aestronglyMeasurable)]
    simp only [c,lift_toTorus (peak_periodic n)]
  have hint (m : ℕ) : (∫ z, c z^m • lift f z ∂(volume : Measure (UnitAddTorus (Fin n)))) =
      ∫ x, peak x^m • f x ∂cube n := by
    rw [torus_volume_eq_haar,← integral_toTorus (fun z => c z^m • lift f z)
      (show AEStronglyMeasurable (fun z => c z^m • lift f z) (haar n) from
        ((hc.pow m).smul (lift_continuous hp hf)).aestronglyMeasurable)]
    simp only [c,lift_toTorus (peak_periodic n),lift_toTorus hp]
  have hf0 : lift f 0 = f 0 := by rw [← hzero]; exact lift_toTorus hp 0
  simp only [hnorm,hint,hf0] at h
  convert h using 1
  funext m
  simp_rw [kernel_eq_peak_normalized,div_eq_mul_inv,mul_comm _ ((∫ z, peak z^m ∂cube n)⁻¹),mul_smul]
  exact integral_smul _ _

end SharpWasserstein.PeriodicPositiveKernel
