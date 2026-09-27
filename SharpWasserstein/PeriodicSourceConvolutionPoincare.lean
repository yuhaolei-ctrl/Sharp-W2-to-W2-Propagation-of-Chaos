import SharpWasserstein.PeriodicFourierDensity

/-! A genuine periodic Poincaré inequality, obtained from the Haar Fourier
basis and the already proved derivative coefficient identity. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators ContDiff
namespace SharpWasserstein.PeriodicSourceConvolution
open PeriodicIntegrationByParts PeriodicFourierDerivative PeriodicTorusBridge

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Parseval's identity for actual real periodic functions on the unit cube. -/
theorem coefficient_hasSum_sq {n : ℕ} {f : Coordinates n → ℝ}
    (hf : Continuous f) (hp : Periodic f) :
    HasSum (fun k : Fin n → ℤ => ‖coefficient f k‖^2) (∫ x, (f x)^2 ∂cube n) := by
  let F := complexLift f hp hf
  have h := UnitAddTorus.hasSum_sq_mFourierCoeff (F.toLp 2 volume ℂ)
  have hi : (∫ z, ‖(F.toLp 2 volume ℂ) z‖^2 ∂volume) =
      ∫ z, ‖F z‖^2 ∂haar n := by
    apply integral_congr_ae
    filter_upwards [F.coeFn_toLp (p := 2) (𝕜 := ℂ) volume] with z hz
    rw [hz]
  rw [hi] at h
  have hc : (∫ z, ‖F z‖^2 ∂haar n) = ∫ x, (f x)^2 ∂cube n := by
    calc
      _ = ∫ x, ‖F (toTorus x)‖^2 ∂cube n :=
        (integral_toTorus (fun z => ‖F z‖^2)
          (F.continuous.norm.pow 2).aestronglyMeasurable).symm
      _ = _ := ?_
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      simp only [F,complexLift_toTorus,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  rw [hc] at h
  simpa only [UnitAddTorus.mFourierCoeff_toLp,F,mFourierCoeff_complexLift] using h

/-- The zero mode is the actual mean. -/
theorem coefficient_zero {n : ℕ} (f : Coordinates n → ℝ) :
    coefficient f 0 = ((∫ x, f x ∂cube n : ℝ) : ℂ) := by
  simp [coefficient,cosineCoefficient,sineCoefficient,PeriodicFourierTests.cosine,
    PeriodicFourierTests.sine,PeriodicFourierTests.phase_apply]

/-- The nonzero integer-frequency spectral gap has its literal value. -/
theorem frequency_gap {n : ℕ} {k : Fin n → ℤ} (hk : k ≠ 0) :
    (2*Real.pi)^2 ≤ ∑ i : Fin n, (2*Real.pi*(k i : ℝ))^2 := by
  classical
  obtain ⟨i,hi⟩ : ∃ i,k i ≠ 0 := by
    by_contra hn
    apply hk
    funext i
    simpa using not_exists.mp hn i
  have ha : (1 : ℝ) ≤ |(k i : ℝ)| := by
    exact_mod_cast Int.one_le_abs hi
  have hs : (1 : ℝ) ≤ (k i : ℝ)^2 := by nlinarith [sq_abs (k i : ℝ)]
  have hb : (2*Real.pi)^2 ≤ (2*Real.pi*(k i : ℝ))^2 := by
    nlinarith [mul_nonneg (sq_nonneg (2*Real.pi)) (sub_nonneg.mpr hs)]
  exact hb.trans (Finset.single_le_sum (f := fun j => (2*Real.pi*(k j : ℝ))^2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i))

/-- Genuine periodic Poincaré with sharp spectral constant for zero-mean C¹ functions. -/
theorem periodic_poincare_sq {n : ℕ} {f : Coordinates n → ℝ}
    (hf : ContDiff ℝ 1 f) (hp : Periodic f) (hmean : ∫ x, f x ∂cube n = 0) :
    (2*Real.pi)^2 * (∫ x, (f x)^2 ∂cube n) ≤
      ∑ i : Fin n, ∫ x, (coordinatePartial f i x)^2 ∂cube n := by
  classical
  have hleft := (coefficient_hasSum_sq hf.continuous hp).mul_left ((2*Real.pi)^2)
  have hright := hasSum_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
    coefficient_hasSum_sq (continuous_coordinatePartial hf i) (periodic_coordinatePartial hp i))
  apply hasSum_le _ hleft hright
  intro k
  by_cases hk : k = 0
  · subst k
    simp only [coefficient_zero,hmean,Complex.ofReal_zero,norm_zero,zero_pow,ne_eq,
      OfNat.ofNat_ne_zero,not_false_eq_true,mul_zero]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  · have he (i : Fin n) : ‖coefficient (coordinatePartial f i) k‖^2 =
        (2*Real.pi*(k i : ℝ))^2 * ‖coefficient f k‖^2 := by
      rw [coefficient_coordinatePartial hf hp,norm_mul,norm_mul,Complex.norm_I,mul_one,
        Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
    simp_rw [he,← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (frequency_gap hk) (sq_nonneg _)

/-- Centering removes precisely the constant mode; the actual gradient is unchanged. -/
theorem periodic_poincare_centered_sq {n : ℕ} {f : Coordinates n → ℝ}
    (hf : ContDiff ℝ 1 f) (hp : Periodic f) :
    (2*Real.pi)^2 * (∫ x, (f x - ∫ y, f y ∂cube n)^2 ∂cube n) ≤
      ∑ i : Fin n, ∫ x, (coordinatePartial f i x)^2 ∂cube n := by
  let c : ℝ := ∫ y, f y ∂cube n
  have hg : ContDiff ℝ 1 (fun x => f x-c) := hf.sub contDiff_const
  have hpg : Periodic (fun x => f x-c) := fun i x => congrArg (·-c) (hp i x)
  have hm : ∫ x, (f x-c) ∂cube n = 0 := by
    rw [integral_sub (continuous_integrable_cube hf.continuous) (integrable_const c)]
    simp [c]
  have he (i : Fin n) : coordinatePartial (fun x => f x-c) i = coordinatePartial f i := by
    funext x
    unfold coordinatePartial
    rw [fderiv_fun_sub (hf.differentiable (by norm_num) x) (differentiableAt_const c),
      (hasFDerivAt_const c x).fderiv,sub_zero]
  simpa only [he,c] using periodic_poincare_sq hg hpg hm

end SharpWasserstein.PeriodicSourceConvolution
