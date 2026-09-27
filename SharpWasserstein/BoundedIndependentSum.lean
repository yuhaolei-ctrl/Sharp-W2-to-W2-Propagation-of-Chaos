import SharpWasserstein.SubGaussianSquare

/-!
# Bounded independent sums under a finite product law

The sub-Gaussian parameter is proved from the individual bounds and the
independence of coordinate evaluations. It is not an assumed concentration
hypothesis. The diagonal term needed by particle systems is handled separately.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal BigOperators

namespace SharpWasserstein

/-- The centered sum of bounded coordinate observables on a product law. -/
def centeredProductSum {A ι : Type*} [MeasurableSpace A] [Fintype ι]
    (r : Measure A) (f : ι → A → ℝ) (x : ι → A) : ℝ :=
  ∑ i, (f i (x i) - ∫ y, f i y ∂r)

theorem centeredProductSum_subGaussian {A ι : Type*} [MeasurableSpace A] [Fintype ι]
    {r : Measure A} [IsProbabilityMeasure r] {f : ι → A → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hf : ∀ i, Measurable (f i)) (hb : ∀ i x, |f i x| ≤ M) :
    HasSubgaussianMGF (centeredProductSum r f)
      ((Fintype.card ι : ℝ≥0) * ⟨M ^ 2, sq_nonneg M⟩) (Measure.pi fun _ : ι ↦ r) := by
  have hsingle (i : ι) : HasSubgaussianMGF (fun y ↦ f i y - ∫ z, f i z ∂r)
      ⟨M ^ 2, sq_nonneg M⟩ r := by
    have h := hasSubgaussianMGF_of_mem_Icc (μ := r) (hf i).aemeasurable
      (Filter.Eventually.of_forall fun x ↦ (abs_le.mp (hb i x)))
    have hc : ((‖M - -M‖₊ / 2) ^ 2) = (⟨M ^ 2, sq_nonneg M⟩ : ℝ≥0) := by
      apply Subtype.ext
      change (‖M - -M‖ / 2) ^ 2 = M ^ 2
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ M - -M)]
      ring
    convert h using 1
    exact hc.symm
  have hcoord (i : ι) : HasSubgaussianMGF
      (fun x : ι → A ↦ f i (x i) - ∫ z, f i z ∂r) ⟨M ^ 2, sq_nonneg M⟩
      (Measure.pi fun _ : ι ↦ r) := by
    have hmap := (measurePreserving_eval (fun _ : ι ↦ r) i).map_eq
    have hs : HasSubgaussianMGF (fun y ↦ f i y - ∫ z, f i z ∂r)
        ⟨M ^ 2, sq_nonneg M⟩ ((Measure.pi fun _ : ι ↦ r).map (Function.eval i)) := by
      rw [hmap]
      exact hsingle i
    exact HasSubgaussianMGF.of_map (μ := Measure.pi fun _ : ι ↦ r)
      (Y := Function.eval i) (X := fun y ↦ f i y - ∫ z, f i z ∂r)
      (measurable_pi_apply i).aemeasurable hs
  have hind : iIndepFun (fun i (x : ι → A) ↦ f i (x i) - ∫ z, f i z ∂r)
      (Measure.pi fun _ : ι ↦ r) :=
    iIndepFun_pi (fun i ↦ ((hf i).sub measurable_const).aemeasurable)
  change HasSubgaussianMGF (fun x : ι → A ↦ ∑ i, (f i (x i) - ∫ z, f i z ∂r)) _ _
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
    HasSubgaussianMGF.sum_of_iIndepFun (s := Finset.univ) hind (fun i _ ↦ hcoord i)

theorem integral_bounded_observable_abs_le {A : Type*} [MeasurableSpace A]
    {r : Measure A} [IsProbabilityMeasure r] {f : A → ℝ} {M : ℝ}
    (hf : Measurable f) (hb : ∀ x, |f x| ≤ M) : |∫ x, f x ∂r| ≤ M := by
  have hi : Integrable f r := (integrable_const M).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ by simpa only [Real.norm_eq_abs] using hb x)
  calc
    _ ≤ ∫ x, |f x| ∂r := abs_integral_le_integral_abs
    _ ≤ ∫ _x, M ∂r := integral_mono_ae hi.abs (integrable_const M)
      (Filter.Eventually.of_forall hb)
    _ = M := by simp

theorem centeredProductSum_abs_le {A ι : Type*} [MeasurableSpace A] [Fintype ι]
    {r : Measure A} [IsProbabilityMeasure r] {f : ι → A → ℝ} {M : ℝ}
    (hf : ∀ i, Measurable (f i)) (hb : ∀ i x, |f i x| ≤ M) (x : ι → A) :
    |centeredProductSum r f x| ≤ (Fintype.card ι : ℝ) * (2 * M) := by
  unfold centeredProductSum
  calc
    _ ≤ ∑ i, |f i (x i) - ∫ y, f i y ∂r| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, 2 * M := Finset.sum_le_sum (fun i _ ↦ by
      have h := abs_sub (f i (x i)) (∫ y, f i y ∂r)
      have hi := integral_bounded_observable_abs_le (r := r) (hf i) (hb i)
      linarith [hb i (x i)])
    _ = _ := by simp

/-- A bounded real observable has integrable square exponent under a finite law. -/
theorem integrable_exp_sq_of_bounded {A : Type*} [MeasurableSpace A]
    {r : Measure A} [IsFiniteMeasure r] {X : A → ℝ} {B q : ℝ}
    (hX : Measurable X) (hb : ∀ x, |X x| ≤ B) (hq : 0 ≤ q) :
    Integrable (fun x ↦ exp (q * X x ^ 2)) r := by
  apply (integrable_const (exp (q * B ^ 2))).mono' (by fun_prop)
  exact Filter.Eventually.of_forall fun x ↦ by
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    apply exp_le_exp.mpr
    have hs := pow_le_pow_left₀ (abs_nonneg (X x)) (hb x) 2
    rw [sq_abs] at hs
    exact mul_le_mul_of_nonneg_left hs hq

/-- Scale depending only on the uniform bound, never on the number of terms. -/
def internalSquareScale (M : ℝ) : ℝ := 1 / (16 * (M + 1) ^ 2)

theorem internalSquareScale_pos {M : ℝ} (hM : 0 ≤ M) : 0 < internalSquareScale M := by
  unfold internalSquareScale
  positivity

/-- The diagonal term costs only a universal factor in the exponential-square
bound for a centered finite independent sum. -/
theorem shifted_centeredProductSum_exp_square_le
    {A : Type*} [MeasurableSpace A] {r : Measure A} [IsProbabilityMeasure r]
    {n : ℕ} {f : Fin n → A → ℝ} {M D : ℝ}
    (hM : 0 ≤ M) (hf : ∀ i, Measurable (f i)) (hb : ∀ i x, |f i x| ≤ M)
    (hD : |D| ≤ 2 * M) :
    ∫ x, exp (internalSquareScale M / (n + 1 : ℝ) * (D + centeredProductSum r f x) ^ 2)
      ∂Measure.pi (fun _ : Fin n ↦ r)
      ≤ exp 1 * squareExponentialConstant := by
  let q := internalSquareScale M / (n + 1 : ℝ)
  let a := sqrt (4 * q)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have hM1 : (0 : ℝ) < M + 1 := by linarith
  have hq : 0 < q := div_pos (internalSquareScale_pos hM) hn1
  have ha : a ^ 2 = 4 * q := Real.sq_sqrt (by positivity)
  have hVn : (n : ℝ) * M ^ 2 ≤ (n + 1) * (M + 1) ^ 2 := by
    nlinarith [mul_nonneg hn hM, sq_nonneg M]
  have hVM : M ^ 2 ≤ (n + 1 : ℝ) * (M + 1) ^ 2 := by
    nlinarith [mul_nonneg hn (sq_nonneg (M + 1)), sq_nonneg M]
  have hqeq : q = 1 / (16 * (n + 1) * (M + 1) ^ 2) := by
    dsimp [q, internalSquareScale]
    field_simp
  have hden : 0 < 16 * (n + 1 : ℝ) * (M + 1) ^ 2 := by positivity
  have hscale : (((n : ℝ≥0) * ⟨M ^ 2, sq_nonneg M⟩ : ℝ≥0) : ℝ) * a ^ 2 ≤ 1 / 2 := by
    change (n : ℝ) * M ^ 2 * a ^ 2 ≤ 1 / 2
    rw [ha, hqeq]
    have h : (4 * (n : ℝ) * M ^ 2) / (16 * (n + 1) * (M + 1) ^ 2) ≤ 1 / 2 :=
      (div_le_iff₀ hden).mpr (by nlinarith)
    convert h using 1; ring
  have hdiag : 2 * q * D ^ 2 ≤ 1 := by
    have hd2 := pow_le_pow_left₀ (abs_nonneg D) hD 2
    rw [sq_abs] at hd2
    have h : (8 * M ^ 2) / (16 * (n + 1 : ℝ) * (M + 1) ^ 2) ≤ 1 :=
      (div_le_iff₀ hden).mpr (by nlinarith)
    have h8 : 8 * q * M ^ 2 ≤ 1 := by rw [hqeq]; convert h using 1; ring
    nlinarith [mul_le_mul_of_nonneg_left hd2 hq.le]
  have hsmeas : Measurable (centeredProductSum r f) := by
    unfold centeredProductSum
    fun_prop
  have hsbound := centeredProductSum_abs_le (r := r) hf hb
  simp only [Fintype.card_fin] at hsbound
  have hsub := centeredProductSum_subGaussian (r := r) hM hf hb
  simp only [Fintype.card_fin] at hsub
  have hs := integral_exp_square_le_of_subGaussian (a := a) hsmeas
    hsub (by positivity : 0 ≤ (n : ℝ) * (2 * M))
    hsbound hscale
  have hleft : Integrable (fun x ↦ exp (q * (D + centeredProductSum r f x) ^ 2))
      (Measure.pi fun _ : Fin n ↦ r) :=
    integrable_exp_sq_of_bounded (measurable_const.add hsmeas)
      (fun x ↦ (abs_add_le D _).trans (add_le_add hD (hsbound x))) hq.le
  have hright : Integrable (fun x ↦ exp ((a * centeredProductSum r f x) ^ 2 / 2))
      (Measure.pi fun _ : Fin n ↦ r) := by
    convert integrable_exp_sq_of_bounded (r := Measure.pi fun _ : Fin n ↦ r) hsmeas hsbound (by positivity : 0 ≤ a ^ 2 / 2) using 1
    funext x
    congr 1
    ring
  change (∫ x, exp (q * (D + centeredProductSum r f x) ^ 2) ∂Measure.pi (fun _ : Fin n ↦ r)) ≤ _
  calc
    _ ≤ ∫ x, exp 1 * exp ((a * centeredProductSum r f x) ^ 2 / 2)
        ∂Measure.pi (fun _ : Fin n ↦ r) := by
      apply integral_mono_ae hleft (hright.const_mul (exp 1))
      exact Filter.Eventually.of_forall fun x ↦ by
        change exp (q * (D + centeredProductSum r f x) ^ 2) ≤
          exp 1 * exp ((a * centeredProductSum r f x) ^ 2 / 2)
        rw [← exp_add]
        apply exp_le_exp.mpr
        have hsq : (D + centeredProductSum r f x) ^ 2 ≤
            2 * D ^ 2 + 2 * centeredProductSum r f x ^ 2 := by
          nlinarith [sq_nonneg (D - centeredProductSum r f x)]
        have h := mul_le_mul_of_nonneg_left hsq hq.le
        rw [mul_pow, ha]
        nlinarith only [h, hdiag]
    _ = exp 1 * (∫ x, exp ((a * centeredProductSum r f x) ^ 2 / 2)
        ∂Measure.pi (fun _ : Fin n ↦ r)) := integral_const_mul _ _
    _ ≤ exp 1 * squareExponentialConstant := mul_le_mul_of_nonneg_left hs (exp_pos 1).le

end SharpWasserstein
