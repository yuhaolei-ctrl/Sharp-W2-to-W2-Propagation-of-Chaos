module

public import SharpWasserstein.Compat
public import SharpWasserstein.EntropyVariational
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

@[expose] public section

/-! # Bounded measurable dual characterization of actual relative entropy
The reverse variational bound is derived from truncated log densities and Fatou.
In particular, absolute continuity and entropy finiteness are consequences. -/
noncomputable section
open MeasureTheory InformationTheory Real Filter Set
open scoped ENNReal Topology
namespace SharpWasserstein

/-- The maximizer of the entropy dual integrand restricted to `[-n,n]`. -/
def entropyLogClip (n : ℕ) (p : ℝ) : ℝ :=
  if p = 0 then -(n : ℝ) else max (-(n : ℝ)) (min (n : ℝ) (log p))

theorem entropyLogClip_measurable (n : ℕ) : Measurable (entropyLogClip n) := by
  unfold entropyLogClip
  exact Measurable.ite (measurableSet_singleton 0) measurable_const
    (measurable_const.max (measurable_const.min measurable_id.log))

theorem entropyLogClip_abs_le (n : ℕ) (p : ℝ) : |entropyLogClip n p| ≤ n := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  unfold entropyLogClip
  split_ifs <;> rw [abs_le] <;> constructor <;> simp

theorem entropyLogClip_fenchel_nonneg (n : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ p * entropyLogClip n p - exp (entropyLogClip n p) + 1 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  by_cases hp0 : p = 0
  · simp only [entropyLogClip, hp0, ↓reduceIte, zero_mul, zero_sub]
    have he : exp (-(n : ℝ)) ≤ 1 := (exp_le_one_iff).mpr (by linarith)
    linarith
  have hpos : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
  unfold entropyLogClip
  rw [if_neg hp0]
  by_cases hu : (n : ℝ) ≤ log p
  · rw [min_eq_left hu, max_eq_right (by linarith : -(n : ℝ) ≤ n)]
    have hpe : exp (n : ℝ) ≤ p := (le_log_iff_exp_le hpos).mp hu
    have hk := klFun_nonneg (exp_pos (n : ℝ)).le
    rw [klFun, log_exp] at hk
    nlinarith [mul_le_mul_of_nonneg_right hpe hn]
  · rw [min_eq_right (le_of_not_ge hu)]
    by_cases hl : log p ≤ -(n : ℝ)
    · rw [max_eq_left hl]
      have hpe : p ≤ exp (-(n : ℝ)) := (log_le_iff_le_exp hpos).mp hl
      have hk := klFun_nonneg (exp_pos (-(n : ℝ))).le
      rw [klFun, log_exp] at hk
      nlinarith [mul_le_mul_of_nonpos_right hpe (by linarith : -(n : ℝ) ≤ 0)]
    · rw [max_eq_right (le_of_not_ge hl), exp_log hpos]
      have hk := klFun_nonneg hp
      dsimp [klFun] at hk
      linarith

theorem entropyLogClip_fenchel_tendsto {p : ℝ} (hp : 0 ≤ p) :
    Tendsto (fun n : ℕ ↦ p * entropyLogClip n p - exp (entropyLogClip n p) + 1)
      atTop (𝓝 (klFun p)) := by
  by_cases hp0 : p = 0
  · simp only [hp0, entropyLogClip, ↓reduceIte, zero_mul, zero_sub, klFun_zero]
    simpa using ((tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop).neg.add_const 1)
  · have hpos : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
    have he : ∀ᶠ n : ℕ in atTop, |log p| ≤ (n : ℝ) :=
      (tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop |log p|))
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with n hn
    have h1 : log p ≤ (n : ℝ) := (le_abs_self _).trans hn
    have h2 : -(n : ℝ) ≤ log p := by linarith [neg_abs_le (log p)]
    simp [entropyLogClip, hp0, min_eq_right h1, max_eq_right h2, exp_log hpos, klFun]
    ring

variable {A : Type*} [MeasurableSpace A] {μ ν : Measure A}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- A uniform finite dual bound forces absolute continuity; this is not a
hypothesis of the later characterization. -/
theorem absolutelyContinuous_of_bounded_entropy_tests {C : ℝ}
    (htest : ∀ f : A → ℝ, Measurable f → (∃ M : ℝ, ∀ x, |f x| ≤ M) →
      (∫ x, f x ∂μ) - (∫ x, exp (f x) ∂ν) + 1 ≤ C) : μ ≪ ν := by
  refine Measure.AbsolutelyContinuous.mk fun s hs hνs ↦ ?_
  by_contra hμs
  have hp : 0 < μ.real s := (ENNReal.toReal_pos hμs (measure_ne_top μ s))
  let t : ℝ := (|C| + 1) / μ.real s
  let f : A → ℝ := s.indicator (fun _ ↦ t)
  have hf : Measurable f := measurable_const.indicator hs
  have hb : ∀ x, |f x| ≤ |t| := by
    intro x
    by_cases hx : x ∈ s <;> simp [f, hx]
  have hz : f =ᵐ[ν] 0 := by
    have hsAE : ∀ᵐ x ∂ν, x ∉ s := ae_iff.mpr (by simpa using hνs)
    filter_upwards [hsAE] with x hx
    simp [f, hx]
  have h := htest f hf ⟨|t|, hb⟩
  have he : ∫ x, exp (f x) ∂ν = 1 := by
    calc
      _ = ∫ _, (1 : ℝ) ∂ν := integral_congr_ae (hz.mono fun x hx ↦ by simp [hx])
      _ = 1 := by simp
  have hi : ∫ x, f x ∂μ = |C| + 1 := by
    rw [show f = s.indicator (fun _ ↦ t) from rfl, integral_indicator hs]
    simp only [integral_const, measureReal_restrict_apply_univ,
      smul_eq_mul, t]
    exact mul_div_cancel₀ _ hp.ne'
  rw [he, hi] at h
  linarith [le_abs_self C]

/-- The bounded measurable entropy tests characterize the actual KL bound,
including exclusion of singular parts and infinite entropy. -/
theorem klDiv_le_of_bounded_entropy_tests {C : ℝ}
    (htest : ∀ f : A → ℝ, Measurable f → (∃ M : ℝ, ∀ x, |f x| ≤ M) →
      (∫ x, f x ∂μ) - (∫ x, exp (f x) ∂ν) + 1 ≤ C) :
    klDiv μ ν ≤ ENNReal.ofReal C := by
  have hac := absolutelyContinuous_of_bounded_entropy_tests htest
  let p : A → ℝ := fun x ↦ (μ.rnDeriv ν x).toReal
  let f : ℕ → A → ℝ := fun n x ↦ entropyLogClip n (p x)
  let g : ℕ → A → ℝ := fun n x ↦ p x * f n x - exp (f n x) + 1
  have hp : Measurable p := (Measure.measurable_rnDeriv μ ν).ennreal_toReal
  have hf (n : ℕ) : Measurable (f n) := (entropyLogClip_measurable n).comp hp
  have hb (n : ℕ) (x : A) : |f n x| ≤ n := entropyLogClip_abs_le n (p x)
  have hfi (n : ℕ) : Integrable (f n) μ :=
    Integrable.of_bound (hf n).aestronglyMeasurable n (ae_of_all _ (hb n))
  have hei (n : ℕ) : Integrable (fun x ↦ exp (f n x)) ν := by
    apply Integrable.of_bound (hf n).exp.aestronglyMeasurable (exp (n : ℝ))
    exact ae_of_all _ fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      exact exp_le_exp.mpr ((le_abs_self _).trans (hb n x))
  have hgi (n : ℕ) : Integrable (g n) ν :=
    (((integrable_toReal_rnDeriv_mul_iff hac).mpr (hfi n)).sub (hei n)).add
      (integrable_const 1)
  have hg0 (n : ℕ) (x : A) : 0 ≤ g n x := entropyLogClip_fenchel_nonneg n ENNReal.toReal_nonneg
  have hgm (n : ℕ) : Measurable (fun x ↦ ENNReal.ofReal (g n x)) :=
    (((hp.mul (hf n)).sub (hf n).exp).add measurable_const).ennreal_ofReal
  have hgint (n : ℕ) : ∫ x, g n x ∂ν ≤ C := by
    have h := htest (f n) (hf n) ⟨n, hb n⟩
    change (∫ x, (μ.rnDeriv ν x).toReal * f n x - exp (f n x) + 1 ∂ν) ≤ C
    rw [integral_add (f := fun x ↦ (μ.rnDeriv ν x).toReal * f n x - exp (f n x)) (g := fun _ ↦ (1 : ℝ)) (((integrable_toReal_rnDeriv_mul_iff hac).mpr (hfi n)).sub (hei n))
      (integrable_const 1), integral_sub (f := fun x ↦ (μ.rnDeriv ν x).toReal * f n x) (g := fun x ↦ exp (f n x)) ((integrable_toReal_rnDeriv_mul_iff hac).mpr (hfi n))
      (hei n), integral_toReal_rnDeriv_mul hac]
    simpa using h
  have hglin (n : ℕ) : ∫⁻ x, ENNReal.ofReal (g n x) ∂ν ≤ ENNReal.ofReal C := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hgi n) (ae_of_all _ (hg0 n))]
    exact ENNReal.ofReal_le_ofReal (hgint n)
  have hlim (x : A) : Tendsto (fun n ↦ ENNReal.ofReal (g n x)) atTop
      (𝓝 (ENNReal.ofReal (klFun (p x)))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (entropyLogClip_fenchel_tendsto ENNReal.toReal_nonneg)
  rw [klDiv_eq_lintegral_klFun_of_ac hac]
  calc
    _ = ∫⁻ x, liminf (fun n ↦ ENNReal.ofReal (g n x)) atTop ∂ν :=
      lintegral_congr fun x ↦ (hlim x).liminf_eq.symm
    _ ≤ liminf (fun n ↦ ∫⁻ x, ENNReal.ofReal (g n x) ∂ν) atTop := lintegral_liminf_le hgm
    _ ≤ ENNReal.ofReal C := by
      simpa using liminf_le_liminf (f := atTop) (Filter.Eventually.of_forall hglin)

/-- Every bounded measurable test is bounded by the actual finite entropy. -/
theorem bounded_entropy_test_le_klDiv (hfinite : klDiv μ ν ≠ ∞)
    {f : A → ℝ} (hf : Measurable f) {M : ℝ} (hb : ∀ x, |f x| ≤ M) :
    (∫ x, f x ∂μ) - (∫ x, exp (f x) ∂ν) + 1 ≤ (klDiv μ ν).toReal := by
  have hi : Integrable f μ := Integrable.of_bound hf.aestronglyMeasurable M (ae_of_all _ hb)
  have he : Integrable (fun x ↦ exp (f x)) ν := by
    refine Integrable.of_bound hf.exp.aestronglyMeasurable (exp M) (ae_of_all _ fun x ↦ ?_)
    rw [norm_eq_abs, abs_of_pos (exp_pos _)]
    exact exp_le_exp.mpr ((le_abs_self _).trans (hb x))
  have hl : exp (-M) ≤ ∫ x, exp (f x) ∂ν := by
    calc
      _ = ∫ _, exp (-M) ∂ν := by simp
      _ ≤ _ := integral_mono (integrable_const _) he fun x ↦ exp_le_exp.mpr (by
        have := (abs_le.mp (hb x)).1; linarith)
  have hlog := log_le_sub_one_of_pos ((exp_pos (-M)).trans_le hl)
  have h := integral_le_klDiv_add_log_exp hfinite hi he
  linarith

end SharpWasserstein
