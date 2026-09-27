import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Weighted Cauchy--Schwarz for actual Bochner integrals, with no lower-bound
constant on the weight. This form controls convolution commutators even when
the positive smoothing density approaches zero as the smoothing is removed. -/
noncomputable section
open MeasureTheory Filter
namespace SharpWasserstein.WeightedIntegralSquare

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure Ω} {w r : Ω → ℝ}

theorem weighted_scalar_sq_le (hw : Integrable w μ)
    (hwr : Integrable (fun x => w x*r x) μ)
    (hwr₂ : Integrable (fun x => w x*(r x)^2) μ)
    (hw₀ : ∀ᵐ x ∂μ, 0 ≤ w x) (hZ : 0 < ∫ x, w x ∂μ) :
    (∫ x, w x*r x ∂μ)^2 / (∫ x, w x ∂μ) ≤ ∫ x, w x*(r x)^2 ∂μ := by
  let Z := ∫ x, w x ∂μ
  let A := ∫ x, w x*r x ∂μ
  let B := ∫ x, w x*(r x)^2 ∂μ
  have he : (∫ x, w x*(r x-A/Z)^2 ∂μ) = B-2*(A/Z)*A+(A/Z)^2*Z := by
    have hp : (fun x => w x*(r x-A/Z)^2) =
        (fun x => w x*(r x)^2 - (2*(A/Z))*(w x*r x) + w x*(A/Z)^2) := by
      funext x
      ring
    have hs := integral_add (hwr₂.sub (hwr.const_mul (2*(A/Z)))) (hw.mul_const ((A/Z)^2))
    have ht := integral_sub hwr₂ (hwr.const_mul (2*(A/Z)))
    simp only [Pi.sub_apply] at hs ht
    rw [hp,hs,ht,integral_const_mul,integral_mul_const]
    dsimp [Z,A,B]
    ring
  have hnon : 0 ≤ B-2*(A/Z)*A+(A/Z)^2*Z := by
    rw [← he]
    exact integral_nonneg_of_ae (hw₀.mono (fun x hx => mul_nonneg hx (sq_nonneg _)))
  have hz : Z ≠ 0 := hZ.ne'
  have halg : B-2*(A/Z)*A+(A/Z)^2*Z = B-A^2/Z := by
    field_simp [hz]
    ring
  rw [halg] at hnon
  exact sub_nonneg.mp hnon

theorem weighted_norm_integral_sq_le {v : Ω → E}
    (hw : Integrable w μ)
    (hwn : Integrable (fun x => w x*‖v x‖) μ)
    (hwn₂ : Integrable (fun x => w x*‖v x‖^2) μ)
    (hw₀ : ∀ᵐ x ∂μ, 0 ≤ w x) (hZ : 0 < ∫ x, w x ∂μ) :
    ‖∫ x, w x • v x ∂μ‖^2 / (∫ x, w x ∂μ) ≤ ∫ x, w x*‖v x‖^2 ∂μ := by
  have hn : ‖∫ x, w x • v x ∂μ‖ ≤ ∫ x, w x*‖v x‖ ∂μ := by
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    apply integral_congr_ae
    exact hw₀.mono (fun x hx => by simp [norm_smul, Real.norm_eq_abs,abs_of_nonneg hx])
  exact (div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hn 2) hZ.le).trans
    (weighted_scalar_sq_le hw hwn hwn₂ hw₀ hZ)

end SharpWasserstein.WeightedIntegralSquare
