import SharpWasserstein.InternalSource
import SharpWasserstein.ExchangeableEntropy
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Full-vector exponential moment and marginal source profile

Jensen's inequality upgrades the coordinate exponential moments to the actual
Euclidean square. The internal source estimate is also specialized to the
project's concrete finite-coordinate marginals and quadratic entropy profile.
-/

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Real
open scoped ENNReal NNReal BigOperators

namespace SharpWasserstein

theorem internalSource_convex_exp_mean_le {d : ℕ} (hd : 0 < d) (u : Fin d → ℝ) :
    exp ((d : ℝ)⁻¹ * ∑ a, u a) ≤ (d : ℝ)⁻¹ * ∑ a, exp (u a) := by
  have hdn : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have h := convexOn_exp.map_sum_le (t := Finset.univ) (w := fun _ : Fin d ↦ (d : ℝ)⁻¹)
    (p := u) (fun _ _ ↦ by positivity) (by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_inv_cancel₀ hdn]) (fun _ _ ↦ Set.mem_univ _)
  simpa only [smul_eq_mul, ← Finset.mul_sum] using h

/-- The full Euclidean square has the claimed uniform exponential moment,
with scale lambda(M)/d and with the diagonal term retained. -/
theorem internalCurrentSquare_exp_le {A : Type*} [MeasurableSpace A]
    {r : Measure A} [IsProbabilityMeasure r] {m d : ℕ} {b : A → A → Fin d → ℝ} {M : ℝ}
    (hd : 0 < d) (hM : 0 ≤ M) (hb : Measurable (Function.uncurry b))
    (hbound : ∀ x y a, |b x y a| ≤ M) (i : Fin m) :
    ∫ x, exp (internalSquareScale M / (d * m : ℝ) * internalCurrentSquare r b i x)
      ∂Measure.pi (fun _ : Fin m ↦ r) ≤ exp 1 * squareExponentialConstant := by
  let Q := Measure.pi fun _ : Fin m ↦ r
  let E := fun (a : Fin d) (x : Fin m → A) ↦
    exp (internalSquareScale M / m * internalScalarCurrent r (fun u v ↦ b u v a) i x ^ 2)
  have hEi (a : Fin d) : Integrable (E a) Q :=
    integrable_exp_sq_of_bounded
      (measurable_internalScalarCurrent (r := r) (b := fun u v ↦ b u v a)
        ((measurable_pi_apply a).comp hb) i)
      (internalScalarCurrent_abs_le (r := r) (b := fun u v ↦ b u v a) ((measurable_pi_apply a).comp hb)
        (fun x y ↦ hbound x y a) i)
      (div_nonneg (internalSquareScale_pos hM).le (Nat.cast_nonneg m))
  have hpoint (x : Fin m → A) :
      exp (internalSquareScale M / (d * m : ℝ) * internalCurrentSquare r b i x) ≤
        (d : ℝ)⁻¹ * ∑ a, E a x := by
    have h := internalSource_convex_exp_mean_le hd
      (fun a ↦ internalSquareScale M / m * internalScalarCurrent r (fun u v ↦ b u v a) i x ^ 2)
    rw [← Finset.mul_sum] at h
    calc
      _ = exp ((d : ℝ)⁻¹ * (internalSquareScale M / m *
          ∑ a, internalScalarCurrent r (fun u v ↦ b u v a) i x ^ 2)) := by
        unfold internalCurrentSquare
        congr 1
        field_simp
      _ ≤ _ := h
  have hright : Integrable (fun x ↦ (d : ℝ)⁻¹ * ∑ a, E a x) Q :=
    (integrable_finsetSum Finset.univ (fun a _ ↦ hEi a)).const_mul _
  have hmeas : Measurable (internalCurrentSquare r b i) := by
    unfold internalCurrentSquare
    apply Finset.measurable_sum
    intro a _
    exact (measurable_internalScalarCurrent (r := r) (b := fun u v ↦ b u v a)
      ((measurable_pi_apply a).comp hb) i).pow_const 2
  have hleft := hright.mono_nonneg
    ((measurable_const.mul hmeas).exp.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun _ ↦ (exp_pos _).le) (Filter.Eventually.of_forall hpoint)
  have h := integral_mono_ae hleft hright (Filter.Eventually.of_forall hpoint)
  rw [integral_const_mul, integral_finsetSum _ (fun a _ ↦ hEi a)] at h
  have hsum : ∑ a : Fin d, ∫ x, E a x ∂Q ≤ d * (exp 1 * squareExponentialConstant) := by
    calc
      _ ≤ ∑ _a : Fin d, exp 1 * squareExponentialConstant :=
        Finset.sum_le_sum (fun a _ ↦ internalScalarCurrent_exp_square_le (r := r)
          (b := fun u v ↦ b u v a) hM ((measurable_pi_apply a).comp hb)
          (fun x y ↦ hbound x y a) i)
      _ = _ := by simp
  have hdn : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  calc
    _ ≤ _ := h
    _ ≤ (d : ℝ)⁻¹ * (d * (exp 1 * squareExponentialConstant)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by field_simp

/-- The internal source has the quadratic particle profile for actual
marginals of a full law. This bound does not need exchangeability. -/
theorem internal_source_marginal_energy_le_profile {d m N : ℕ} {H M : ℝ}
    {r : Measure (Position d)} [IsProbabilityMeasure r]
    {P : Measure (Configuration d N)} [IsProbabilityMeasure P]
    {b : Position d → Position d → Position d}
    (hN : 0 < N) (hm : m ≤ N) (hH : 0 ≤ H) (hM : 0 ≤ M)
    (hb : Measurable (Function.uncurry b)) (hbound : ∀ x y a, |b x y a| ≤ M)
    (hfinite : klDiv P (tensorLaw r N) ≠ ∞)
    (hprofile : ∀ j, j ≤ N → marginalEntropy P r j ≤ H * (j : ℝ) ^ 2 / (N : ℝ) ^ 2) :
    (∫ x, ∑ i : Fin m, internalCurrentSquare r b i x ∂marginal hm P) / (N : ℝ) ^ 2 ≤
      (d * internalSourceConstant M) * (1 + H) * (m : ℝ) ^ 2 / (N : ℝ) ^ 2 := by
  have hraw := internal_source_energy_le_entropy (N := N) (P := marginal hm P)
    hM hb hbound (marginal_klDiv_ne_top hm hfinite)
  change _ ≤ (d * internalSourceConstant M) * (m : ℝ) ^ 2 / (N : ℝ) ^ 2 *
    (1 + (klDiv (marginal hm P) (tensorLaw r m)).toReal) at hraw
  rw [← marginalEntropy_eq hm P r] at hraw
  have hp := (hprofile m hm).trans
    (quadratic_profile_le_constant hH (by exact_mod_cast hN) (Nat.cast_nonneg m)
      (by exact_mod_cast hm))
  have hc : 0 ≤ (d * internalSourceConstant M) * (m : ℝ) ^ 2 / (N : ℝ) ^ 2 := by
    have := internalSourceConstant_nonneg hM
    positivity
  calc
    _ ≤ _ := hraw
    _ ≤ (d * internalSourceConstant M) * (m : ℝ) ^ 2 / (N : ℝ) ^ 2 * (1 + H) :=
      mul_le_mul_of_nonneg_left (by linarith) hc
    _ = _ := by ring

end SharpWasserstein
