module

public import SharpWasserstein.Compat
public import SharpWasserstein.TransportMoments
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

/-! Actual transport convergence from common-label mean-square convergence. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace SharpWasserstein

theorem commonLabel_isCoupling {Ω : Type*} [MeasurableSpace Ω] {d N : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] {F G : Ω → Configuration d N}
    (hF : Measurable F) (hG : Measurable G) :
    IsCoupling (Measure.map F P) (Measure.map G P) (Measure.map (fun ω => (F ω,G ω)) P) := by
  refine ⟨Measure.isProbabilityMeasure_map (hF.prodMk hG).aemeasurable, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst (hF.prodMk hG)]
    rfl
  · rw [Measure.map_map measurable_snd (hF.prodMk hG)]
    rfl

theorem wassersteinSq_commonLabel_le {Ω : Type*} [MeasurableSpace Ω] {d N : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] {F G : Ω → Configuration d N}
    (hF : Measurable F) (hG : Measurable G) :
    wassersteinSq (Measure.map F P) (Measure.map G P) ≤
      ∫⁻ ω, ENNReal.ofReal (productCost (F ω) (G ω)) ∂P := by
  have h := wassersteinSq_le_cost (commonLabel_isCoupling P hF hG)
  rw [transportCost, lintegral_map measurable_productCost.ennreal_ofReal (hF.prodMk hG)] at h
  exact h

/-- The dimension factor here concerns only the equivalence with the ambient
Pi norm; the transport cost itself remains unnormalized Euclidean cost. -/
theorem productCost_le_dimension_norm {d N : ℕ} (x y : Configuration d N) :
    productCost x y ≤ (N : ℝ) * d * ‖x-y‖ ^ 2 := by
  have hb (i : Fin N) (a : Fin d) : (x i a-y i a)^2 ≤ ‖x-y‖^2 := by
    have h := (norm_le_pi_norm (x i-y i) a).trans (norm_le_pi_norm (x-y) i)
    simpa only [Pi.sub_apply, Real.norm_eq_abs, sq_abs] using (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h
  calc
    _ ≤ ∑ _i : Fin N, ∑ _a : Fin d, ‖x-y‖ ^ 2 :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun a _ => hb i a
    _ = _ := by simp; ring

theorem wassersteinSq_commonLabel_le_normIntegral {Ω : Type*} [MeasurableSpace Ω] {d N : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] {F G : Ω → Configuration d N}
    (hF : Measurable F) (hG : Measurable G) (hi : Integrable (fun ω => ‖F ω-G ω‖^2) P) :
    wassersteinSq (Measure.map F P) (Measure.map G P) ≤
      ENNReal.ofReal ((N : ℝ) * d * ∫ ω, ‖F ω-G ω‖^2 ∂P) := by
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal (productCost (F ω) (G ω)) ∂P := wassersteinSq_commonLabel_le P hF hG
    _ ≤ ∫⁻ ω, ENNReal.ofReal ((N : ℝ) * d * ‖F ω-G ω‖^2) ∂P :=
      lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (productCost_le_dimension_norm (F ω) (G ω))
    _ = _ := by
      rw [← ofReal_integral_eq_lintegral_ofReal (hi.const_mul _) (Eventually.of_forall (fun _ => by positivity)),
        integral_const_mul]

theorem wassersteinSq_tendsto_zero_of_meanSquare {Ω : Type*} [MeasurableSpace Ω] {d N : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] {F : ℕ → Ω → Configuration d N} {G : Ω → Configuration d N}
    (hF : ∀ n, Measurable (F n)) (hG : Measurable G)
    (hi : ∀ n, Integrable (fun ω => ‖F n ω-G ω‖^2) P)
    (hlim : Tendsto (fun n => ∫ ω, ‖F n ω-G ω‖^2 ∂P) atTop (nhds 0)) :
    Tendsto (fun n => wassersteinSq (Measure.map (F n) P) (Measure.map G P)) atTop (nhds 0) := by
  have hupper := ENNReal.tendsto_ofReal (hlim.const_mul ((N : ℝ)*d))
  simp only [mul_zero, ENNReal.ofReal_zero] at hupper
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun _ => zero_le) (fun n => wassersteinSq_commonLabel_le_normIntegral P (hF n) hG (hi n))

end SharpWasserstein
