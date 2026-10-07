module

public import SharpWasserstein.Compat
public import SharpWasserstein.BrownianGrid
public import SharpWasserstein.ParticleMomentBounds

@[expose] public section

/-! Exact Brownian increment moments and time-increment bounds for the actual
integral trajectories. No supremum-in-time Brownian moment is assumed. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Interval BigOperators
namespace SharpWasserstein
namespace BrownianNoise

theorem scalarLaw_increment_secondMoment {T : ℝ} (s t : Icc 0 T) :
    (∫ w : C(Icc 0 T,ℝ), (w t-w s)^2 ∂scalarLaw T) = 2*|(t : ℝ)-s| := by
  have hm : (∫ w : C(Icc 0 T,ℝ), w t-w s ∂scalarLaw T) = 0 := by
    rw [(scalarLaw_increment_hasLaw s t).integral_eq,integral_id_gaussianReal]
  have hv := (scalarLaw_increment_hasLaw s t).variance_eq
  rw [variance_eq_integral (scalarLaw_increment_hasLaw s t).aemeasurable,hm,
    variance_id_gaussianReal] at hv
  simpa only [sub_zero,NNReal.coe_mul,NNReal.coe_ofNat,coe_nndist,Real.dist_eq] using hv

theorem configurationLaw_increment_cost_integrable {d N : ℕ} {T : ℝ} (s t : Icc 0 T) :
    Integrable (fun w : C(Icc 0 T,Configuration d N) => productCost (w t) (w s))
      (configurationLaw d N T) := by
  unfold productCost
  exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun a _ =>
    ((((configurationLaw_memLp t 2 (by norm_num)).sub
      (configurationLaw_memLp s 2 (by norm_num))).eval i).eval a).integrable_sq))

theorem configurationLaw_coordinate_increment_secondMoment {d N : ℕ} {T : ℝ}
    (s t : Icc 0 T) (i : Fin N) (a : Fin d) :
    (∫ w : C(Icc 0 T,Configuration d N), (w t i a-w s i a)^2 ∂configurationLaw d N T) =
      2*|(t : ℝ)-s| := by
  rw [configurationLaw,integral_map configurationPath_measurable.aemeasurable
    (by fun_prop : Continuous (fun w : C(Icc 0 T,Configuration d N) =>
      (w t i a-w s i a)^2)).measurable.aestronglyMeasurable]
  have he := (labels_coordinate_preserving (T := T) i a).hasLaw.integral_comp
    (by fun_prop : Continuous (fun w : C(Icc 0 T,ℝ) => (w t-w s)^2)).measurable.aestronglyMeasurable
  exact he.trans (scalarLaw_increment_secondMoment s t)

theorem configurationLaw_increment_momentIntegral {d N : ℕ} {T : ℝ} (s t : Icc 0 T) :
    (∫ w : C(Icc 0 T,Configuration d N), productCost (w t) (w s) ∂configurationLaw d N T) =
      (N : ℝ)*d*(2*|(t : ℝ)-s|) := by
  have hc (i : Fin N) (a : Fin d) :
      Integrable (fun w : C(Icc 0 T,Configuration d N) => (w t i a-w s i a)^2)
        (configurationLaw d N T) :=
    ((((configurationLaw_memLp t 2 (by norm_num)).sub
      (configurationLaw_memLp s 2 (by norm_num))).eval i).eval a).integrable_sq
  unfold productCost
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun a _ => hc i a))]
  simp_rw [integral_finsetSum _ (fun a _ => hc _ a),configurationLaw_coordinate_increment_secondMoment]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

end BrownianNoise

theorem productCost_sub_zero {d N : ℕ} (x y : Configuration d N) :
    productCost (x-y) 0 = productCost x y := by simp [productCost]

theorem FiniteAdditiveTrajectory.increment_equation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {v : ℝ → E → E} {w X : ℝ → E} {x : E} {T s t : ℝ}
    (h : FiniteAdditiveTrajectory v w x T X) (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) :
    X t-X s = (∫ r in s..t, v r (X r))+(w t-w s) := by
  have hi (r : ℝ) (hr : r ∈ Icc 0 T) :
      IntervalIntegrable (fun u => v u (X u)) volume 0 r :=
    (h.driftContinuous.mono (Icc_subset_Icc_right hr.2)).intervalIntegrable_of_Icc hr.1
  rw [h.equation t ht,h.equation s hs,
    ← intervalIntegral.integral_interval_sub_left (hi t ht) (hi s hs)]
  abel

theorem FiniteAdditiveTrajectory.increment_productCost_le {d N : ℕ}
    {v : ℝ → Configuration d N → Configuration d N} {w X : ℝ → Configuration d N}
    {x : Configuration d N} {T s t M : ℝ} (h : FiniteAdditiveTrajectory v w x T X)
    (hM : 0 ≤ M) (hb : ∀ r ∈ Icc 0 T, ∀ z, ‖v r z‖ ≤ M)
    (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) :
    productCost (X t) (X s) ≤ 2*((N : ℝ)*d*(M*|t-s|)^2)+2*productCost (w t) (w s) := by
  let I := ∫ r in s..t, v r (X r)
  have hi : ‖I‖ ≤ M*|t-s| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro r hr
    exact hb r ((uIcc_subset_Icc hs ht) (uIoc_subset_uIcc hr)) (X r)
  have hc : productCost I 0 ≤ (N : ℝ)*d*(M*|t-s|)^2 := by
    refine (productCost_le_dimension_norm I 0).trans ?_
    simp only [sub_zero]
    exact mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hi) (by positivity)
  rw [← productCost_sub_zero (X t) (X s),h.increment_equation hs ht]
  exact (productCost_add_zero_le I (w t-w s)).trans (by rw [productCost_sub_zero]; linarith)

end SharpWasserstein
