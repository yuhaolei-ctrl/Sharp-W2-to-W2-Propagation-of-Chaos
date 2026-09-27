import SharpWasserstein.ExchangeableEntropy
import SharpWasserstein.EuclideanDrift
import SharpWasserstein.TransportMoments

/-! Genuine second moments for coordinate marginals and product reference laws. -/
noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace SharpWasserstein

theorem hasSecondMoment_iff_integrable {d N : ℕ} (P : Measure (Configuration d N)) :
    HasSecondMoment P ↔ Integrable (fun x ↦ productCost x 0) P := by
  have hm : AEStronglyMeasurable (fun x : Configuration d N ↦ productCost x 0) P :=
    (measurable_productCost.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  have he := hasFiniteIntegral_iff_ofReal (μ := P)
    (Filter.Eventually.of_forall fun x : Configuration d N ↦ productCost_nonneg x 0)
  exact ⟨fun h ↦ ⟨hm, he.mpr h⟩, fun h ↦ he.mp h.2⟩

theorem hasSecondMoment_marginal {d m N : ℕ} (hm : m ≤ N)
    {P : Measure (Configuration d N)} (hP : HasSecondMoment P) :
    HasSecondMoment (marginal hm P) := by
  unfold HasSecondMoment marginal
  rw [lintegral_map measurable_secondMoment (measurable_restrictCoordinates hm)]
  apply lt_of_le_of_lt (lintegral_mono fun x ↦ ?_) hP
  exact ENNReal.ofReal_le_ofReal (productCost_restrict_le hm x 0)

theorem hasSecondMoment_tensorLaw {d : ℕ} (r : Measure (Position d)) [IsProbabilityMeasure r]
    (hr : Integrable positionSq r) (N : ℕ) : HasSecondMoment (tensorLaw r N) := by
  apply (hasSecondMoment_iff_integrable _).mpr
  have hi (i : Fin N) : Integrable (fun x : Configuration d N ↦ positionSq (x i)) (tensorLaw r N) :=
    (measurePreserving_eval (fun _ : Fin N ↦ r) i).integrable_comp_of_integrable hr
  have h := integrable_finsetSum Finset.univ (fun i _ ↦ hi i)
  simpa only [productCost_eq_sum_positionSq, sub_zero, Pi.zero_apply] using h

end SharpWasserstein
