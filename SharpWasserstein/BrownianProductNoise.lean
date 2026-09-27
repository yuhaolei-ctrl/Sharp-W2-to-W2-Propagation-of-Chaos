import SharpWasserstein.ConfigurationBrownian
import Mathlib.Probability.Independence.Basic

/-! The constructed configuration Brownian law is a tensor product of actual
one-particle continuous-path laws, followed by deterministic path assembly. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace SharpWasserstein.BrownianNoise

def positionPath {d : ℕ} {T : ℝ} (w : Fin d → C(Icc 0 T, ℝ)) : C(Icc 0 T, Position d) :=
  ⟨fun t a ↦ w a t, continuous_pi fun a ↦ (w a).continuous⟩

theorem positionPath_measurable {d : ℕ} {T : ℝ} :
    Measurable (positionPath (d := d) (T := T)) := by
  apply (ContinuousMap.measurable_iff_eval _).mpr
  intro t
  exact measurable_pi_lambda _ fun a ↦ (continuous_eval_const t).measurable.comp (measurable_pi_apply a)

def positionLaw (d : ℕ) (T : ℝ) : Measure C(Icc 0 T, Position d) :=
  (coordinateLaw d T).map positionPath

instance positionLaw_isProbability (d : ℕ) (T : ℝ) : IsProbabilityMeasure (positionLaw d T) :=
  Measure.isProbabilityMeasure_map positionPath_measurable.aemeasurable

def assemblePositionPaths {d N : ℕ} {T : ℝ}
    (w : Fin N → C(Icc 0 T, Position d)) : C(Icc 0 T, Configuration d N) :=
  ⟨fun t i ↦ w i t, continuous_pi fun i ↦ (w i).continuous⟩

theorem assemblePositionPaths_measurable {d N : ℕ} {T : ℝ} :
    Measurable (assemblePositionPaths (d := d) (N := N) (T := T)) := by
  apply (ContinuousMap.measurable_iff_eval _).mpr
  intro t
  exact measurable_pi_lambda _ fun i ↦ (continuous_eval_const t).measurable.comp (measurable_pi_apply i)

/-- Genuine path-law product factorization of the constructed Brownian noise. -/
theorem configurationLaw_eq_position_product (d N : ℕ) (T : ℝ) :
    configurationLaw d N T = (Measure.pi fun _ : Fin N ↦ positionLaw d T).map assemblePositionPaths := by
  have hp : (pathLabels d N T).map (fun w i ↦ positionPath (w i)) =
      Measure.pi fun _ : Fin N ↦ positionLaw d T :=
    Measure.pi_map_pi (fun _ ↦ positionPath_measurable.aemeasurable)
  have hm : Measurable (fun w : Fin N → Fin d → C(Icc 0 T, ℝ) ↦ fun i ↦ positionPath (w i)) :=
    measurable_pi_lambda _ fun i ↦ positionPath_measurable.comp (measurable_pi_apply i)
  rw [← hp, Measure.map_map assemblePositionPaths_measurable hm]
  rfl

end SharpWasserstein.BrownianNoise

namespace SharpWasserstein

/-- Coordinate restriction of a genuine finite product probability measure. -/
theorem probability_pi_map_prefix {A : Type*} [MeasurableSpace A]
    (ξ : Measure A) [IsProbabilityMeasure ξ] {m N : ℕ} (hm : m ≤ N) :
    (Measure.pi fun _ : Fin N ↦ ξ).map (fun w : Fin N → A ↦ fun i : Fin m ↦ w (Fin.castLE hm i)) =
      Measure.pi fun _ : Fin m ↦ ξ := by
  have hi := (iIndepFun_pi (μ := fun _ : Fin N ↦ ξ) (X := fun _ ↦ id)
    (fun _ ↦ measurable_id.aemeasurable)).precomp (Fin.castLE_injective hm)
  have h := hi.map_fun_eq_pi_map (fun i ↦ (measurable_pi_apply (Fin.castLE hm i)).aemeasurable)
  have he (i : Fin m) : (Measure.pi fun _ : Fin N ↦ ξ).map
      (fun w : Fin N → A ↦ w (Fin.castLE hm i)) = ξ :=
    (measurePreserving_eval (fun _ : Fin N ↦ ξ) (Fin.castLE hm i)).map_eq
  simpa only [Function.comp_def, id_eq, he] using h

end SharpWasserstein
