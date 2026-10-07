module

public import SharpWasserstein.Compat
public import SharpWasserstein.FrozenGaussianStep

@[expose] public section

/-! The frozen expectation is the integral against the actual Gaussian vector
transition measure, with exactly covariance 2t times the identity. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators Interval
namespace SharpWasserstein.FrozenGaussian
open GaussianSharpness

theorem flatten_noiseMap {d N : ℕ} (ω : Fin (N*d+1) → ℝ) :
    configurationFlatten d N (noiseMap d N ω) = fun k : Fin (N*d) => ω k.succ := by
  funext k
  rw [configurationFlatten_apply]
  simp only [noiseMap_apply, Prod.mk.eta, Equiv.apply_symm_apply]

theorem label_flat_hasLaw {d N : ℕ} (x u : Configuration d N) (α : ℝ) :
    HasLaw (fun ω => configurationFlatten d N (label x u α ω))
      (gaussianVectorLaw (configurationFlatten d N (x+(α^2/2)•u)) (NNReal.mk (α^2) (sq_nonneg _)))
      (standardLabels (N*d+1)) := by
  let m := configurationFlatten d N (x+(α^2/2)•u)
  have hind : iIndepFun (fun k : Fin (N*d) => fun ω : Fin (N*d+1) → ℝ => ω k.succ)
      (standardLabels (N*d+1)) :=
    (iIndepFun_pi (μ := fun _ : Fin (N*d+1) => gaussianReal 0 1)
      (X := fun _ => id) (fun _ => measurable_id.aemeasurable)).precomp (Fin.succ_injective (N*d))
  have hi : ∀ k : Fin (N*d), HasLaw (fun ω : Fin (N*d+1) → ℝ => m k + α*ω k.succ)
      (gaussianReal (m k) (NNReal.mk (α^2) (sq_nonneg _))) (standardLabels (N*d+1)) := by
    intro k
    have h := gaussianReal_const_add (gaussianReal_const_mul
      (measurePreserving_eval (fun _ : Fin (N*d+1) => gaussianReal 0 1) k.succ).hasLaw α) (m k)
    simpa only [mul_zero, zero_add, mul_one, Function.eval, standardLabels] using h
  have hp := (hind.comp (fun k z => m k+α*z) (fun _ => by fun_prop)).hasLaw_pi hi
  convert hp using 1
  · funext ω k
    simp only [m, label, configurationFlatten_add, configurationFlatten_smul, flatten_noiseMap,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  · rfl

theorem label_hasLaw {d N : ℕ} (x u : Configuration d N) (α : ℝ) :
    HasLaw (label x u α)
      ((gaussianVectorLaw (configurationFlatten d N (x+(α^2/2)•u)) (NNReal.mk (α^2) (sq_nonneg _))).map
        (configurationFlatten d N).symm) (standardLabels (N*d+1)) := by
  have hm : HasLaw (configurationFlatten d N).symm
      ((gaussianVectorLaw (configurationFlatten d N (x+(α^2/2)•u)) (NNReal.mk (α^2) (sq_nonneg _))).map
        (configurationFlatten d N).symm)
      (gaussianVectorLaw (configurationFlatten d N (x+(α^2/2)•u)) (NNReal.mk (α^2) (sq_nonneg _))) :=
    ⟨(configurationFlatten d N).symm.measurable.aemeasurable, rfl⟩
  simpa only [Function.comp_def, MeasurableEquiv.symm_apply_apply] using hm.comp (label_flat_hasLaw x u α)

def transitionLaw {d N : ℕ} (x u : Configuration d N) (t : ℝ≥0) : Measure (Configuration d N) :=
  (gaussianVectorLaw (configurationFlatten d N (x+(t : ℝ)•u)) (2*t)).map (configurationFlatten d N).symm

instance transitionLaw_probability {d N : ℕ} (x u : Configuration d N) (t : ℝ≥0) :
    IsProbabilityMeasure (transitionLaw x u t) :=
  Measure.isProbabilityMeasure_map (configurationFlatten d N).symm.measurable.aemeasurable

theorem label_time_hasLaw {d N : ℕ} (x u : Configuration d N) (t : ℝ≥0) :
    HasLaw (label x u (Real.sqrt (2*t))) (transitionLaw x u t) (standardLabels (N*d+1)) := by
  have hsq : (Real.sqrt (2*(t : ℝ)))^2 = 2*t := Real.sq_sqrt (by positivity)
  have hv : NNReal.mk ((Real.sqrt (2*(t : ℝ)))^2) (sq_nonneg _) = 2*t := by
    apply NNReal.eq
    exact hsq
  have hc : (Real.sqrt (2*(t : ℝ)))^2/2 = t := by rw [hsq]; ring
  simpa only [transitionLaw, hv, hc] using label_hasLaw x u (Real.sqrt (2*t))

theorem integral_transitionLaw {d N : ℕ} {φ : Configuration d N → ℝ} (hφ : Continuous φ)
    (x u : Configuration d N) (t : ℝ≥0) :
    (∫ y, φ y ∂transitionLaw x u t) = timeExpectation φ x u t := by
  rw [← (label_time_hasLaw x u t).map_eq,
    integral_map (label_continuous x u _).measurable.aemeasurable hφ.aestronglyMeasurable]
  rfl

end SharpWasserstein.FrozenGaussian
