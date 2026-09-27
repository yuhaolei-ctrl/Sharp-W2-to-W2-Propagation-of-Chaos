import SharpWasserstein.BrownianNoise
import SharpWasserstein.ParticleFlowPermutation
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-! Independent Brownian coordinates assembled into actual continuous
configuration paths. Their laws discharge the noise moment and permutation
hypotheses of the constructed interacting particle flow. -/

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SharpWasserstein.BrownianNoise

def coordinateLaw (d : ℕ) (T : ℝ) : Measure (Fin d → C(Icc 0 T, ℝ)) :=
  Measure.pi fun _ => scalarLaw T

instance coordinateLaw_probability (d : ℕ) (T : ℝ) : IsProbabilityMeasure (coordinateLaw d T) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : Fin d => scalarLaw T))

def pathLabels (d N : ℕ) (T : ℝ) : Measure (Fin N → Fin d → C(Icc 0 T, ℝ)) :=
  Measure.pi fun _ => coordinateLaw d T

instance pathLabels_probability (d N : ℕ) (T : ℝ) : IsProbabilityMeasure (pathLabels d N T) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : Fin N => coordinateLaw d T))

def configurationPath {d N : ℕ} {T : ℝ}
    (w : Fin N → Fin d → C(Icc 0 T, ℝ)) : C(Icc 0 T, Configuration d N) :=
  ⟨fun t i a => w i a t, continuous_pi fun i => continuous_pi fun a => (w i a).continuous⟩

theorem configurationPath_measurable {d N : ℕ} {T : ℝ} :
    Measurable (configurationPath (d := d) (N := N) (T := T)) := by
  apply (ContinuousMap.measurable_iff_eval _).mpr
  intro t
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro a
  exact (by fun_prop : Continuous (fun w : C(Icc 0 T, ℝ) => w t)).measurable.comp
    ((measurable_pi_apply a).comp (measurable_pi_apply i))

def configurationLaw (d N : ℕ) (T : ℝ) : Measure C(Icc 0 T, Configuration d N) :=
  Measure.map configurationPath (pathLabels d N T)

instance configurationLaw_probability (d N : ℕ) (T : ℝ) :
    IsProbabilityMeasure (configurationLaw d N T) :=
  Measure.isProbabilityMeasure_map configurationPath_measurable.aemeasurable

theorem labels_coordinate_preserving {d N : ℕ} {T : ℝ} (i : Fin N) (a : Fin d) :
    MeasurePreserving (fun w : Fin N → Fin d → C(Icc 0 T, ℝ) => w i a)
      (pathLabels d N T) (scalarLaw T) :=
  (measurePreserving_eval (fun _ : Fin d => scalarLaw T) a).comp
    (measurePreserving_eval (fun _ : Fin N => coordinateLaw d T) i)

theorem configurationLaw_coordinate_preserving {d N : ℕ} {T : ℝ}
    (t : Icc 0 T) (i : Fin N) (a : Fin d) :
    MeasurePreserving (fun w : C(Icc 0 T, Configuration d N) => w t i a)
      (configurationLaw d N T) (gaussianReal 0 (2 * ⟨t, t.property.1⟩)) := by
  have h := ((scalarLaw_hasLaw t).measurePreserving
    (by fun_prop : Continuous (fun w : C(Icc 0 T, ℝ) => w t)).measurable).comp
      (labels_coordinate_preserving i a)
  refine ⟨(by fun_prop : Continuous (fun w : C(Icc 0 T, Configuration d N) => w t i a)).measurable, ?_⟩
  rw [configurationLaw, Measure.map_map
    (by fun_prop : Continuous (fun w : C(Icc 0 T, Configuration d N) => w t i a)).measurable
    configurationPath_measurable]
  exact h.map_eq

theorem configurationLaw_memLp {d N : ℕ} {T : ℝ} (t : Icc 0 T)
    (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun w : C(Icc 0 T, Configuration d N) => w t) p (configurationLaw d N T) := by
  apply (memLp_map_measure_iff
    (by fun_prop : Continuous (fun w : C(Icc 0 T, Configuration d N) => w t)).measurable.aestronglyMeasurable
    configurationPath_measurable.aemeasurable).mpr
  apply memLp_pi_iff.mpr
  intro i
  apply memLp_pi_iff.mpr
  intro a
  exact (scalarLaw_memLp t p hp).comp_measurePreserving (labels_coordinate_preserving i a)

theorem configurationLaw_zero_ae {d N : ℕ} {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ w ∂configurationLaw d N T, w (⟨0, le_rfl, hT⟩ : Icc 0 T) = 0 := by
  apply (ae_map_iff configurationPath_measurable.aemeasurable
    ((by fun_prop : Continuous (fun w : C(Icc 0 T, Configuration d N) => w ⟨0, le_rfl, hT⟩)).measurable
      (measurableSet_singleton 0))).mpr
  have h : ∀ i : Fin N, ∀ a : Fin d, ∀ᵐ w ∂pathLabels d N T,
      w i a (⟨0, le_rfl, hT⟩ : Icc 0 T) = 0 := by
    intro i a
    exact (labels_coordinate_preserving i a).quasiMeasurePreserving.ae (scalarLaw_zero_ae hT)
  filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (h i))] with w hw
  exact funext fun i => funext fun a => hw i a

theorem configurationLaw_coordinate_secondMoment {d N : ℕ} {T : ℝ}
    (t : Icc 0 T) (i : Fin N) (a : Fin d) :
    (∫ w : C(Icc 0 T, Configuration d N), (w t i a) ^ 2 ∂configurationLaw d N T) =
      2 * (t : ℝ) := by
  rw [configurationLaw, integral_map configurationPath_measurable.aemeasurable
    (by fun_prop : Continuous (fun w : C(Icc 0 T, Configuration d N) => (w t i a)^2)).measurable.aestronglyMeasurable]
  have he := (labels_coordinate_preserving (T := T) i a).hasLaw.integral_comp
    (by fun_prop : Continuous (fun w : C(Icc 0 T, ℝ) => (w t)^2)).measurable.aestronglyMeasurable
  exact he.trans (scalarLaw_secondMoment t)

theorem configurationLaw_momentIntegral {d N : ℕ} {T : ℝ} (t : Icc 0 T) :
    (∫ w : C(Icc 0 T, Configuration d N), productCost (w t) 0 ∂configurationLaw d N T) =
      (N : ℝ) * d * (2 * (t : ℝ)) := by
  have hc (i : Fin N) (a : Fin d) :
      Integrable (fun w : C(Icc 0 T, Configuration d N) => (w t i a)^2)
        (configurationLaw d N T) :=
    (((configurationLaw_memLp t 2 (by norm_num)).eval i).eval a).integrable_sq
  simp only [productCost, Pi.zero_apply, sub_zero]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun a _ => hc i a))]
  simp_rw [integral_finsetSum _ (fun a _ => hc _ a), configurationLaw_coordinate_secondMoment]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The entire independent path law is invariant under particle permutations. -/
theorem configurationLaw_permutation {d N : ℕ} {T : ℝ} (e : Equiv.Perm (Fin N)) :
    Measure.map (permutedPath e) (configurationLaw d N T) = configurationLaw d N T := by
  let R : (Fin N → Fin d → C(Icc 0 T, ℝ)) → (Fin N → Fin d → C(Icc 0 T, ℝ)) :=
    fun w i => w (e i)
  have hR : Measurable R := measurable_pi_lambda _ fun i => measurable_pi_apply (e i)
  have hmap : Measure.map R (pathLabels d N T) = pathLabels d N T := by
    simpa [R, pathLabels, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft'] using
      (measurePreserving_piCongrLeft (fun _ : Fin N => coordinateLaw d T) e.symm).map_eq
  unfold configurationLaw
  rw [Measure.map_map (permutedPath_continuous e).measurable configurationPath_measurable]
  have heq : permutedPath e ∘ configurationPath = configurationPath ∘ R := rfl
  rw [heq, ← Measure.map_map configurationPath_measurable hR, hmap]

end SharpWasserstein.BrownianNoise
