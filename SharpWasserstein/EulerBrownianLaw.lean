import SharpWasserstein.EulerGaussianHistory
import SharpWasserstein.EulerLaw
import SharpWasserstein.GaussianHistoryMarginals

/-! The Euler endpoints under genuine independent initial/Brownian inputs are
observations of the constructed Gaussian transition histories. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace SharpWasserstein

@[simp] theorem configurationFlatten_add {d N : ℕ} (x y : Configuration d N) :
    configurationFlatten d N (x+y) = configurationFlatten d N x + configurationFlatten d N y := by
  ext k
  simp [configurationFlatten, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
@[simp] theorem configurationFlatten_sub {d N : ℕ} (x y : Configuration d N) :
    configurationFlatten d N (x-y) = configurationFlatten d N x - configurationFlatten d N y := by
  ext k
  simp [configurationFlatten, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
@[simp] theorem configurationFlatten_smul {d N : ℕ} (c : ℝ) (x : Configuration d N) :
    configurationFlatten d N (c • x) = c • configurationFlatten d N x := by
  ext k
  simp [configurationFlatten, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
@[simp] theorem configurationFlatten_zero {d N : ℕ} :
    configurationFlatten d N (0 : Configuration d N) = 0 := by
  ext k
  simp [configurationFlatten, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]

def flattenedDrift {d N : ℕ} (b : ℝ → Configuration d N → Configuration d N)
    (t : ℝ) (z : Position (N*d)) : Position (N*d) :=
  configurationFlatten d N (b t ((configurationFlatten d N).symm z))

theorem flattenedDrift_measurable {d N : ℕ}
    (b : ℝ → Configuration d N → Configuration d N) (hb : ∀ t, Measurable (b t)) (t : ℝ) :
    Measurable (flattenedDrift b t) :=
  (configurationFlatten d N).measurable.comp ((hb t).comp (configurationFlatten d N).symm.measurable)

theorem configurationFlatten_nodes {d N : ℕ}
    (b : ℝ → Configuration d N → Configuration d N) (x : Configuration d N)
    (w : ℝ → Configuration d N) (δ : ℝ) (n : ℕ) :
    configurationFlatten d N (Euler.nodes b x w δ n) =
      Euler.nodes (flattenedDrift b) (configurationFlatten d N x)
        (fun t => configurationFlatten d N (w t)) δ n := by
  induction n with
  | zero => exact configurationFlatten_add _ _
  | succ n ih =>
    simp only [Euler.nodes, configurationFlatten_add, configurationFlatten_smul,
      configurationFlatten_sub, flattenedDrift]
    rw [← ih, MeasurableEquiv.symm_apply_apply]

namespace BrownianNoise

def uniformGrid {T : ℝ} (hT : 0 ≤ T) (n : ℕ) (j : Fin (n+2)) : Icc 0 T :=
  ⟨(j : ℝ) * (T/(n+1)), by
    have hn : (0 : ℝ) < n+1 := by positivity
    have hδ : 0 ≤ T/(n+1) := div_nonneg hT hn.le
    have hj : (j : ℝ) ≤ n+1 := by exact_mod_cast Nat.le_of_lt_succ j.isLt
    constructor
    · positivity
    · calc (j : ℝ) * (T/(n+1)) ≤ (n+1) * (T/(n+1)) := mul_le_mul_of_nonneg_right hj hδ
           _ = T := mul_div_cancel₀ T (ne_of_gt hn)⟩

theorem uniformGrid_monotone {T : ℝ} (hT : 0 ≤ T) (n : ℕ) : Monotone (uniformGrid hT n) := by
  intro i j hij
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) (div_nonneg hT (by positivity))

theorem uniformGrid_variance {T : ℝ} (hT : 0 ≤ T) (n : ℕ) (j : Fin (n+1)) :
    2 * nndist (uniformGrid hT n j.succ : ℝ) (uniformGrid hT n j.castSucc : ℝ) =
      ⟨2*(T/(n+1)), by positivity⟩ := by
  apply NNReal.eq
  simp only [NNReal.coe_mul, NNReal.coe_ofNat, coe_nndist, Real.dist_eq, uniformGrid,
    Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
  rw [show ((j : ℝ)+1)*(T/(n+1)) - (j : ℝ)*(T/(n+1)) = T/(n+1) by ring,
    abs_of_nonneg (div_nonneg hT (by positivity))]
  rfl

theorem flattenedGridIncrement_uniform {T : ℝ} (hT : 0 ≤ T) (n : ℕ) {d N : ℕ}
    (w : C(Icc 0 T, Configuration d N)) :
    flattenedGridIncrement (uniformGrid hT n) w =
      fun j : Fin (n+1) =>
        configurationFlatten d N (BoundedFlow.noiseExtension hT w ((j+1)*(T/(n+1)))) -
        configurationFlatten d N (BoundedFlow.noiseExtension hT w (j*(T/(n+1)))) := by
  funext j
  unfold flattenedGridIncrement BoundedFlow.noiseExtension
  have hs := projIcc_of_mem hT (uniformGrid hT n j.succ).property
  have hc := projIcc_of_mem hT (uniformGrid hT n j.castSucc).property
  simp only [uniformGrid, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one] at hs hc ⊢
  rw [hs, hc]
  exact configurationFlatten_sub _ _

end BrownianNoise

def configurationEulerMean {A : Type*} {d N : ℕ} (initial : A → Configuration d N)
    (b : A → ℝ → Configuration d N → Configuration d N) (δ : ℝ) :
    (j : ℕ) → GaussianHistory A (N*d) j → Position (N*d) :=
  eulerLabelHistoryMean (fun z => configurationFlatten d N (initial z))
    (fun z => flattenedDrift (b z)) δ

def configurationEulerObservation {A : Type*} {d N : ℕ} (initial : A → Configuration d N)
    (j : ℕ) (h : GaussianHistory A (N*d) j) : Configuration d N :=
  (configurationFlatten d N).symm
    (gaussianHistoryCurrent (fun z => configurationFlatten d N (initial z)) j h)

theorem configurationEulerMean_measurable {A : Type*} [MeasurableSpace A] {d N : ℕ}
    (initial : A → Configuration d N) (hi : Measurable initial)
    (b : A → ℝ → Configuration d N → Configuration d N)
    (hb : ∀ t, Measurable (fun p : A × Configuration d N => b p.1 t p.2))
    (δ : ℝ) (j : ℕ) : Measurable (configurationEulerMean initial b δ j) := by
  apply eulerLabelHistoryMean_measurable _ ((configurationFlatten d N).measurable.comp hi)
  intro t
  exact (configurationFlatten d N).measurable.comp ((hb t).comp
    (measurable_fst.prodMk ((configurationFlatten d N).symm.measurable.comp measurable_snd)))

theorem configurationEulerObservation_measurable {A : Type*} [MeasurableSpace A] {d N : ℕ}
    (initial : A → Configuration d N) (hi : Measurable initial) (j : ℕ) :
    Measurable (configurationEulerObservation initial j) :=
  (configurationFlatten d N).symm.measurable.comp
    (gaussianHistoryCurrent_measurable _ ((configurationFlatten d N).measurable.comp hi) j)

/-- Exact pathwise endpoint identity on paths starting at zero. -/
theorem configurationEuler_simulator_eq_nodes {A : Type*} [MeasurableSpace A] {d N : ℕ}
    {T : ℝ} (hT : 0 ≤ T) (initial : A → Configuration d N)
    (b : A → ℝ → Configuration d N → Configuration d N)
    (z : A) (w : C(Icc 0 T, Configuration d N)) (hw : w ⟨0,le_rfl,hT⟩ = 0) (n : ℕ) :
    configurationEulerObservation initial (n+1)
      (gaussianHistorySimulator (configurationEulerMean initial b (T/(n+1))) (n+1)
        ((z, fun i => Fin.elim0 i), BrownianNoise.flattenedGridIncrement (BrownianNoise.uniformGrid hT n) w)) =
      Euler.nodes (b z) (initial z) (BoundedFlow.noiseExtension hT w) (T/(n+1)) (n+1) := by
  apply (configurationFlatten d N).injective
  rw [configurationEulerObservation, MeasurableEquiv.apply_symm_apply,
    BrownianNoise.flattenedGridIncrement_uniform]
  have hw0 : configurationFlatten d N (BoundedFlow.noiseExtension hT w 0) = 0 := by
    unfold BoundedFlow.noiseExtension
    rw [projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩), hw, configurationFlatten_zero]
  exact (gaussianHistorySimulator_label_current_eq_nodes
    (fun z => configurationFlatten d N (initial z)) (fun z => flattenedDrift (b z)) (T/(n+1))
    (fun t => configurationFlatten d N (BoundedFlow.noiseExtension hT w t)) hw0
    (z, fun i => Fin.elim0 i) (n+1)).trans
    (configurationFlatten_nodes (b z) (initial z) (BoundedFlow.noiseExtension hT w) (T/(n+1)) (n+1)).symm

/-- Actual independently initialized configuration Brownian Euler endpoints are
observations of Gaussian transition histories. The drift may depend on retained
initial coupling labels. The Brownian transition law is derived, not assumed. -/
theorem configurationEuler_brownian_hasLaw {A : Type*} [MeasurableSpace A] {d N : ℕ}
    {T : ℝ} (hT : 0 ≤ T) (μ : Measure A) [IsProbabilityMeasure μ]
    (initial : A → Configuration d N) (hi : Measurable initial)
    (b : A → ℝ → Configuration d N → Configuration d N)
    (hb : ∀ t, Measurable (fun p : A × Configuration d N => b p.1 t p.2)) (n : ℕ) :
    HasLaw (fun p : A × C(Icc 0 T, Configuration d N) =>
      Euler.nodes (b p.1) (initial p.1) (BoundedFlow.noiseExtension hT p.2) (T/(n+1)) (n+1))
      ((gaussianHistoryLaw (gaussianInitialHistory (N*d) μ)
        (configurationEulerMean initial b (T/(n+1)))
        (configurationEulerMean_measurable initial hi b hb (T/(n+1)))
        (fun _ => ⟨2*(T/(n+1)), by positivity⟩) (n+1)).map (configurationEulerObservation initial (n+1)))
      (μ.prod (BrownianNoise.configurationLaw d N T)) := by
  have hm : MeasurePreserving (fun z : A => (z, fun i : Fin 0 => (Fin.elim0 i : Position (N*d))))
      μ (gaussianInitialHistory (N*d) μ) := ⟨by fun_prop, rfl⟩
  have hinput := hm.prod (MeasurePreserving.id (BrownianNoise.configurationLaw d N T))
  have hsim := (BrownianNoise.brownian_gaussianHistory_hasLaw
    (BrownianNoise.uniformGrid hT n) (BrownianNoise.uniformGrid_monotone hT n)
    (gaussianInitialHistory (N*d) μ) (configurationEulerMean initial b (T/(n+1)))
    (configurationEulerMean_measurable initial hi b hb (T/(n+1)))
    (fun _ => ⟨2*(T/(n+1)), by positivity⟩)
    (fun j => (BrownianNoise.uniformGrid_variance hT n j).symm)).comp hinput.hasLaw
  have hout : HasLaw (configurationEulerObservation initial (n+1))
      ((gaussianHistoryLaw (gaussianInitialHistory (N*d) μ)
        (configurationEulerMean initial b (T/(n+1)))
        (configurationEulerMean_measurable initial hi b hb (T/(n+1)))
        (fun _ => ⟨2*(T/(n+1)), by positivity⟩) (n+1)).map (configurationEulerObservation initial (n+1)))
      (gaussianHistoryLaw (gaussianInitialHistory (N*d) μ)
        (configurationEulerMean initial b (T/(n+1)))
        (configurationEulerMean_measurable initial hi b hb (T/(n+1)))
        (fun _ => ⟨2*(T/(n+1)), by positivity⟩) (n+1)) :=
    ⟨(configurationEulerObservation_measurable initial hi (n+1)).aemeasurable, rfl⟩
  apply (hout.comp hsim).congr
  have hzero := (measurePreserving_snd (μ := μ) (ν := BrownianNoise.configurationLaw d N T)).quasiMeasurePreserving.ae
    (BrownianNoise.configurationLaw_zero_ae hT (d := d) (N := N))
  filter_upwards [hzero] with p hp
  exact (configurationEuler_simulator_eq_nodes hT initial b p.1 p.2 hp n).symm

end SharpWasserstein
