import SharpWasserstein.EulerBrownianLaw

/-! Actual Euler history laws for every prefix of a fixed time grid. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace SharpWasserstein.BrownianNoise

def linearGrid {T δ : ℝ} (_hT : 0 ≤ T) (hδ : 0 ≤ δ) (m : ℕ) (hm : (m : ℝ)*δ ≤ T)
    (j : Fin (m+1)) : Icc 0 T :=
  ⟨(j : ℝ)*δ, mul_nonneg (by positivity) hδ,
    (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_of_lt_succ j.isLt) hδ).trans hm⟩

theorem linearGrid_monotone {T δ : ℝ} (hT : 0 ≤ T) (hδ : 0 ≤ δ) (m : ℕ) (hm : (m : ℝ)*δ ≤ T) :
    Monotone (linearGrid hT hδ m hm) := by
  intro i j hij
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hδ

theorem linearGrid_variance {T δ : ℝ} (hT : 0 ≤ T) (hδ : 0 ≤ δ) (m : ℕ) (hm : (m : ℝ)*δ ≤ T)
    (j : Fin m) :
    2*nndist (linearGrid hT hδ m hm j.succ : ℝ) (linearGrid hT hδ m hm j.castSucc : ℝ) =
      NNReal.mk (2*δ) (by positivity) := by
  apply NNReal.eq
  simp only [NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_mk, coe_nndist, Real.dist_eq, linearGrid,
    Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
  rw [show ((j : ℝ)+1)*δ-(j : ℝ)*δ = δ by ring, abs_of_nonneg hδ]

theorem flattenedGridIncrement_linear {T δ : ℝ} (hT : 0 ≤ T) (hδ : 0 ≤ δ)
    (m : ℕ) (hm : (m : ℝ)*δ ≤ T) {d N : ℕ} (w : C(Icc 0 T, Configuration d N)) :
    flattenedGridIncrement (linearGrid hT hδ m hm) w = fun j : Fin m =>
      configurationFlatten d N (BoundedFlow.noiseExtension hT w ((j+1)*δ))-
      configurationFlatten d N (BoundedFlow.noiseExtension hT w (j*δ)) := by
  funext j
  unfold flattenedGridIncrement BoundedFlow.noiseExtension
  have hs := projIcc_of_mem hT (linearGrid hT hδ m hm j.succ).property
  have hc := projIcc_of_mem hT (linearGrid hT hδ m hm j.castSucc).property
  simp only [linearGrid, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one] at hs hc ⊢
  rw [hs,hc]
  exact configurationFlatten_sub _ _

end SharpWasserstein.BrownianNoise
namespace SharpWasserstein

theorem configurationEuler_simulator_grid_eq_nodes {A : Type*} [MeasurableSpace A] {d N : ℕ}
    {T δ : ℝ} (hT : 0 ≤ T) (hδ : 0 ≤ δ) (m : ℕ) (hm : (m : ℝ)*δ ≤ T)
    (initial : A → Configuration d N) (b : A → ℝ → Configuration d N → Configuration d N)
    (z : A) (w : C(Icc 0 T, Configuration d N)) (hw : w ⟨0,le_rfl,hT⟩ = 0) :
    configurationEulerObservation initial m
      (gaussianHistorySimulator (configurationEulerMean initial b δ) m
        ((z, fun i => Fin.elim0 i), BrownianNoise.flattenedGridIncrement (BrownianNoise.linearGrid hT hδ m hm) w)) =
      Euler.nodes (b z) (initial z) (BoundedFlow.noiseExtension hT w) δ m := by
  apply (configurationFlatten d N).injective
  rw [configurationEulerObservation, MeasurableEquiv.apply_symm_apply,
    BrownianNoise.flattenedGridIncrement_linear]
  have hw0 : configurationFlatten d N (BoundedFlow.noiseExtension hT w 0) = 0 := by
    unfold BoundedFlow.noiseExtension
    rw [projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩), hw, configurationFlatten_zero]
  exact (gaussianHistorySimulator_label_current_eq_nodes
    (fun z => configurationFlatten d N (initial z)) (fun z => flattenedDrift (b z)) δ
    (fun t => configurationFlatten d N (BoundedFlow.noiseExtension hT w t)) hw0
    (z, fun i => Fin.elim0 i) m).trans
    (configurationFlatten_nodes (b z) (initial z) (BoundedFlow.noiseExtension hT w) δ m).symm

/-- Every intermediate Euler node has the genuine corresponding Gaussian
history marginal under the same fixed Brownian horizon. -/
theorem configurationEuler_brownian_grid_hasLaw {A : Type*} [MeasurableSpace A] {d N : ℕ}
    {T δ : ℝ} (hT : 0 ≤ T) (hδ : 0 ≤ δ) (m : ℕ) (hm : (m : ℝ)*δ ≤ T)
    (μ : Measure A) [IsProbabilityMeasure μ]
    (initial : A → Configuration d N) (hi : Measurable initial)
    (b : A → ℝ → Configuration d N → Configuration d N)
    (hb : ∀ t, Measurable (fun p : A × Configuration d N => b p.1 t p.2)) :
    HasLaw (fun p : A × C(Icc 0 T, Configuration d N) =>
      Euler.nodes (b p.1) (initial p.1) (BoundedFlow.noiseExtension hT p.2) δ m)
      ((gaussianHistoryLaw (gaussianInitialHistory (N*d) μ) (configurationEulerMean initial b δ)
        (configurationEulerMean_measurable initial hi b hb δ)
        (fun _ => NNReal.mk (2*δ) (by positivity)) m).map (configurationEulerObservation initial m))
      (μ.prod (BrownianNoise.configurationLaw d N T)) := by
  have hm0 : MeasurePreserving (fun z : A => (z, fun i : Fin 0 => (Fin.elim0 i : Position (N*d))))
      μ (gaussianInitialHistory (N*d) μ) := ⟨by fun_prop, rfl⟩
  have hinput := hm0.prod (MeasurePreserving.id (BrownianNoise.configurationLaw d N T))
  have hsim := (BrownianNoise.brownian_gaussianHistory_hasLaw
    (BrownianNoise.linearGrid hT hδ m hm) (BrownianNoise.linearGrid_monotone hT hδ m hm)
    (gaussianInitialHistory (N*d) μ) (configurationEulerMean initial b δ)
    (configurationEulerMean_measurable initial hi b hb δ)
    (fun _ => NNReal.mk (2*δ) (by positivity))
    (fun j => (BrownianNoise.linearGrid_variance hT hδ m hm j).symm)).comp hinput.hasLaw
  have hout : HasLaw (configurationEulerObservation initial m)
      ((gaussianHistoryLaw (gaussianInitialHistory (N*d) μ) (configurationEulerMean initial b δ)
        (configurationEulerMean_measurable initial hi b hb δ)
        (fun _ => NNReal.mk (2*δ) (by positivity)) m).map (configurationEulerObservation initial m))
      (gaussianHistoryLaw (gaussianInitialHistory (N*d) μ) (configurationEulerMean initial b δ)
        (configurationEulerMean_measurable initial hi b hb δ)
        (fun _ => NNReal.mk (2*δ) (by positivity)) m) :=
    ⟨(configurationEulerObservation_measurable initial hi m).aemeasurable, rfl⟩
  apply (hout.comp hsim).congr
  have hzero := (measurePreserving_snd (μ := μ) (ν := BrownianNoise.configurationLaw d N T)).quasiMeasurePreserving.ae
    (BrownianNoise.configurationLaw_zero_ae hT (d := d) (N := N))
  filter_upwards [hzero] with p hp
  exact (configurationEuler_simulator_grid_eq_nodes hT hδ m hm initial b p.1 p.2 hp).symm

end SharpWasserstein
