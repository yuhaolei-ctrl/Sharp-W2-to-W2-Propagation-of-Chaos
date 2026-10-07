module

public import SharpWasserstein.Compat
public import SharpWasserstein.FlowDependence
public import Mathlib.Topology.ContinuousMap.Compact

@[expose] public section

/-! A measurable solution map is constructed, rather than assumed, for every
bounded globally Lipschitz drift and every continuous additive input. -/

noncomputable section
open Set MeasureTheory
open scoped NNReal

namespace SharpWasserstein.BoundedFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {v : ℝ → E → E} {M K : ℝ≥0}

/-- Extend a continuous input from its compact time interval by endpoint values. -/
def noiseExtension {T : ℝ} (hT : 0 ≤ T) (w : C(Icc 0 T, E)) (t : ℝ) : E :=
  w (projIcc 0 T hT t)

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem noiseExtension_continuous {T : ℝ} (hT : 0 ≤ T) (w : C(Icc 0 T, E)) :
    Continuous (noiseExtension hT w) := w.continuous.comp continuous_projIcc

/-- The selected function satisfies the actual integral equation; uniqueness
below removes dependence on the choice of the Picard solution. -/
def flow (hv : Continuous (Function.uncurry v))
    (hb : ∀ t x, ‖v t x‖ ≤ M) (hl : ∀ t, LipschitzWith K (v t))
    {T : ℝ} (hT : 0 ≤ T) (x : E) (w : C(Icc 0 T, E)) : ℝ → E :=
  Classical.choose (exists_finiteAdditiveTrajectory hv (noiseExtension_continuous hT w)
    hb hl x hT)

theorem flow_trajectory (hv : Continuous (Function.uncurry v))
    (hb : ∀ t x, ‖v t x‖ ≤ M) (hl : ∀ t, LipschitzWith K (v t))
    {T : ℝ} (hT : 0 ≤ T) (x : E) (w : C(Icc 0 T, E)) :
    FiniteAdditiveTrajectory v (noiseExtension hT w) x T (flow hv hb hl hT x w) :=
  Classical.choose_spec (exists_finiteAdditiveTrajectory hv (noiseExtension_continuous hT w)
    hb hl x hT)

/-- Quantitative continuous dependence on initial data and on the entire input. -/
theorem flow_difference_le (hv : Continuous (Function.uncurry v))
    (hb : ∀ t x, ‖v t x‖ ≤ M) (hl : ∀ t, LipschitzWith K (v t))
    {T : ℝ} (hT : 0 ≤ T) (x y : E) (w z : C(Icc 0 T, E))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖flow hv hb hl hT x w t - flow hv hb hl hT y z t‖ ≤
      (‖x - y‖ + ‖w - z‖) * Real.exp ((K : ℝ) * t) := by
  apply FiniteAdditiveTrajectory.forcing_stability (fun s _ => hl s)
    (noiseExtension_continuous hT w).continuousOn
    (noiseExtension_continuous hT z).continuousOn _
    (flow_trajectory hv hb hl hT x w) (flow_trajectory hv hb hl hT y z) ht
  intro s _
  exact (w - z).norm_coe_le_norm (projIcc 0 T hT s)

/-- Every fixed-time solution map is globally Lipschitz and hence measurable. -/
theorem flow_lipschitz (hv : Continuous (Function.uncurry v))
    (hb : ∀ t x, ‖v t x‖ ≤ M) (hl : ∀ t, LipschitzWith K (v t))
    {T : ℝ} (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    LipschitzWith ⟨2 * Real.exp ((K : ℝ) * t), by positivity⟩
      (fun p : E × C(Icc 0 T, E) => flow hv hb hl hT p.1 p.2 t) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  rw [dist_eq_norm]
  change ‖flow hv hb hl hT p.1 p.2 t - flow hv hb hl hT q.1 q.2 t‖ ≤
    (2 * Real.exp ((K : ℝ) * t)) * dist p q
  have h := flow_difference_le hv hb hl hT p.1 q.1 p.2 q.2 ht
  have hp : ‖p.1 - q.1‖ ≤ dist p q := by
    rw [← dist_eq_norm, Prod.dist_eq]
    exact le_max_left _ _
  have hq : ‖p.2 - q.2‖ ≤ dist p q := by
    rw [← dist_eq_norm, Prod.dist_eq]
    exact le_max_right _ _
  calc
    _ ≤ (‖p.1 - q.1‖ + ‖p.2 - q.2‖) * Real.exp ((K : ℝ) * t) := h
    _ ≤ (2 * dist p q) * Real.exp ((K : ℝ) * t) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by ring

theorem flow_continuous (hv : Continuous (Function.uncurry v))
    (hb : ∀ t x, ‖v t x‖ ≤ M) (hl : ∀ t, LipschitzWith K (v t))
    {T : ℝ} (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Continuous (fun p : E × C(Icc 0 T, E) => flow hv hb hl hT p.1 p.2 t) :=
  (flow_lipschitz hv hb hl hT ht).continuous

/-- Continuity is joint in the initial point, input path, and time. -/
theorem flow_joint_continuous (hv : Continuous (Function.uncurry v))
    (hb : ∀ t x, ‖v t x‖ ≤ M) (hl : ∀ t, LipschitzWith K (v t))
    {T : ℝ} (hT : 0 ≤ T) :
    Continuous (fun p : (E × C(Icc 0 T, E)) × Icc 0 T =>
      flow hv hb hl hT p.1.1 p.1.2 p.2) := by
  apply continuous_prod_of_continuous_lipschitzWith _
    ⟨2 * Real.exp ((K : ℝ) * T), by positivity⟩
  · intro p
    exact (flow_trajectory hv hb hl hT p.1 p.2).continuous.restrict
  · intro t
    apply (flow_lipschitz hv hb hl hT t.property).weaken
    change 2 * Real.exp ((K : ℝ) * (t : ℝ)) ≤ 2 * Real.exp ((K : ℝ) * T)
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left t.property.2 K.coe_nonneg)) (by positivity)

/-- Uniqueness against every solution of the same integral equation. -/
theorem flow_eq_of_trajectory (hv : Continuous (Function.uncurry v))
    (hb : ∀ t x, ‖v t x‖ ≤ M) (hl : ∀ t, LipschitzWith K (v t))
    {T : ℝ} (hT : 0 ≤ T) (x : E) (w : C(Icc 0 T, E))
    {X : ℝ → E} (hX : FiniteAdditiveTrajectory v (noiseExtension hT w) x T X)
    {t : ℝ} (ht : t ∈ Icc 0 T) : flow hv hb hl hT x w t = X t := by
  have h := (flow_trajectory hv hb hl hT x w).stability
    (fun s _ => hl s) hX ht
  simpa only [sub_self, norm_zero, zero_mul, norm_le_zero_iff, sub_eq_zero] using h

end SharpWasserstein.BoundedFlow
