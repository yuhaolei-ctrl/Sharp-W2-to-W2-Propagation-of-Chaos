import SharpWasserstein.BrownianEntropyTransport
import SharpWasserstein.BrownianProductNoise
import SharpWasserstein.DecoupledMarginal
import SharpWasserstein.FlattenedEuclidean

/-! The actual Brownian configuration flow for a coordinatewise drift is the
concrete decoupled flow, with exact tensor and marginal identities. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
namespace SharpWasserstein.DecoupledFlow

variable {d : ℕ} {v : ℝ → Position d → Position d} {M K L : ℝ≥0}

def liftDrift (N : ℕ) (v : ℝ → Position d → Position d) (t : ℝ)
    (x : Configuration d N) : Configuration d N := fun i ↦ v t (x i)

theorem liftDrift_continuous (N : ℕ) (hv : Continuous (Function.uncurry v)) :
    Continuous (Function.uncurry (liftDrift N v)) :=
  continuous_pi fun i ↦ hv.comp (continuous_fst.prodMk ((continuous_apply i).comp continuous_snd))

theorem liftDrift_bound (N : ℕ) (hb : ∀ t x, ‖v t x‖ ≤ M) :
    ∀ t x, ‖liftDrift N v t x‖ ≤ M := by
  intro t x
  exact (pi_norm_le_iff_of_nonneg M.coe_nonneg).mpr fun i ↦ hb t (x i)

theorem liftDrift_lipschitz (N : ℕ) (hl : ∀ t, LipschitzWith K (v t)) :
    ∀ t, LipschitzWith K (liftDrift N v t) := by
  intro t
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg K.coe_nonneg (norm_nonneg _))).mpr
  intro i
  have h := (hl t).dist_le_mul (x i) (y i)
  simp only [dist_eq_norm] at h
  exact h.trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm (x-y) i) K.coe_nonneg)

/-- Coordinatewise Euclidean Lipschitz constants do not grow with the level. -/
theorem liftDrift_quadratic (N : ℕ)
    (he : ∀ t, LipschitzWith L (GaussianBridge.euclideanDrift v t)) (t : ℝ)
    (x y : Configuration d N) :
    productCost (liftDrift N v t x) (liftDrift N v t y) ≤ (L : ℝ)^2 * productCost x y := by
  unfold productCost
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h := (he t).dist_le_mul (WithLp.toLp 2 (x i)) (WithLp.toLp 2 (y i))
  simp only [dist_eq_norm] at h
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg L.coe_nonneg (norm_nonneg _))).mpr h
  simpa only [mul_pow, EuclideanSpace.real_norm_sq_eq, PiLp.sub_apply,
    GaussianBridge.euclideanDrift, liftDrift] using hs

theorem liftDrift_euclidean_lipschitz (N : ℕ)
    (he : ∀ t, LipschitzWith L (GaussianBridge.euclideanDrift v t)) :
    ∀ t, LipschitzWith L (GaussianBridge.euclideanDrift (flattenedDrift (liftDrift N v)) t) := by
  intro t
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg L.coe_nonneg (norm_nonneg _))).mp
  let x₀ := (configurationFlatten d N).symm (WithLp.ofLp x)
  let y₀ := (configurationFlatten d N).symm (WithLp.ofLp y)
  have hcost : productCost x₀ y₀ = ‖x-y‖^2 := by
    rw [← configurationFlatten_displacementSq]
    simp only [x₀, y₀, MeasurableEquiv.apply_symm_apply, EuclideanSpace.real_norm_sq_eq, PiLp.sub_apply]
  have hdiff : ‖GaussianBridge.euclideanDrift (flattenedDrift (liftDrift N v)) t x -
      GaussianBridge.euclideanDrift (flattenedDrift (liftDrift N v)) t y‖^2 =
      productCost (liftDrift N v t x₀) (liftDrift N v t y₀) := by
    rw [← configurationFlatten_displacementSq, EuclideanSpace.real_norm_sq_eq]
    rfl
  rw [hdiff, mul_pow, ← hcost]
  exact liftDrift_quadratic N he t x₀ y₀

/-- Exact coordinate identity for the explicit Euler approximation. -/
theorem liftDrift_nodes_coordinate {N : ℕ} (x : Configuration d N)
    (w : ℝ → Configuration d N) (δ : ℝ) (n : ℕ) (i : Fin N) :
    Euler.nodes (liftDrift N v) x w δ n i = Euler.nodes v (x i) (fun t ↦ w t i) δ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Euler.nodes, liftDrift, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, ih]

/-- Actual terminal integral-equation solutions agree coordinate by coordinate;
this follows from the proved Euler limits, not an assumed flow factorization. -/
theorem liftDrift_flow_coordinate {N : ℕ} {T : ℝ}
    (hv : Continuous (Function.uncurry v)) (hb : ∀ t x, ‖v t x‖ ≤ M)
    (hl : ∀ t, LipschitzWith K (v t)) (hT : 0 < T)
    (x : Configuration d N) (w : Fin N → C(Icc 0 T, Position d)) (i : Fin N) :
    BoundedFlow.flow (liftDrift_continuous N hv) (liftDrift_bound N hb) (liftDrift_lipschitz N hl)
      hT.le x (BrownianNoise.assemblePositionPaths w) T i = BoundedFlow.flow hv hb hl hT.le (x i) (w i) T := by
  have hfull := Euler.trajectory_endpoint_tendsto (BoundedFlow.flow_trajectory
    (liftDrift_continuous N hv) (liftDrift_bound N hb) (liftDrift_lipschitz N hl)
    hT.le x (BrownianNoise.assemblePositionPaths w)) (liftDrift_lipschitz N hl) hT
  have hc := (continuous_apply i).continuousAt.tendsto.comp hfull
  have hsingle := Euler.trajectory_endpoint_tendsto (BoundedFlow.flow_trajectory hv hb hl hT.le (x i) (w i)) hl hT
  have heq : (fun n : ℕ ↦ Euler.nodes (liftDrift N v) x
      (BoundedFlow.noiseExtension hT.le (BrownianNoise.assemblePositionPaths w)) (T/(n+1)) (n+1) i) =
      (fun n : ℕ ↦ Euler.nodes v (x i) (BoundedFlow.noiseExtension hT.le (w i)) (T/(n+1)) (n+1)) := by
    funext n
    exact liftDrift_nodes_coordinate x _ _ _ i
  simp only [Function.comp_def] at hc
  rw [heq] at hc
  exact tendsto_nhds_unique hc hsingle

/-- The actual constructed configuration Brownian flow is exactly the decoupled
independent one-particle flow used in the entropy source regularization. -/
theorem brownian_flowLaw_eq {N : ℕ} {T : ℝ}
    (hv : Continuous (Function.uncurry v)) (hb : ∀ t x, ‖v t x‖ ≤ M)
    (hl : ∀ t, LipschitzWith K (v t)) (hT : 0 < T)
    (P : Measure (Configuration d N)) [IsProbabilityMeasure P] :
    (BrownianEntropy.flowLaw P (liftDrift_continuous N hv) (liftDrift_bound N hb)
      (liftDrift_lipschitz N hl) hT.le : Measure (Configuration d N)) =
      law hv hb hl hT.le P (BrownianNoise.positionLaw d T) T := by
  change (P.prod (BrownianNoise.configurationLaw d N T)).map
    (fun p ↦ BoundedFlow.flow (liftDrift_continuous N hv) (liftDrift_bound N hb)
      (liftDrift_lipschitz N hl) hT.le p.1 p.2 T) = _
  rw [BrownianNoise.configurationLaw_eq_position_product]
  have hm : (P.prod (Measure.pi fun _ : Fin N ↦ BrownianNoise.positionLaw d T)).map
      (Prod.map id BrownianNoise.assemblePositionPaths) =
      P.prod ((Measure.pi fun _ : Fin N ↦ BrownianNoise.positionLaw d T).map BrownianNoise.assemblePositionPaths) := by
    simpa using (Measure.map_prod_map P _ measurable_id BrownianNoise.assemblePositionPaths_measurable).symm
  rw [← hm, Measure.map_map
    (BoundedFlow.flow_continuous (liftDrift_continuous N hv) (liftDrift_bound N hb)
      (liftDrift_lipschitz N hl) hT.le ⟨hT.le, le_rfl⟩).measurable
    (measurable_id.prodMap BrownianNoise.assemblePositionPaths_measurable)]
  unfold law randomMapLaw
  congr 1
  funext p
  funext i
  exact liftDrift_flow_coordinate hv hb hl hT p.1 p.2 i

end SharpWasserstein.DecoupledFlow
