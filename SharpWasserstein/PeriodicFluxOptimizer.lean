import SharpWasserstein.PeriodicGradientClosure

/-! Minimum-energy bound for the genuine periodic optimizer driven by an
actual L² flux. All pairings use the actual Hilbert integral and Euclidean norm. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace BoundedContinuousFunction
namespace SharpWasserstein.PeriodicFluxOptimizer
open PeriodicIntegrationByParts PeriodicFourierTests PeriodicGalerkin PeriodicGradientClosure
open WeightedTangent WeightedDensity
variable {n : ℕ} [MeasurableSpace (Point n)] [BorelSpace (Point n)]

/-- An actual flux determines a continuous functional on the genuine gradient closure. -/
def functional (q : Lp (Point n) 2 (cubePoint (n := n))) :
    gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ :=
  (innerSL ℝ q).comp (gradientClosure (cubePoint (n := n))).subtypeL

theorem functional_apply (q : Lp (Point n) 2 (cubePoint (n := n)))
    (u : gradientClosure (cubePoint (n := n))) :
    functional q u = ∫ y, ⟪q y,(u : Lp (Point n) 2 cubePoint) y⟫_ℝ ∂cubePoint := by
  change ⟪q,(u : Lp (Point n) 2 cubePoint)⟫_ℝ = _
  exact L2.inner_def q u

theorem integrable_fluxAction (ρ : Point n →ᵇ ℝ)
    (q : Lp (Point n) 2 (cubePoint (n := n))) {a : ℝ} (ha : 0 < a) (hp : ∀ y, a ≤ ρ y) :
    Integrable (fun y => ‖q y‖^2/ρ y) cubePoint := by
  have hq : Integrable (fun y => ‖q y‖^2) cubePoint :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp q).aestronglyMeasurable).mp (Lp.memLp q)
  have hm : AEStronglyMeasurable (fun y => ‖q y‖^2/ρ y) cubePoint := by
    have hm₀ := ((Lp.aestronglyMeasurable q).norm.pow 2).mul
      (ρ.continuous.inv₀ (fun y => (ha.trans_le (hp y)).ne')).aestronglyMeasurable
    exact hm₀.congr (Eventually.of_forall fun y => by
      simp only [Pi.mul_apply,Pi.pow_apply,Pi.inv_apply,div_eq_mul_inv])
  apply (hq.div_const a).mono' hm
  exact Eventually.of_forall fun y => by
    rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (sq_nonneg _) (ha.le.trans (hp y)))]
    exact div_le_div_of_nonneg_left (sq_nonneg _) ha (hp y)

omit [MeasurableSpace (Point n)] [BorelSpace (Point n)] in
theorem weighted_young (u q : Point n) {r : ℝ} (hr : 0 < r) :
    2*⟪q,u⟫_ℝ-r*‖u‖^2 ≤ ‖q‖^2/r := by
  have h := norm_sub_sq_real q (r • u)
  rw [real_inner_smul_right,norm_smul,Real.norm_eq_abs,abs_of_pos hr] at h
  have hn := sq_nonneg ‖q-r • u‖
  apply (le_div_iff₀ hr).mpr
  nlinarith

/-- The actual periodic elliptic optimizer has no more energy than its
constructed representing flux. -/
theorem optimizer_energy_le_fluxAction (ρ : Point n →ᵇ ℝ)
    (q : Lp (Point n) 2 (cubePoint (n := n))) {a : ℝ} (ha : 0 < a) (hp : ∀ y, a ≤ ρ y) :
    functional q (optimizer ρ (functional q)) ≤ ∫ y, ‖q y‖^2/ρ y ∂cubePoint := by
  let u : gradientClosure (cubePoint (n := n)) := optimizer ρ (functional q)
  have he := optimizer_equation ρ (functional q) ha (Eventually.of_forall hp)
    (optimizer ρ (functional q))
  rw [weightedOperator_inner] at he
  simp only [real_inner_self_eq_norm_sq] at he
  have hu : Integrable (fun y => ρ y*‖(u : Lp (Point n) 2 cubePoint) y‖^2) cubePoint := by
    simpa only [real_inner_self_eq_norm_sq] using integrable_weighted_inner cubePoint ρ u u
  have hq := L2.integrable_inner (𝕜 := ℝ) q (u : Lp (Point n) 2 cubePoint)
  have hineq := integral_mono ((hq.const_mul 2).sub hu) (integrable_fluxAction ρ q ha hp)
    (fun y => weighted_young ((u : Lp (Point n) 2 cubePoint) y) (q y) (ha.trans_le (hp y)))
  simp only [Pi.sub_apply] at hineq
  rw [integral_sub (hq.const_mul 2) hu,integral_const_mul,← functional_apply] at hineq
  change (∫ y, ρ y*‖(u : Lp (Point n) 2 cubePoint) y‖^2 ∂cubePoint) = functional q u at he
  rw [he] at hineq
  change functional q u ≤ _
  linarith

end SharpWasserstein.PeriodicFluxOptimizer
