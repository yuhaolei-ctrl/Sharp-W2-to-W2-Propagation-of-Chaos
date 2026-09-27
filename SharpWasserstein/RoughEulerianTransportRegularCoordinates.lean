import SharpWasserstein.RoughEulerianTransportRegular
import SharpWasserstein.PropagatedSourceEquation

/-! Exact Euclidean-coordinate adapter for the regular finite-action theorem.
Coordinate norm constants occur only in regularity of the constructed drift;
the action is the literal Euclidean square norm with coefficient one. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal ENNReal Topology ContDiff InnerProductSpace Interval
namespace SharpWasserstein.RoughEulerianTransport
open WeightedTangent NoiseAverage PropagatedSourceEquation

section Linear
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem equivDrift_fderiv (L : E ≃L[ℝ] F) {v : E → E} (hv : Differentiable ℝ v) (x : F) :
    fderiv ℝ (equivDrift L v) x = L.toContinuousLinearMap.comp
      ((fderiv ℝ v (L.symm x)).comp L.symm.toContinuousLinearMap) := by
  exact ((L.hasFDerivAt).comp x ((hv (L.symm x)).hasFDerivAt.comp x
    L.symm.hasFDerivAt)).fderiv

theorem equivDrift_fderiv_lipschitz (L : E ≃L[ℝ] F) {v : E → E}
    (hv : Differentiable ℝ v) {K : ℝ≥0} (hK : LipschitzWith K (fderiv ℝ v)) :
    LipschitzWith (‖L.toContinuousLinearMap‖₊*K*‖L.symm.toContinuousLinearMap‖₊^2)
      (fderiv ℝ (equivDrift L v)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm,equivDrift_fderiv L hv x,equivDrift_fderiv L hv y,
    ← ContinuousLinearMap.comp_sub,← ContinuousLinearMap.sub_comp]
  calc
    _ ≤ ‖L.toContinuousLinearMap‖*
        (‖fderiv ℝ v (L.symm x)-fderiv ℝ v (L.symm y)‖*‖L.symm.toContinuousLinearMap‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ ‖L.toContinuousLinearMap‖*((K:ℝ)*
        (‖L.symm.toContinuousLinearMap‖*dist x y)*‖L.symm.toContinuousLinearMap‖) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      simpa only [dist_eq_norm,coe_nnnorm] using (hK.dist_le_mul _ _).trans
        (mul_le_mul_of_nonneg_left (L.symm.lipschitz.dist_le_mul x y) K.coe_nonneg)
    _ = _ := by simp only [NNReal.coe_mul,NNReal.coe_pow,coe_nnnorm]; ring
end Linear

variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]

/-- Literal compact Euclidean continuity equation for a supplied regular velocity. -/
structure EuclideanCompactWeakContinuity (v : ℝ → Point (N*d) → Point (N*d))
    (μ : ℝ → ProbabilityMeasure (Point (N*d))) (T : ℝ) : Prop where
  continuous : Continuous μ
  equation : ∀ φ : Test (N*d),∀ a ∈ Icc 0 T,∀ b ∈ Icc 0 T,
    IntervalIntegrable (fun r => ∫ x,⟪gradient φ.val x,v r x⟫_ℝ ∂(μ r : Measure _)) volume a b ∧
    (∫ x,φ.val x ∂(μ b : Measure _))-(∫ x,φ.val x ∂(μ a : Measure _)) =
      ∫ r in a..b,∫ x,⟪gradient φ.val x,v r x⟫_ℝ ∂(μ r : Measure _)

def configurationVelocity (v : ℝ → Point (N*d) → Point (N*d)) (t : ℝ) :
    Configuration d N → Configuration d N := equivDrift (configurationEuclidean d N).symm (v t)

def configurationCurve (μ : ℝ → ProbabilityMeasure (Point (N*d))) (t : ℝ) :
    ProbabilityMeasure (Configuration d N) :=
  (μ t).map (configurationEuclidean d N).symm.continuous.measurable.aemeasurable

/-- The literal Euclidean flux equation becomes exactly the configuration
compact-test weak equation, with the genuine test pullback. -/
theorem EuclideanCompactWeakContinuity.toConfiguration
    {v : ℝ → Point (N*d) → Point (N*d)} {μ : ℝ → ProbabilityMeasure (Point (N*d))} {T : ℝ}
    (h : EuclideanCompactWeakContinuity v μ T) :
    EulerianTransport.CompactWeakContinuity (configurationVelocity v) (configurationCurve μ) T := by
  refine ⟨(ProbabilityMeasure.continuous_map (configurationEuclidean d N).symm.continuous).comp h.continuous,?_⟩
  intro ψ hψ a ha b hb
  let φ : Test (N*d) := ⟨euclideanTest ψ,smoothCompactTest_euclidean hψ⟩
  have hi (r : ℝ) : (∫ x,ψ x ∂(configurationCurve μ r : Measure _)) =
      ∫ y,φ.val y ∂(μ r : Measure _) := by
    exact integral_map_equiv (configurationEuclidean d N).symm.toHomeomorph.toMeasurableEquiv ψ
  have hg (r : ℝ) : (∫ x,EulerianTransport.generator (configurationVelocity v r) ψ x
      ∂(configurationCurve μ r : Measure _)) =
      ∫ y,⟪gradient φ.val y,v r y⟫_ℝ ∂(μ r : Measure _) := by
    rw [show (∫ x,EulerianTransport.generator (configurationVelocity v r) ψ x
        ∂(configurationCurve μ r : Measure _)) =
      ∫ y,EulerianTransport.generator (configurationVelocity v r) ψ ((configurationEuclidean d N).symm y)
        ∂(μ r : Measure _) from integral_map_equiv
          (configurationEuclidean d N).symm.toHomeomorph.toMeasurableEquiv _]
    apply integral_congr_ae
    filter_upwards [] with y
    rw [inner_gradient_left]
    change fderiv ℝ ψ ((configurationEuclidean d N).symm y)
      ((configurationEuclidean d N).symm (v r (configurationEuclidean d N ((configurationEuclidean d N).symm y)))) =
      fderiv ℝ (ψ ∘ (configurationEuclidean d N).symm) y (v r y)
    rw [(configurationEuclidean d N).symm.comp_right_fderiv]
    simp
  simpa only [hi,hg] using h.equation φ a ha b hb

/-- Exact action conversion, without a dimension-dependent norm comparison. -/
theorem configuration_action_eq (v : ℝ → Point (N*d) → Point (N*d))
    (μ : ProbabilityMeasure (Point (N*d))) (t : ℝ) :
    (∫ x,productCost (configurationVelocity v t x) 0
      ∂(μ.map (configurationEuclidean d N).symm.continuous.measurable.aemeasurable : Measure _)) =
      ∫ y,‖v t y‖^2 ∂(μ : Measure _) := by
  rw [show (∫ x,productCost (configurationVelocity v t x) 0
      ∂(μ.map (configurationEuclidean d N).symm.continuous.measurable.aemeasurable : Measure _)) =
    ∫ y,productCost (configurationVelocity v t ((configurationEuclidean d N).symm y)) 0
      ∂(μ : Measure _) from integral_map_equiv
        (configurationEuclidean d N).symm.toHomeomorph.toMeasurableEquiv _]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [productCost_eq_configurationEuclidean_dist_sq]
  simp only [configurationVelocity,equivDrift,ContinuousLinearEquiv.symm_symm,
    ContinuousLinearEquiv.apply_symm_apply,map_zero,sub_zero]

/-- The exact finite-action bound for actual regular Euclidean curves. -/
theorem EuclideanCompactWeakContinuity.wassersteinSq_le_finiteAction
    {v : ℝ → Point (N*d) → Point (N*d)} {μ : ℝ → ProbabilityMeasure (Point (N*d))} {T : ℝ}
    (h : EuclideanCompactWeakContinuity v μ T) {M K K₁ : ℝ≥0}
    (hv : Continuous (Function.uncurry v)) (hb : ∀ t x,‖v t x‖ ≤ M)
    (hl : ∀ t,LipschitzWith K (v t)) (hT : 0 ≤ T)
    (hvs : ∀ t,ContDiff ℝ ∞ (v t)) (hvB : ∀ t,AllDerivativesBounded (v t))
    (hv₁ : ∀ t,LipschitzWith K₁ (fderiv ℝ (v t)))
    (hP : HasSecondMoment ((μ 0 : Measure _).map (configurationEuclidean d N).symm))
    {a b : ℝ} (ha : a ∈ Icc 0 T) (hbT : b ∈ Icc 0 T) (hab : a ≤ b)
    {E : ℝ → ℝ} (hE : IntervalIntegrable E volume a b)
    (hbound : ∀ᵐ t ∂volume.restrict (Icc a b),(∫ x,‖v t x‖^2 ∂(μ t : Measure _)) ≤ E t) :
    wassersteinSq ((μ a : Measure _).map (configurationEuclidean d N).symm)
      ((μ b : Measure _).map (configurationEuclidean d N).symm) ≤
      ENNReal.ofReal ((b-a)*(∫ t in a..b,E t)) := by
  let L := (configurationEuclidean d N).symm
  have hc : Continuous (Function.uncurry (configurationVelocity v)) :=
    L.continuous.comp (hv.comp (continuous_fst.prodMk
      ((configurationEuclidean d N).continuous.comp continuous_snd)))
  have hb' (t : ℝ) (x : Configuration d N) :
      ‖configurationVelocity v t x‖ ≤ (‖L.toContinuousLinearMap‖₊*M:ℝ≥0) :=
    (L.toContinuousLinearMap.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (hb t _) (norm_nonneg _))
  have hl' (t : ℝ) : LipschitzWith (‖L.toContinuousLinearMap‖₊*K*‖L.symm.toContinuousLinearMap‖₊)
      (configurationVelocity v t) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [mul_assoc,configurationVelocity,equivDrift,Function.comp_def,L,dist_eq_norm] using
      (L.lipschitz.comp ((hl t).comp L.symm.lipschitz)).dist_le_mul x y
  have hd' (t : ℝ) := equivDrift_fderiv_lipschitz L ((hvs t).differentiable (by simp)) (hv₁ t)
  apply regular_wassersteinSq_le_finiteAction h.toConfiguration hc hb' hl' hT
    (fun t => equivDrift_smooth L (hvs t)) (fun t => equivDrift_allDerivativesBounded L (hvs t) (hvB t))
    hd' hP ha hbT hab hE
  simpa only [configurationCurve,configuration_action_eq] using hbound

end SharpWasserstein.RoughEulerianTransport
