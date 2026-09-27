import SharpWasserstein.PeriodicConvolutionMarginal
import SharpWasserstein.PeriodicOptimizerProducts
import SharpWasserstein.WeightedMarginal

/-! Actual prefix lifting for periodic gradient fields on the product cube.
The reference measure, Euclidean zero-extension, and L² isometry are derived
from the genuine product measure and coordinate maps. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
namespace SharpWasserstein.PeriodicMarginalLift
open PeriodicIntegrationByParts PeriodicFourierTests PeriodicGalerkin PeriodicGradientClosure PeriodicBochner
open PeriodicSmoothGradient PeriodicOptimizerProducts PeriodicConvolution WeightedTangent WeightedMarginal
variable {n m : ℕ}

theorem prefixCoords_measurePreserving (n m : ℕ) :
    MeasurePreserving (prefixCoords n m) (cube (n+m)) (cube n) := by
  have h := (measurePreserving_fst (μ := cube n) (ν := cube m)).comp
    (splitCoordinates_measurePreserving n m)
  simpa only [Function.comp_def,splitCoordinates_fst] using h

variable [MeasurableSpace (Point n)] [BorelSpace (Point n)]
  [MeasurableSpace (Point (n+m))] [BorelSpace (Point (n+m))]

omit [MeasurableSpace (Point (n+m))] [BorelSpace (Point (n+m))] in
theorem coordinate_measurePreserving :
    MeasurePreserving (coordinateEquiv n) (cubePoint (n := n)) (cube n) := by
  refine ⟨(coordinateEquiv n).continuous.measurable,?_⟩
  rw [cubePoint,Measure.map_map (coordinateEquiv n).continuous.measurable
    (coordinateEquiv n).symm.continuous.measurable]
  simp only [Function.comp_def,ContinuousLinearEquiv.apply_symm_apply]
  exact Measure.map_id

omit [MeasurableSpace (Point (n+m))] [BorelSpace (Point (n+m))] in
theorem coordinateSymm_measurePreserving :
    MeasurePreserving (coordinateEquiv n).symm (cube n) (cubePoint (n := n)) :=
  ⟨(coordinateEquiv n).symm.continuous.measurable,rfl⟩

theorem prefix_measurePreserving :
    MeasurePreserving (prefixProjection n m) (cubePoint (n := n+m)) (cubePoint (n := n)) := by
  have h := (coordinateSymm_measurePreserving (n := n)).comp
    ((prefixCoords_measurePreserving n m).comp (coordinate_measurePreserving (n := n+m)))
  exact h

/-- Exact prefix marginal identity for the Euclidean product cube. -/
theorem cubePoint_prefix_map :
    (cubePoint (n := n+m)).map (prefixProjection n m) = cubePoint (n := n) :=
  prefix_measurePreserving.map_eq

/-- Pullback along the genuine prefix projection, followed by Euclidean zero-extension. -/
def liftLinear : Lp (Point n) 2 (cubePoint (n := n)) →ₗ[ℝ]
    Lp (Point (n+m)) 2 (cubePoint (n := n+m)) :=
  ((prefixEmbedding n m).toContinuousLinearMap.compLpₗ 2 cubePoint).comp
    (Lp.compMeasurePreservingₗ ℝ (prefixProjection n m) prefix_measurePreserving)

theorem liftLinear_ae (u : Lp (Point n) 2 (cubePoint (n := n))) :
    liftLinear (m := m) u =ᵐ[cubePoint]
      (fun y => prefixEmbedding n m (u (prefixProjection n m y))) := by
  filter_upwards [(prefixEmbedding n m).toContinuousLinearMap.coeFn_compLp
    (Lp.compMeasurePreserving (prefixProjection n m) prefix_measurePreserving u),
    Lp.coeFn_compMeasurePreserving u prefix_measurePreserving] with y hy hz
  exact hy.trans (congrArg (prefixEmbedding n m) hz)

theorem liftLinear_norm (u : Lp (Point n) 2 (cubePoint (n := n))) :
    ‖liftLinear (m := m) u‖ = ‖u‖ := by
  have hn : ∀ᵐ y ∂cubePoint, ‖liftLinear (m := m) u y‖ =
      ‖Lp.compMeasurePreserving (prefixProjection n m) prefix_measurePreserving u y‖ := by
    filter_upwards [liftLinear_ae (m := m) u,
      Lp.coeFn_compMeasurePreserving u prefix_measurePreserving] with y hy hz
    rw [hy,hz,LinearIsometry.norm_map]
    rfl
  calc
    _ = ‖Lp.compMeasurePreserving (prefixProjection n m) prefix_measurePreserving u‖ := by
      simp only [Lp.norm_def]
      congr 1
      exact eLpNorm_congr_norm_ae hn
    _ = _ := Lp.norm_compMeasurePreserving _ _

def lift : Lp (Point n) 2 (cubePoint (n := n)) →ₗᵢ[ℝ]
    Lp (Point (n+m)) 2 (cubePoint (n := n+m)) where
  toLinearMap := liftLinear
  norm_map' := liftLinear_norm

theorem lift_gradientClosure_mem (u : gradientClosure (cubePoint (n := n))) :
    lift (m := m) (u : Lp (Point n) 2 cubePoint) ∈ gradientClosure (cubePoint (n := n+m)) := by
  refine (dense_gradientIntoClosure cubePoint).induction_on u ?_ ?_
  · exact (testGradientLinear cubePoint).range.isClosed_topologicalClosure.preimage
      ((lift (m := m)).continuous.comp continuous_subtype_val)
  · intro φ
    obtain ⟨hs,ha,hb⟩ := cylinder_test_smooth_bounded (m := m) φ
    have hg := bounded_smooth_gradient_memLp
      (cubePoint (n := n+m)) _ hs hb
    have he : lift (m := m) (testGradient cubePoint φ) =
        hg.toLp (gradient ((φ : Point n → ℝ) ∘ prefixProjection n m)) := by
      apply Lp.ext
      have hφ : ∀ᵐ y ∂(cubePoint (n := n+m)).map (prefixProjection n m),
          testGradient cubePoint φ y = gradient (φ : Point n → ℝ) y := by
        rw [cubePoint_prefix_map]
        exact testGradient_ae cubePoint φ
      filter_upwards [liftLinear_ae (m := m) (testGradient cubePoint φ),
        ae_of_ae_map (prefixProjection n m).continuous.measurable.aemeasurable hφ,
        hg.coeFn_toLp] with y hy hp ht
      exact hy.trans (by rw [hp,ht,gradient_comp_prefixProjection (test_differentiable φ)])
    change lift (m := m) (testGradient cubePoint φ) ∈ _
    rw [he]
    exact bounded_smooth_gradient_memClosure
      cubePoint _ hs ha hb hg

def gradientLiftLinear : gradientClosure (cubePoint (n := n)) →ₗ[ℝ]
    gradientClosure (cubePoint (n := n+m)) :=
  ((lift (n := n) (m := m)).toLinearMap.comp (gradientClosure cubePoint).subtype).codRestrict
    (gradientClosure cubePoint) (lift_gradientClosure_mem (n := n) (m := m))

/-- Continuous prefix pullback on the actual closed gradient spaces. -/
def gradientLift : gradientClosure (cubePoint (n := n)) →L[ℝ]
    gradientClosure (cubePoint (n := n+m)) :=
  ((lift (n := n) (m := m)).toContinuousLinearMap.comp
    (gradientClosure (cubePoint (n := n))).subtypeL).codRestrict
      (gradientClosure (cubePoint (n := n+m))) (lift_gradientClosure_mem (n := n) (m := m))

omit [MeasurableSpace (Point n)] [BorelSpace (Point n)]
  [MeasurableSpace (Point (n+m))] [BorelSpace (Point (n+m))] in
def prefixLinear (n m : ℕ) : Coordinates (n+m) →L[ℝ] Coordinates n :=
  (coordinateEquiv n).toContinuousLinearMap.comp
    ((prefixProjection n m).comp (coordinateEquiv (n+m)).symm.toContinuousLinearMap)

omit [MeasurableSpace (Point n)] [BorelSpace (Point n)]
  [MeasurableSpace (Point (n+m))] [BorelSpace (Point (n+m))] in
theorem prefix_smooth (n m : ℕ) : ContDiff ℝ ∞ (prefixCoords n m) :=
  (prefixLinear n m).contDiff

omit [MeasurableSpace (Point n)] [BorelSpace (Point n)]
  [MeasurableSpace (Point (n+m))] [BorelSpace (Point (n+m))] in
theorem prefix_periodic {f : Coordinates n → ℝ} (hp : Periodic f) :
    Periodic (f ∘ prefixCoords n m) := by
  intro i x
  cases i using Fin.addCases with
  | left i =>
    have he : prefixCoords n m (x + Pi.single (i.castAdd m) 1) =
        prefixCoords n m x + Pi.single i 1 := by
      ext j
      simp [prefixCoords,Pi.single_apply,Fin.castAdd_inj]
    change f (prefixCoords n m (x + Pi.single (i.castAdd m) 1)) = _
    rw [he]
    exact hp i _
  | right i =>
    have he : prefixCoords n m (x + Pi.single (i.natAdd n) 1) = prefixCoords n m x := by
      ext j
      have hn : (j.castAdd m) ≠ i.natAdd n := by
        intro h
        have hv := congrArg Fin.val h
        simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
        omega
      simp [prefixCoords,hn]
    change f (prefixCoords n m (x + Pi.single (i.natAdd n) 1)) = _
    rw [he]
    rfl

theorem gradientLift_gradientVector (f : Coordinates n → ℝ) (hf : ContDiff ℝ ∞ f) :
    gradientLift (m := m) (gradientVector f hf) =
      gradientVector (f ∘ prefixCoords n m) (hf.comp (prefix_smooth n m)) := by
  apply Subtype.ext
  apply Lp.ext
  have hp := ae_of_ae_map (prefixProjection n m).continuous.measurable.aemeasurable
    (show ∀ᵐ y ∂(cubePoint (n := n+m)).map (prefixProjection n m),
      testGradient cubePoint (compactTest f hf) y = gradient (pullback f) y from by
        rw [cubePoint_prefix_map]
        filter_upwards [testGradient_ae cubePoint (compactTest f hf),
          cubePoint_ae_mem (n := n)] with y hy hc
        exact hy.trans (compactTest_gradient_on_cube f hf hc))
  filter_upwards [liftLinear_ae (m := m)
      (gradientVector f hf : Lp (Point n) 2 cubePoint), hp,
    testGradient_ae cubePoint (compactTest (f ∘ prefixCoords n m) (hf.comp (prefix_smooth n m))),
    cubePoint_ae_mem (n := n+m)] with y hy hl hg hc
  change lift (m := m) (gradientVector f hf : Lp (Point n) 2 cubePoint) y = _
  rw [show lift (m := m) (gradientVector f hf : Lp (Point n) 2 cubePoint) y =
    prefixEmbedding n m (gradient (pullback f) (prefixProjection n m y)) from hy.trans (congrArg _ hl)]
  change _ = testGradient cubePoint (compactTest (f ∘ prefixCoords n m) (hf.comp (prefix_smooth n m))) y
  have hgc := compactTest_gradient_on_cube (f ∘ prefixCoords n m) (hf.comp (prefix_smooth n m)) hc
  simp only [ContinuousLinearEquiv.symm_apply_apply] at hgc
  rw [hg,hgc]
  exact (gradient_comp_prefixProjection
    ((hf.comp (coordinateEquiv n).contDiff).differentiable (by simp)) y).symm

/-- A periodic tangent remains periodic under the genuine prefix lift. -/
theorem gradientLift_periodic_mem (u : periodicSpace (n := n)) :
    gradientLift (n := n) (m := m) (u : gradientClosure (cubePoint (n := n))) ∈
      periodicSpace (n := n+m) := by
  have hle : periodicSpace (n := n) ≤
      (periodicSpace (n := n+m)).comap (gradientLift (n := n) (m := m)).toLinearMap := by
    rw [periodicSpace_eq_smoothGradientClosure]
    apply Submodule.topologicalClosure_minimal
    · rintro v ⟨f,rfl⟩
      change gradientLift (m := m) (gradientVector f.val f.property.1) ∈ periodicSpace
      rw [gradientLift_gradientVector]
      exact gradientVector_mem_periodicSpace _ _ (prefix_periodic f.property.2)
    · exact (iSup (trialSpace (n := n+m))).isClosed_topologicalClosure.preimage
        (gradientLift (n := n) (m := m)).continuous
  exact hle u.property

/-- Genuine continuous prefix lifting between the two periodic tangent spaces. -/
def periodicLift : periodicSpace (n := n) →L[ℝ] periodicSpace (n := n+m) :=
  ((gradientLift (n := n) (m := m)).comp
    (periodicSpace (n := n)).subtypeL).codRestrict (periodicSpace (n := n+m))
      gradientLift_periodic_mem

end SharpWasserstein.PeriodicMarginalLift
