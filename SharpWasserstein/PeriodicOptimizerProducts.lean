module

public import SharpWasserstein.Compat
public import SharpWasserstein.PeriodicL2Multiplier

@[expose] public section

/-! Actual optimizer coordinates and their smooth periodic multiples lie in
closed scalar test-value spaces. This makes weak Hessian convergence usable
against the products occurring in the drift energy identity. -/

noncomputable section
namespace SharpWasserstein.PeriodicOptimizerProducts
open MeasureTheory Filter Set PeriodicIntegrationByParts PeriodicFourierTests PeriodicBochner
open PeriodicGalerkin PeriodicGradientClosure PeriodicSmoothGradient PeriodicTestL2 WeightedTangent
open scoped ENNReal Topology BigOperators ContDiff InnerProductSpace BoundedContinuousFunction

variable {n : ℕ} [MeasurableSpace (Point n)] [BorelSpace (Point n)]

theorem cubePoint_ae_mem : ∀ᵐ y ∂cubePoint (n := n),
    coordinateEquiv n y ∈ Set.pi Set.univ (fun _ : Fin n => Icc (0 : ℝ) 1) := by
  have hmeas : MeasurableSet {y : Point n |
      coordinateEquiv n y ∈ Set.pi Set.univ (fun _ : Fin n => Icc (0 : ℝ) 1)} :=
    ((isCompact_univ_pi (fun _ : Fin n => isCompact_Icc)).isClosed.preimage
      (coordinateEquiv n).continuous).measurableSet
  rw [cubePoint, ae_map_iff (coordinateEquiv n).symm.continuous.measurable.aemeasurable hmeas]
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using cube_ae_mem n

/-- A smooth periodic gradient component is the actual scalar value of its derivative test. -/
theorem component_gradientVector_eq_value (f : SmoothPeriodicTest n) (j : Fin n) :
    component j (gradientVector f.val f.property.1 : Lp (Point n) 2 (cubePoint (n := n))) =
      value (partialTest f j) := by
  apply Lp.ext
  filter_upwards [component_ae j (gradientVector f.val f.property.1 : Lp (Point n) 2 cubePoint),
    testGradient_ae cubePoint (compactTest f.val f.property.1),
    scalarTestLp_ae (compactTest (partialTest f j).val (partialTest f j).property.1), cubePoint_ae_mem] with y ha hb hc hd
  change component j (gradientVector f.val f.property.1 : Lp (Point n) 2 cubePoint) y =
    scalarTestLp (compactTest (partialTest f j).val (partialTest f j).property.1) y
  rw [ha, hc]
  change testGradient cubePoint (compactTest f.val f.property.1) y j = _
  rw [hb]
  have hg := compactTest_gradient_on_cube f.val f.property.1 hd
  have hv := compactTest_value_on_cube (partialTest f j).val (partialTest f j).property.1 hd
  simp only [ContinuousLinearEquiv.symm_apply_apply] at hg hv
  rw [hg, hv, ← PDEPairings.directionDeriv_eq_gradient_component, directionDeriv_pullback]
  rfl

theorem component_vector_mem_testClosure (ρ : Point n →ᵇ ℝ)
    (ℓ : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)
    (s : Finset ((Fin n → ℤ) × Bool)) (j : Fin n) :
    component j (vector ρ ℓ s : Lp (Point n) 2 cubePoint) ∈ WeakDerivativeLimit.testClosure value := by
  have hf := frequencySpace_properties s (potential ρ ℓ s).property
  let f : SmoothPeriodicTest n := ⟨(potential ρ ℓ s).val, hf.1, hf.2.1⟩
  have hg : gradientVector f.val f.property.1 = vector ρ ℓ s := gradient_potential ρ ℓ s
  rw [← hg, component_gradientVector_eq_value]
  exact (value (n := n)).range.le_topologicalClosure (LinearMap.mem_range_self _ _)

/-- The limiting optimizer's actual coordinates belong to the same scalar test closure. -/
theorem component_optimizer_mem_testClosure (ρ : Point n →ᵇ ℝ)
    (ℓ : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)
    {a : ℝ} (ha : 0 < a) (hp : ∀ᵐ y ∂cubePoint, a ≤ ρ y) (j : Fin n) :
    component j ((optimizer ρ ℓ : gradientClosure (cubePoint (n := n))) :
      Lp (Point n) 2 cubePoint) ∈ WeakDerivativeLimit.testClosure value := by
  have hv := (gradientClosure (cubePoint (n := n))).subtypeL.continuous.continuousAt.tendsto.comp
    (vector_tendsto ρ ℓ ha hp)
  have hc := (component j).continuous.continuousAt.tendsto.comp hv
  apply (value (n := n)).range.isClosed_topologicalClosure.mem_of_tendsto hc
  exact Filter.Eventually.of_forall (fun s => component_vector_mem_testClosure ρ ℓ s j)

/-- All actual drift-test products with the optimizer are admissible weak-Hessian tests. -/
theorem multiply_component_optimizer_mem_testClosure (q ρ : Point n →ᵇ ℝ)
    (ℓ : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)
    (hq : ContDiff ℝ ∞ (fun x => q ((coordinateEquiv n).symm x)))
    (hpq : Periodic (fun x => q ((coordinateEquiv n).symm x)))
    {a : ℝ} (ha : 0 < a) (hp : ∀ᵐ y ∂cubePoint, a ≤ ρ y) (j : Fin n) :
    PeriodicL2Multiplier.operator q (component j
      ((optimizer ρ ℓ : gradientClosure (cubePoint (n := n))) : Lp (Point n) 2 cubePoint)) ∈
        WeakDerivativeLimit.testClosure value :=
  PeriodicL2Multiplier.operator_mem_testClosure q hq hpq (component_optimizer_mem_testClosure ρ ℓ ha hp j)

end SharpWasserstein.PeriodicOptimizerProducts
