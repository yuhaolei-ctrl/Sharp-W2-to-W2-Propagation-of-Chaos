import SharpWasserstein.PeriodicFourierDensity
import SharpWasserstein.PeriodicGradientClosure

/-! Every genuine smooth periodic gradient belongs to the constructed Fourier
closure. This follows from actual `H¹` Fourier approximation, not from a density
hypothesis inserted into the elliptic theorem. -/

noncomputable section
namespace SharpWasserstein.PeriodicSmoothGradient
open MeasureTheory Filter Set PeriodicIntegrationByParts PeriodicFourierTests PeriodicBochner
open PeriodicFourierPolynomials PeriodicFourierDensity PeriodicGalerkin PeriodicGradientClosure
open WeightedTangent WeightedDensity
open scoped ENNReal Topology BigOperators ContDiff InnerProductSpace BoundedContinuousFunction

/-- One fixed compactification preserves the entire fundamental cube. -/
def compactTest {n : ℕ} (f : Coordinates n → ℝ) (hf : ContDiff ℝ ∞ f) : Test n :=
  SmoothCutoff.approximate (pullback f) (hf.comp (coordinateEquiv n).contDiff) n

theorem compactTest_gradient_on_cube {n : ℕ} (f : Coordinates n → ℝ)
    (hf : ContDiff ℝ ∞ f) {x : Coordinates n}
    (hx : x ∈ Set.pi Set.univ (fun _ : Fin n => Icc (0 : ℝ) 1)) :
    gradient (compactTest f hf : Point n → ℝ) ((coordinateEquiv n).symm x) =
      gradient (pullback f) ((coordinateEquiv n).symm x) := by
  apply Filter.EventuallyEq.gradient_eq
  filter_upwards [cutoff_eq_one_near_cube hx] with y hy
  change SmoothCutoff.cutoff n n y * pullback f y = pullback f y
  rw [hy, one_mul]

variable {n : ℕ} [MeasurableSpace (Point n)] [BorelSpace (Point n)]

/-- The actual smooth periodic gradient as a vector in weighted `L²` over the cube. -/
def gradientVector (f : Coordinates n → ℝ) (hf : ContDiff ℝ ∞ f) :
    gradientClosure (cubePoint (n := n)) := gradientIntoClosure cubePoint (compactTest f hf)

theorem gradientVector_polynomial_mem (s : Finset (Fin n → ℤ)) (f : Coordinates n → ℝ) :
    gradientVector (polynomial s f) (smooth_polynomial s f) ∈ periodicSpace := by
  apply trialSpace_le_periodicSpace (frequencySet s)
  exact ⟨⟨polynomial s f, polynomial_mem s f⟩, rfl⟩

/-- The actual Hilbert distance between gradients equals the sum of coordinate square-errors. -/
theorem gradientVector_norm_sub_sq (f g : Coordinates n → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ‖gradientVector f hf - gradientVector g hg‖ ^ 2 =
      ∑ i : Fin n, ∫ x, (coordinatePartial f i x - coordinatePartial g i x) ^ 2 ∂cube n := by
  change ‖testGradient cubePoint (compactTest f hf) - testGradient cubePoint (compactTest g hg)‖ ^ 2 = _
  rw [lp_norm_sq_eq_integral]
  calc
    _ = ∫ y, ‖gradient (compactTest f hf : Point n → ℝ) y -
        gradient (compactTest g hg : Point n → ℝ) y‖ ^ 2 ∂cubePoint := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (testGradient cubePoint (compactTest f hf))
        (testGradient cubePoint (compactTest g hg)), testGradient_ae cubePoint (compactTest f hf),
        testGradient_ae cubePoint (compactTest g hg)] with y ha hb hc
      rw [ha]
      simp only [Pi.sub_apply, hb, hc]
    _ = ∫ x, ∑ i : Fin n, (coordinatePartial f i x - coordinatePartial g i x) ^ 2 ∂cube n := by
      rw [integral_cubePoint]
      apply integral_congr_ae
      filter_upwards [cube_ae_mem n] with x hx
      rw [compactTest_gradient_on_cube f hf hx, compactTest_gradient_on_cube g hg hx,
        EuclideanSpace.real_norm_sq_eq]
      apply Finset.sum_congr rfl
      intro i _
      simp only [PiLp.sub_apply]
      rw [← PDEPairings.directionDeriv_eq_gradient_component,
        ← PDEPairings.directionDeriv_eq_gradient_component, directionDeriv_pullback,
        directionDeriv_pullback, ContinuousLinearEquiv.apply_symm_apply]
    _ = _ := integral_finsetSum Finset.univ (fun i _ =>
      continuous_integrable_cube
        (((smooth_coordinatePartial hf i).continuous.sub (smooth_coordinatePartial hg i).continuous).pow 2))

/-- Actual Fourier gradients converge strongly to every smooth periodic gradient. -/
theorem gradientVector_polynomial_tendsto (f : Coordinates n → ℝ)
    (hf : ContDiff ℝ ∞ f) (hp : Periodic f) :
    Tendsto (fun s => gradientVector (polynomial s f) (smooth_polynomial s f))
      atTop (𝓝 (gradientVector f hf)) := by
  have hs : Tendsto (fun s => ‖gradientVector (polynomial s f) (smooth_polynomial s f) -
      gradientVector f hf‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simp_rw [gradientVector_norm_sub_sq]
    have h := tendsto_finsetSum Finset.univ (fun i _ =>
      integral_derivative_error_tendsto f hp
        (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)) i)
    simpa only [Finset.sum_const_zero] using h
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using h

/-- All smooth periodic test gradients lie in the actual closed Fourier gradient space. -/
theorem gradientVector_mem_periodicSpace (f : Coordinates n → ℝ)
    (hf : ContDiff ℝ ∞ f) (hp : Periodic f) : gradientVector f hf ∈ periodicSpace := by
  apply (iSup (trialSpace (n := n))).isClosed_topologicalClosure.mem_of_tendsto
    (gradientVector_polynomial_tendsto f hf hp)
  exact Filter.Eventually.of_forall (fun s => gradientVector_polynomial_mem s f)

/-- The actual vector space of globally smooth coordinate-periodic scalar tests. -/
def periodicTestSpace (n : ℕ) : Submodule ℝ (Coordinates n → ℝ) where
  carrier := {f | ContDiff ℝ ∞ f ∧ Periodic f}
  zero_mem' := ⟨contDiff_const, fun _ _ => rfl⟩
  add_mem' hf hg := ⟨hf.1.add hg.1, fun i x => congrArg₂ (· + ·) (hf.2 i x) (hg.2 i x)⟩
  smul_mem' c _ hf := ⟨hf.1.const_smul c, fun i x => congrArg (c • ·) (hf.2 i x)⟩

abbrev SmoothPeriodicTest (n : ℕ) := periodicTestSpace n

/-- A fixed cutoff embeds all smooth periodic tests linearly into actual compact tests. -/
def testCompactification : SmoothPeriodicTest n →ₗ[ℝ] WeightedTangent.Test n where
  toFun f := compactTest f.val f.property.1
  map_add' f g := by
    apply Subtype.ext
    funext y
    change SmoothCutoff.cutoff n n y * (f.val (coordinateEquiv n y) + g.val (coordinateEquiv n y)) =
      SmoothCutoff.cutoff n n y * f.val (coordinateEquiv n y) +
        SmoothCutoff.cutoff n n y * g.val (coordinateEquiv n y)
    ring
  map_smul' c f := by
    apply Subtype.ext
    funext y
    change SmoothCutoff.cutoff n n y * (c * f.val (coordinateEquiv n y)) =
      c * (SmoothCutoff.cutoff n n y * f.val (coordinateEquiv n y))
    ring

/-- The genuine linear test-gradient map for every smooth periodic test. -/
def periodicGradientMap : SmoothPeriodicTest n →ₗ[ℝ] gradientClosure (cubePoint (n := n)) :=
  (gradientIntoClosure cubePoint).comp testCompactification

/-- The Fourier closure equals the closure of all genuine smooth periodic gradients. -/
theorem periodicSpace_eq_smoothGradientClosure : periodicSpace (n := n) =
    (periodicGradientMap (n := n)).range.topologicalClosure := by
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · apply iSup_le
      intro s v hv
      obtain ⟨f, rfl⟩ := hv
      have hf := frequencySpace_properties s f.property
      exact (periodicGradientMap (n := n)).range.le_topologicalClosure
        ⟨⟨f.val, hf.1, hf.2.1⟩, rfl⟩
    · exact (periodicGradientMap (n := n)).range.isClosed_topologicalClosure
  · apply Submodule.topologicalClosure_minimal
    · rintro v ⟨f, rfl⟩
      exact gradientVector_mem_periodicSpace f.val f.property.1 f.property.2
    · exact (iSup (trialSpace (n := n))).isClosed_topologicalClosure

/-- Coordinate derivatives remain genuine smooth periodic tests. -/
def partialTest (f : SmoothPeriodicTest n) (i : Fin n) : SmoothPeriodicTest n :=
  ⟨coordinatePartial f.val i, smooth_coordinatePartial f.property.1 i,
    periodic_coordinatePartial f.property.2 i⟩

/-- The constructed periodic optimizer satisfies the actual weak elliptic equation
against every smooth periodic function, with no Fourier-density hypothesis. -/
theorem optimizer_smooth_equation (ρ : Point n →ᵇ ℝ)
    (ℓ : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)
    {a : ℝ} (ha : 0 < a) (hp : ∀ᵐ y ∂cubePoint, a ≤ ρ y)
    (f : Coordinates n → ℝ) (hf : ContDiff ℝ ∞ f) (hpf : Periodic f) :
    ℓ (gradientVector f hf) = ∫ x, ρ ((coordinateEquiv n).symm x) *
      ⟪((optimizer ρ ℓ : gradientClosure (cubePoint (n := n))) : Lp (Point n) 2 cubePoint)
          ((coordinateEquiv n).symm x),
        gradient (pullback f) ((coordinateEquiv n).symm x)⟫_ℝ ∂cube n := by
  have h := optimizer_equation ρ ℓ ha hp
    ⟨gradientVector f hf, gradientVector_mem_periodicSpace f hf hpf⟩
  rw [← h, weightedOperator_inner]
  calc
    _ = ∫ y, ρ y *
        ⟪((optimizer ρ ℓ : gradientClosure (cubePoint (n := n))) : Lp (Point n) 2 cubePoint) y,
          gradient (compactTest f hf : Point n → ℝ) y⟫_ℝ ∂cubePoint := by
      apply integral_congr_ae
      filter_upwards [testGradient_ae cubePoint (compactTest f hf)] with y hy
      exact congrArg (fun z : Point n => ρ y * ⟪_, z⟫_ℝ) hy
    _ = _ := by
      rw [integral_cubePoint]
      apply integral_congr_ae
      filter_upwards [cube_ae_mem n] with x hx
      rw [compactTest_gradient_on_cube f hf hx]

end SharpWasserstein.PeriodicSmoothGradient
