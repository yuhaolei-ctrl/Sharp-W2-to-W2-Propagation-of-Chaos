module

public import SharpWasserstein.Compat
public import SharpWasserstein.PeriodicBochner
public import SharpWasserstein.WeightedGalerkin
public import SharpWasserstein.SmoothCutoff

@[expose] public section

/-! Construct the actual Fourier Galerkin elliptic potentials by coercive
operator inversion. A fixed cutoff equal to one near the entire period cube
embeds periodic trial gradients into the already constructed weighted Hilbert
space without changing their integrals or coordinate derivatives. -/

noncomputable section
namespace SharpWasserstein.PeriodicGalerkin
open MeasureTheory Set Filter PeriodicIntegrationByParts PeriodicFourierTests PeriodicBochner
open WeightedTangent WeightedDensity WeightedEnergyDerivative
open scoped ENNReal InnerProductSpace BigOperators Topology BoundedContinuousFunction ContDiff

/-- The fundamental cube fits strictly inside the chosen cutoff's unit region. -/
theorem cube_norm_lt {n : ℕ} {x : Coordinates n}
    (hx : x ∈ Set.pi Set.univ (fun _ : Fin n => Icc (0 : ℝ) 1)) :
    ‖(coordinateEquiv n).symm x‖ < (n : ℝ) + 1 := by
  have hs : ‖(coordinateEquiv n).symm x‖ ^ 2 ≤ (n : ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _i : Fin n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        have hi := hx i (Set.mem_univ i)
        change (x i) ^ 2 ≤ 1
        nlinarith [hi.1, hi.2]
      _ = _ := by simp
  nlinarith [norm_nonneg ((coordinateEquiv n).symm x), Nat.cast_nonneg (α := ℝ) n]

/-- One fixed smooth cutoff works for every potential in every Fourier trial space. -/
theorem cutoff_eq_one_near_cube {n : ℕ} {x : Coordinates n}
    (hx : x ∈ Set.pi Set.univ (fun _ : Fin n => Icc (0 : ℝ) 1)) :
    SmoothCutoff.cutoff n n =ᶠ[𝓝 ((coordinateEquiv n).symm x)] (fun _ => 1) := by
  have hn : ‖((n : ℝ) + 1)⁻¹ • (coordinateEquiv n).symm x‖ < 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (by positivity : 0 < (n : ℝ) + 1)]
    rw [← div_eq_inv_mul, div_lt_one (by positivity : 0 < (n : ℝ) + 1)]
    exact cube_norm_lt hx
  have he := (SmoothCutoff.baseBump n).eventuallyEq_one_of_mem_ball (by
    simpa only [Metric.mem_ball, dist_zero_right, SmoothCutoff.baseBump] using hn)
  exact he.comp_tendsto ((show Continuous (fun y : Point n => ((n : ℝ) + 1)⁻¹ • y)
    from by fun_prop).tendsto _)

/-- Linear compactification of actual finite Fourier potentials. -/
def compactify {n : ℕ} (s : Finset ((Fin n → ℤ) × Bool)) : frequencySpace s →ₗ[ℝ] Test n where
  toFun f := SmoothCutoff.approximate (pullback f.val)
    ((frequencySpace_properties s f.property).1.comp (coordinateEquiv n).contDiff) n
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

theorem compactify_gradient_on_cube {n : ℕ} (s : Finset ((Fin n → ℤ) × Bool))
    (f : frequencySpace s) {x : Coordinates n}
    (hx : x ∈ Set.pi Set.univ (fun _ : Fin n => Icc (0 : ℝ) 1)) :
    gradient (compactify s f : Point n → ℝ) ((coordinateEquiv n).symm x) =
      gradient (pullback f.val) ((coordinateEquiv n).symm x) := by
  apply Filter.EventuallyEq.gradient_eq
  filter_upwards [cutoff_eq_one_near_cube hx] with y hy
  change SmoothCutoff.cutoff n n y * pullback f.val y = pullback f.val y
  rw [hy, one_mul]

variable {n : ℕ} [MeasurableSpace (Point n)] [BorelSpace (Point n)]

/-- The same actual fundamental-domain probability measure in Euclidean coordinates. -/
def cubePoint : Measure (Point n) := (cube n).map (coordinateEquiv n).symm

instance cubePoint_isProbabilityMeasure : IsProbabilityMeasure (cubePoint (n := n)) :=
  Measure.isProbabilityMeasure_map (coordinateEquiv n).symm.continuous.measurable.aemeasurable

theorem integral_cubePoint (f : Point n → ℝ) :
    (∫ y, f y ∂cubePoint) = ∫ x, f ((coordinateEquiv n).symm x) ∂cube n :=
  integral_map_equiv (coordinateEquiv n).symm.toHomeomorph.toMeasurableEquiv f

/-- Actual periodic test-gradient map into the established weighted `L²` closure. -/
def trialGradient (s : Finset ((Fin n → ℤ) × Bool)) :
    frequencySpace s →ₗ[ℝ] gradientClosure (cubePoint (n := n)) :=
  (gradientIntoClosure cubePoint).comp (compactify s)

/-- The finite Fourier gradient space carries the inherited actual Hilbert norm. -/
def trialSpace (s : Finset ((Fin n → ℤ) × Bool)) :
    Submodule ℝ (gradientClosure (cubePoint (n := n))) := (trialGradient s).range

instance trialSpace_finiteDimensional (s : Finset ((Fin n → ℤ) × Bool)) :
    FiniteDimensional ℝ (trialSpace s) :=
  LinearMap.finiteDimensional_range (trialGradient s)

instance trialSpace_complete (s : Finset ((Fin n → ℤ) × Bool)) : CompleteSpace (trialSpace s) :=
  (Submodule.complete_of_finiteDimensional (trialSpace s)).completeSpace_coe

def vector (ρ : Point n →ᵇ ℝ) (ℓ : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)
    (s : Finset ((Fin n → ℤ) × Bool)) : gradientClosure (cubePoint (n := n)) :=
  GalerkinApproximation.solution (trialSpace s) (weightedOperator cubePoint ρ)
    (TangentEnergy.rieszRepresentative ℓ)

/-- A smooth periodic Fourier potential is selected from the actual solved gradient range. -/
def potential (ρ : Point n →ᵇ ℝ) (ℓ : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)
    (s : Finset ((Fin n → ℤ) × Bool)) : frequencySpace s :=
  Classical.choose (GalerkinApproximation.solution (trialSpace s) (weightedOperator cubePoint ρ)
    (TangentEnergy.rieszRepresentative ℓ)).property

theorem gradient_potential (ρ : Point n →ᵇ ℝ)
    (ℓ : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)
    (s : Finset ((Fin n → ℤ) × Bool)) :
    trialGradient s (potential ρ ℓ s) = vector ρ ℓ s :=
  Classical.choose_spec (GalerkinApproximation.solution (trialSpace s) (weightedOperator cubePoint ρ)
    (TangentEnergy.rieszRepresentative ℓ)).property

/-- The Hilbert pairing of Fourier trial gradients is the actual periodic integral. -/
theorem weightedOperator_trialGradient_inner (ρ : Point n →ᵇ ℝ)
    (s : Finset ((Fin n → ℤ) × Bool)) (f g : frequencySpace s) :
    ⟪weightedOperator cubePoint ρ (trialGradient s f), trialGradient s g⟫_ℝ =
      ∫ x, ρ ((coordinateEquiv n).symm x) *
        ∑ i : Fin n, coordinatePartial f.val i x * coordinatePartial g.val i x ∂cube n := by
  rw [weightedOperator_inner]
  calc
    _ = ∫ y, ρ y * ⟪gradient (compactify s f : Point n → ℝ) y,
        gradient (compactify s g : Point n → ℝ) y⟫_ℝ ∂cubePoint := by
      apply integral_congr_ae
      filter_upwards [testGradient_ae cubePoint (compactify s f),
        testGradient_ae cubePoint (compactify s g)] with y hy hz
      exact congrArg (fun q : ℝ => ρ y * q) (congrArg₂ (inner ℝ) hy hz)
    _ = _ := by
      rw [integral_cubePoint]
      apply integral_congr_ae
      filter_upwards [cube_ae_mem n] with x hx
      rw [compactify_gradient_on_cube s f hx, compactify_gradient_on_cube s g hx,
        gradientPairing_pullback, ContinuousLinearEquiv.apply_symm_apply]

/-- Coercive inversion produces the genuine periodic weak elliptic equation. -/
theorem potential_equation (ρ : Point n →ᵇ ℝ)
    (ℓ : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)
    {a : ℝ} (ha : 0 < a) (hp : ∀ᵐ y ∂cubePoint, a ≤ ρ y)
    (s : Finset ((Fin n → ℤ) × Bool)) (ψ : frequencySpace s) :
    ℓ (trialGradient s ψ) = ∫ x, ρ ((coordinateEquiv n).symm x) *
      ∑ i : Fin n, coordinatePartial (potential ρ ℓ s).val i x *
        coordinatePartial ψ.val i x ∂cube n := by
  have he := GalerkinApproximation.solution_equation (trialSpace s)
    (weightedOperator cubePoint ρ) (TangentEnergy.rieszRepresentative ℓ) ha
    (WeightedGalerkin.weightedOperator_lower_bound cubePoint ρ hp)
    ⟨trialGradient s ψ, ⟨ψ, rfl⟩⟩
  rw [TangentEnergy.inner_rieszRepresentative] at he
  rw [← he]
  change ⟪weightedOperator cubePoint ρ (vector ρ ℓ s), trialGradient s ψ⟫_ℝ = _
  rw [← gradient_potential, weightedOperator_trialGradient_inner]

/-- Uniform second-derivative control for the constructed Fourier optimizer.
The source hypothesis is its natural distributional pairing with the trial
functions; the elliptic equation and smooth optimizer are conclusions of the
construction, not assumptions. -/
theorem potential_hessian_bound (ρ : Point n →ᵇ ℝ)
    (ℓ : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)
    (s : Finset ((Fin n → ℤ) × Bool)) {σ : Coordinates n → ℝ} {a B : ℝ}
    (ha : 0 < a) (hp : ∀ y, a ≤ ρ y)
    (hρ : ContDiff ℝ 2 (fun x => ρ ((coordinateEquiv n).symm x)))
    (hpρ : Periodic (fun x => ρ ((coordinateEquiv n).symm x)))
    (hΔρ : ∀ᵐ x ∂cube n,
      PeriodicIntegrationByParts.laplacian (fun x => ρ ((coordinateEquiv n).symm x)) x ≤ B)
    (hσ : ContDiff ℝ 1 σ) (hpσ : Periodic σ)
    (hsource : ∀ ψ : frequencySpace s,
      ℓ (trialGradient s ψ) = ∫ x, σ x * ψ.val x ∂cube n) :
    (∫ x, hessianSquare (potential ρ ℓ s).val x ∂cube n) ≤
      ((B + 1) * (∫ x, gradientSquare (potential ρ ℓ s).val x ∂cube n) +
        (∫ x, gradientSquare σ x ∂cube n)) / (2 * a) := by
  apply galerkin_hessian_bound s ha hρ hpρ
    (Filter.Eventually.of_forall (fun x => hp ((coordinateEquiv n).symm x)))
    hΔρ hσ hpσ (potential ρ ℓ s).property
  intro ψ hψ
  rw [← hsource ⟨ψ, hψ⟩]
  exact potential_equation ρ ℓ ha (Filter.Eventually.of_forall hp) s ⟨ψ, hψ⟩

/-- The inherited Hilbert norm is exactly the unweighted periodic Dirichlet integral. -/
theorem trialGradient_norm_sq (s : Finset ((Fin n → ℤ) × Bool)) (f : frequencySpace s) :
    ‖trialGradient s f‖ ^ 2 = ∫ x, gradientSquare f.val x ∂cube n := by
  change ‖testGradient cubePoint (compactify s f)‖ ^ 2 = _
  rw [testGradient_norm_sq, integral_cubePoint]
  apply integral_congr_ae
  filter_upwards [cube_ae_mem n] with x hx
  rw [compactify_gradient_on_cube s f hx, gradientSquare_pullback,
    ContinuousLinearEquiv.apply_symm_apply]

/-- Coercivity gives a uniform first-derivative estimate for the constructed optimizer. -/
theorem vector_norm_le (ρ : Point n →ᵇ ℝ)
    (ℓ : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)
    {a : ℝ} (ha : 0 < a) (hp : ∀ᵐ y ∂cubePoint, a ≤ ρ y)
    (s : Finset ((Fin n → ℤ) × Bool)) : ‖vector ρ ℓ s‖ ≤ ‖ℓ‖ / a := by
  have he := GalerkinApproximation.solution_equation (trialSpace s)
    (weightedOperator cubePoint ρ) (TangentEnergy.rieszRepresentative ℓ) ha
    (WeightedGalerkin.weightedOperator_lower_bound cubePoint ρ hp)
    (GalerkinApproximation.solution (trialSpace s) (weightedOperator cubePoint ρ)
      (TangentEnergy.rieszRepresentative ℓ))
  rw [TangentEnergy.inner_rieszRepresentative] at he
  change ⟪weightedOperator cubePoint ρ (vector ρ ℓ s), vector ρ ℓ s⟫_ℝ = ℓ (vector ρ ℓ s) at he
  have hb := WeightedGalerkin.weightedOperator_lower_bound cubePoint ρ hp (vector ρ ℓ s)
  rw [he] at hb
  have hf : ℓ (vector ρ ℓ s) ≤ ‖ℓ‖ * ‖vector ρ ℓ s‖ :=
    (le_abs_self _).trans (ℓ.le_opNorm _)
  by_cases hz : ‖vector ρ ℓ s‖ = 0
  · rw [hz]
    positivity
  · have hpos : 0 < ‖vector ρ ℓ s‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    apply (le_div_iff₀ ha).mpr
    nlinarith

/-- Actual uniform `H²` control now depends only on data, not on the trial vector. -/
theorem potential_hessian_bound_uniform (ρ : Point n →ᵇ ℝ)
    (ℓ : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)
    (s : Finset ((Fin n → ℤ) × Bool)) {σ : Coordinates n → ℝ} {a B : ℝ}
    (ha : 0 < a) (hB : 0 ≤ B) (hp : ∀ y, a ≤ ρ y)
    (hρ : ContDiff ℝ 2 (fun x => ρ ((coordinateEquiv n).symm x)))
    (hpρ : Periodic (fun x => ρ ((coordinateEquiv n).symm x)))
    (hΔρ : ∀ᵐ x ∂cube n,
      PeriodicIntegrationByParts.laplacian (fun x => ρ ((coordinateEquiv n).symm x)) x ≤ B)
    (hσ : ContDiff ℝ 1 σ) (hpσ : Periodic σ)
    (hsource : ∀ ψ : frequencySpace s,
      ℓ (trialGradient s ψ) = ∫ x, σ x * ψ.val x ∂cube n) :
    (∫ x, hessianSquare (potential ρ ℓ s).val x ∂cube n) ≤
      ((B + 1) * (‖ℓ‖ / a) ^ 2 + (∫ x, gradientSquare σ x ∂cube n)) / (2 * a) := by
  have hn := vector_norm_le ρ ℓ ha (Filter.Eventually.of_forall hp) s
  have hg : (∫ x, gradientSquare (potential ρ ℓ s).val x ∂cube n) ≤ (‖ℓ‖ / a) ^ 2 := by
    rw [← trialGradient_norm_sq, gradient_potential]
    exact pow_le_pow_left₀ (norm_nonneg _) hn 2
  apply (potential_hessian_bound ρ ℓ s ha hp hρ hpρ hΔρ hσ hpσ hsource).trans
  apply div_le_div_of_nonneg_right _ (by positivity : 0 ≤ 2 * a)
  have hm := mul_le_mul_of_nonneg_left hg (show 0 ≤ B + 1 by positivity)
  linarith

end SharpWasserstein.PeriodicGalerkin
