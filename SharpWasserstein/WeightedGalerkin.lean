import SharpWasserstein.GalerkinApproximation

/-! Genuine smooth test-potential Galerkin approximations of the constructed
weighted elliptic optimizer. The limiting optimizer is not assumed smooth.
These approximations converge in weighted energy, but this alone does not
control their Hessians or justify applying a PDE generator outside a trial space. -/

noncomputable section
namespace SharpWasserstein.WeightedGalerkin
open MeasureTheory Set Filter WeightedTangent WeightedDensity WeightedEnergyDerivative
open scoped InnerProductSpace Topology BoundedContinuousFunction

variable {d : ℕ} [MeasurableSpace (Point d)] [BorelSpace (Point d)]
variable (μ : Measure (Point d)) [IsFiniteMeasure μ]

/-- A finite-dimensional space of actual compact smooth gradients. -/
def testSpan (s : Finset (Test d)) : Submodule ℝ (gradientClosure μ) :=
  Submodule.span ℝ ((gradientIntoClosure μ) '' (s : Set (Test d)))

instance testSpan_finiteDimensional (s : Finset (Test d)) :
    FiniteDimensional ℝ (testSpan μ s) :=
  FiniteDimensional.span_of_finite ℝ (s.finite_toSet.image _)

instance testSpan_complete (s : Finset (Test d)) : CompleteSpace (testSpan μ s) :=
  FiniteDimensional.complete ℝ _

/-- Every vector in the trial space is the gradient of an actual smooth compact test. -/
theorem testSpan_le_range (s : Finset (Test d)) :
    testSpan μ s ≤ (gradientIntoClosure μ).range := by
  apply Submodule.span_le.mpr
  rintro _ ⟨φ, _, rfl⟩
  exact LinearMap.mem_range_self _ φ

/-- Actual Galerkin optimizer in the closed gradient space. -/
def galerkinVector (ρ : Point d →ᵇ ℝ) (ℓ : gradientClosure μ →L[ℝ] ℝ)
    (s : Finset (Test d)) : gradientClosure μ :=
  GalerkinApproximation.solution (testSpan μ s) (weightedOperator μ ρ)
    (TangentEnergy.rieszRepresentative ℓ)

/-- An actual compact smooth potential whose gradient is the Galerkin optimizer. -/
def galerkinPotential (ρ : Point d →ᵇ ℝ) (ℓ : gradientClosure μ →L[ℝ] ℝ)
    (s : Finset (Test d)) : Test d :=
  Classical.choose (testSpan_le_range μ s
    (GalerkinApproximation.solution (testSpan μ s) (weightedOperator μ ρ)
      (TangentEnergy.rieszRepresentative ℓ)).property)

theorem gradient_galerkinPotential (ρ : Point d →ᵇ ℝ) (ℓ : gradientClosure μ →L[ℝ] ℝ)
    (s : Finset (Test d)) :
    gradientIntoClosure μ (galerkinPotential μ ρ ℓ s) = galerkinVector μ ρ ℓ s :=
  Classical.choose_spec (testSpan_le_range μ s
    (GalerkinApproximation.solution (testSpan μ s) (weightedOperator μ ρ)
      (TangentEnergy.rieszRepresentative ℓ)).property)

/-- The exact lower bound of the density is inherited by the actual operator. -/
theorem weightedOperator_lower_bound (ρ : Point d →ᵇ ℝ) {a : ℝ}
    (hρ : ∀ᵐ x ∂μ, a ≤ ρ x) (v : gradientClosure μ) :
    a * ‖v‖ ^ 2 ≤ ⟪weightedOperator μ ρ v, v⟫_ℝ := by
  rw [weightedOperator_inner]
  simp_rw [real_inner_self_eq_norm_sq]
  have hi : Integrable (fun x => ‖(v : Lp (Point d) 2 μ) x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (v : Lp (Point d) 2 μ))).mp
      (Lp.memLp (v : Lp (Point d) 2 μ))
  have hρi := integrable_weighted_inner μ ρ v v
  simp_rw [real_inner_self_eq_norm_sq] at hρi
  calc
    _ = ∫ x, a * ‖(v : Lp (Point d) 2 μ) x‖ ^ 2 ∂μ := by
      rw [integral_const_mul, ← lp_norm_sq_eq_integral]
      rfl
    _ ≤ _ := integral_mono_ae (hi.const_mul a) hρi (hρ.mono fun x hx =>
      mul_le_mul_of_nonneg_right hx (sq_nonneg _))

/-- Every trial test satisfies the genuine weighted elliptic equation. -/
theorem galerkin_equation (ρ : Point d →ᵇ ℝ) (ℓ : gradientClosure μ →L[ℝ] ℝ)
    {a : ℝ} (ha : 0 < a) (hρ : ∀ᵐ x ∂μ, a ≤ ρ x)
    (s : Finset (Test d)) (φ : Test d) (hφ : gradientIntoClosure μ φ ∈ testSpan μ s) :
    ℓ (gradientIntoClosure μ φ) = ∫ x, ρ x *
      ⟪gradient (galerkinPotential μ ρ ℓ s : Point d → ℝ) x,
        gradient (φ : Point d → ℝ) x⟫_ℝ ∂μ := by
  have he := GalerkinApproximation.solution_equation (testSpan μ s) (weightedOperator μ ρ)
    (TangentEnergy.rieszRepresentative ℓ) ha (weightedOperator_lower_bound μ ρ hρ)
    ⟨gradientIntoClosure μ φ, hφ⟩
  rw [TangentEnergy.inner_rieszRepresentative] at he
  rw [← he]
  change ⟪weightedOperator μ ρ (galerkinVector μ ρ ℓ s), gradientIntoClosure μ φ⟫_ℝ = _
  rw [← gradient_galerkinPotential, weightedOperator_inner]
  apply integral_congr_ae
  filter_upwards [testGradient_ae μ (galerkinPotential μ ρ ℓ s), testGradient_ae μ φ] with x hx hy
  exact congrArg (fun q : ℝ => ρ x * q) (congrArg₂ (inner ℝ) hx hy)

/-- Céa convergence bound for a genuine smooth trial potential. -/
theorem galerkin_error_le (ρ : Point d →ᵇ ℝ) (ℓ : gradientClosure μ →L[ℝ] ℝ)
    {a : ℝ} (ha : 0 < a) (hρ : ∀ᵐ x ∂μ, a ≤ ρ x)
    (s : Finset (Test d)) (φ : Test d) (hφ : gradientIntoClosure μ φ ∈ testSpan μ s) :
    ‖densitySolution μ ρ ℓ - galerkinVector μ ρ ℓ s‖ ≤
      (‖weightedOperator μ ρ‖ / a) * ‖densitySolution μ ρ ℓ - gradientIntoClosure μ φ‖ :=
  GalerkinApproximation.solution_error_le (testSpan μ s) (weightedOperator μ ρ)
    (TangentEnergy.rieszRepresentative ℓ) (densitySolution μ ρ ℓ) ha
    (weightedOperator_lower_bound μ ρ hρ) (densitySolution_equation μ ρ ℓ ha hρ)
    ⟨gradientIntoClosure μ φ, hφ⟩

/-- Refining all finite smooth test spaces converges strongly to the constructed optimizer. -/
theorem galerkinVector_tendsto (ρ : Point d →ᵇ ℝ) (ℓ : gradientClosure μ →L[ℝ] ℝ)
    {a : ℝ} (ha : 0 < a) (hρ : ∀ᵐ x ∂μ, a ≤ ρ x) :
    Tendsto (galerkinVector μ ρ ℓ) atTop (𝓝 (densitySolution μ ρ ℓ)) := by
  classical
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let C := ‖weightedOperator μ ρ‖ / a
  have hC : 0 ≤ C := div_nonneg (ContinuousLinearMap.opNorm_nonneg _) ha.le
  obtain ⟨φ, hφ⟩ := (dense_gradientIntoClosure μ).exists_dist_lt (densitySolution μ ρ ℓ)
    (show 0 < ε / (C + 1) from div_pos hε (by positivity))
  refine ⟨{φ}, fun s hs => ?_⟩
  have hmem : gradientIntoClosure μ φ ∈ testSpan μ s :=
    Submodule.subset_span ⟨φ, hs (by simp), rfl⟩
  have he := galerkin_error_le μ ρ ℓ ha hρ s φ hmem
  rw [dist_eq_norm] at hφ
  rw [dist_eq_norm, norm_sub_rev]
  calc
    _ ≤ C * ‖densitySolution μ ρ ℓ - gradientIntoClosure μ φ‖ := he
    _ ≤ (C + 1) * ‖densitySolution μ ρ ℓ - gradientIntoClosure μ φ‖ := by
      gcongr
      linarith
    _ < ε := by
      have := (lt_div_iff₀ (show 0 < C + 1 by positivity)).mp hφ
      nlinarith

/-- The exact finite trial energy converges to the actual compact-test variational energy. -/
theorem galerkinEnergy_tendsto (ρ : Point d →ᵇ ℝ) (ℓ : gradientClosure μ →L[ℝ] ℝ)
    {a : ℝ} (ha : 0 < a) (hρ : ∀ᵐ x ∂μ, a ≤ ρ x) :
    Tendsto (fun s => ℓ (galerkinVector μ ρ ℓ s)) atTop (𝓝 (densityEnergy μ ρ ℓ)) := by
  rw [densityEnergy_eq_solution μ ρ ℓ ha hρ]
  exact ℓ.continuous.continuousAt.tendsto.comp (galerkinVector_tendsto μ ρ ℓ ha hρ)

/-- The finite trial energy is exactly the actual density-weighted squared gradient
of the smooth potential constructed by Galerkin inversion. -/
theorem galerkinEnergy_eq_integral (ρ : Point d →ᵇ ℝ) (ℓ : gradientClosure μ →L[ℝ] ℝ)
    {a : ℝ} (ha : 0 < a) (hρ : ∀ᵐ x ∂μ, a ≤ ρ x) (s : Finset (Test d)) :
    ℓ (galerkinVector μ ρ ℓ s) = ∫ x, ρ x *
      ‖gradient (galerkinPotential μ ρ ℓ s : Point d → ℝ) x‖ ^ 2 ∂μ := by
  have hm : gradientIntoClosure μ (galerkinPotential μ ρ ℓ s) ∈ testSpan μ s := by
    rw [gradient_galerkinPotential]
    exact (GalerkinApproximation.solution (testSpan μ s) (weightedOperator μ ρ)
      (TangentEnergy.rieszRepresentative ℓ)).property
  have he := galerkin_equation μ ρ ℓ ha hρ s (galerkinPotential μ ρ ℓ s) hm
  simpa only [gradient_galerkinPotential, real_inner_self_eq_norm_sq] using he

/-- The finite optimizer's own test attains precisely its true variational objective. -/
theorem galerkinEnergy_eq_objective (ρ : Point d →ᵇ ℝ) (ℓ : gradientClosure μ →L[ℝ] ℝ)
    {a : ℝ} (ha : 0 < a) (hρ : ∀ᵐ x ∂μ, a ≤ ρ x) (s : Finset (Test d)) :
    densityTestObjective μ ρ ℓ (galerkinPotential μ ρ ℓ s) = ℓ (galerkinVector μ ρ ℓ s) := by
  unfold densityTestObjective
  rw [gradient_galerkinPotential, ← galerkinEnergy_eq_integral μ ρ ℓ ha hρ]
  ring

/-- Actual density/source differentiability implies the finite-dimensional optimized
energy formula; differentiability or smoothness of the limiting optimizer is not assumed. -/
theorem hasDerivAt_galerkinEnergy
    {ρ : ℝ → (Point d →ᵇ ℝ)} {ρ' : Point d →ᵇ ℝ}
    {ℓ : ℝ → (gradientClosure μ →L[ℝ] ℝ)} {ℓ' : gradientClosure μ →L[ℝ] ℝ}
    {t a : ℝ} (hρ : HasDerivAt ρ ρ' t) (hℓ : HasDerivAt ℓ ℓ' t)
    (ha : 0 < a) (hp : ∀ᵐ x ∂μ, a ≤ ρ t x) (s : Finset (Test d)) :
    HasDerivAt (fun r => ℓ r (galerkinVector μ (ρ r) (ℓ r) s))
      (2 * ℓ' (galerkinVector μ (ρ t) (ℓ t) s) -
        ∫ x, ρ' x * ‖(galerkinVector μ (ρ t) (ℓ t) s : Lp (Point d) 2 μ) x‖ ^ 2 ∂μ) t := by
  have hA : HasDerivAt (fun r => weightedOperator μ (ρ r)) (weightedOperator μ ρ') t :=
    HasFDerivAt.comp_hasDerivAt (F := Point d →ᵇ ℝ)
      (E := gradientClosure μ →L[ℝ] gradientClosure μ) t (weightedOperator μ).hasFDerivAt hρ
  have hf := HasFDerivAt.comp_hasDerivAt (F := gradientClosure μ →L[ℝ] ℝ)
    (E := gradientClosure μ) t (rieszMap μ).hasFDerivAt hℓ
  have h := GalerkinApproximation.hasDerivAt_energy (testSpan μ s) hA hf ha
    (weightedOperator_lower_bound μ (ρ t) hp) (weightedOperator_symmetric μ (ρ t))
  simpa only [Function.comp_apply, rieszMap_apply, TangentEnergy.inner_rieszRepresentative,
    weightedOperator_inner, real_inner_self_eq_norm_sq, galerkinVector] using h

/-- Strong Galerkin convergence also passes the actual density/source derivative
pairing to the limit. This does not assert a uniform Hessian bound. -/
theorem galerkinDerivativePairing_tendsto
    (ρ ρ' : Point d →ᵇ ℝ) (ℓ ℓ' : gradientClosure μ →L[ℝ] ℝ)
    {a : ℝ} (ha : 0 < a) (hp : ∀ᵐ x ∂μ, a ≤ ρ x) :
    Tendsto (fun s => 2 * ℓ' (galerkinVector μ ρ ℓ s) -
        ∫ x, ρ' x * ‖(galerkinVector μ ρ ℓ s : Lp (Point d) 2 μ) x‖ ^ 2 ∂μ)
      atTop (𝓝 (2 * ℓ' (densitySolution μ ρ ℓ) -
        ∫ x, ρ' x * ‖(densitySolution μ ρ ℓ : Lp (Point d) 2 μ) x‖ ^ 2 ∂μ)) := by
  have hc : Continuous (fun v : gradientClosure μ =>
      2 * ℓ' v - ⟪weightedOperator μ ρ' v, v⟫_ℝ) := by fun_prop
  have h := hc.continuousAt.tendsto.comp (galerkinVector_tendsto μ ρ ℓ ha hp)
  simpa only [Function.comp_def, weightedOperator_inner, real_inner_self_eq_norm_sq] using h

end SharpWasserstein.WeightedGalerkin
