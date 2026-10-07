module

public import SharpWasserstein.Compat
public import SharpWasserstein.EulerianTransportLength
public import SharpWasserstein.BoundedConfigurationTests

@[expose] public section

/-! Compact smooth tests suffice for the regular Eulerian transport theorem.
Actual compact cutoffs converge locally together with their first derivatives;
dominated convergence passes both endpoint and time-space drift integrals. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal ContDiff InnerProductSpace Interval
namespace SharpWasserstein.EulerianTransport
open NoiseAverage WeightedTangent
variable {d N : ℕ}

/-- Actual compact smooth approximants have common value/derivative bounds and
are eventually equal to the original test near every point. -/
theorem exists_compact_test_approximation {φ : Configuration d N → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hB : AllDerivativesBounded φ) :
    ∃ (ψ : ℕ → Configuration d N → ℝ) (A D : ℝ), 0 ≤ A ∧ 0 ≤ D ∧
      (∀ j, SmoothCompactTest (ψ j)) ∧ (∀ j x, ‖ψ j x‖ ≤ A) ∧
      (∀ j x, ‖fderiv ℝ (ψ j) x‖ ≤ D) ∧
      (∀ x, ∀ᶠ j in atTop, ψ j x = φ x ∧ fderiv ℝ (ψ j) x = fderiv ℝ φ x) := by
  let f := euclideanTest φ
  have hf : ContDiff ℝ ∞ f := hφ.comp (configurationEuclidean d N).symm.contDiff
  have hfB := allDerivativesBounded_euclideanTest hφ hB
  obtain ⟨A,hA,hfA⟩ := hfB.bounded
  obtain ⟨B,hB₀,hfB₁⟩ := hfB.fderiv.bounded
  have hgrad : ∀ y, ‖gradient f y‖ ≤ B := by
    intro y
    rw [SmoothCutoff.norm_gradient_eq_fderiv]
    exact hfB₁ y
  let ψ : ℕ → Configuration d N → ℝ := fun j =>
    (SmoothCutoff.approximate f hf j : Point (N*d) → ℝ) ∘ configurationEuclidean d N
  let C : ℝ := B+A*(SmoothCutoff.baseLipschitzConstant (N*d):ℝ)
  let D : ℝ := C*‖(configurationEuclidean d N).toContinuousLinearMap‖
  have hfabs : ∀ y, |f y| ≤ A := by simpa only [Real.norm_eq_abs] using hfA
  refine ⟨ψ,A,D,hA,by dsimp [D,C]; positivity,fun j => smoothCompactTest_pullback _,?_,?_,?_⟩
  · intro j x
    simpa only [ψ,Function.comp_apply,Real.norm_eq_abs] using
      SmoothCutoff.approximate_abs_bound f hf hfabs j (configurationEuclidean d N x)
  · intro j x
    change ‖fderiv ℝ ((SmoothCutoff.approximate f hf j : Point (N*d) → ℝ) ∘
      configurationEuclidean d N) x‖ ≤ D
    rw [(configurationEuclidean d N).comp_right_fderiv]
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    rw [← SmoothCutoff.norm_gradient_eq_fderiv]
    exact SmoothCutoff.approximate_gradient_bound f hf hA hfabs hgrad j _
  · intro x
    filter_upwards [SmoothCutoff.cutoff_eventuallyEq_one (configurationEuclidean d N x)] with j hj
    have hj' := hj.comp_tendsto (configurationEuclidean d N).continuous.continuousAt.tendsto
    have he : ψ j =ᶠ[𝓝 x] φ := by
      filter_upwards [hj'] with y hy
      change SmoothCutoff.cutoff (N*d) j (configurationEuclidean d N y) = 1 at hy
      change SmoothCutoff.cutoff (N*d) j (configurationEuclidean d N y)*f (configurationEuclidean d N y) = φ y
      rw [hy,one_mul]
      exact euclideanTest_apply φ y
    exact ⟨he.eq_of_nhds,he.fderiv_eq⟩

/-- The standard compact-smooth spatial-test continuity equation on a finite horizon. -/
structure CompactWeakContinuity (v : ℝ → Configuration d N → Configuration d N)
    (μ : ℝ → ProbabilityMeasure (Configuration d N)) (T : ℝ) : Prop where
  continuous : Continuous μ
  equation : ∀ φ : Configuration d N → ℝ, SmoothCompactTest φ →
    ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T,
      IntervalIntegrable (fun r => ∫ x, generator (v r) φ x ∂(μ r : Measure _)) volume s t ∧
      (∫ x, φ x ∂(μ t : Measure _))-(∫ x, φ x ∂(μ s : Measure _)) =
        ∫ r in s..t, ∫ x, generator (v r) φ x ∂(μ r : Measure _)

/-- Compact-test weak solutions satisfy the bounded-test equation used for
characteristic uniqueness. Bounds and both limiting integral passages are proved. -/
theorem CompactWeakContinuity.toWeakContinuity
    {v : ℝ → Configuration d N → Configuration d N}
    {μ : ℝ → ProbabilityMeasure (Configuration d N)} {T : ℝ}
    (h : CompactWeakContinuity v μ T) (hv : Continuous (Function.uncurry v))
    {M : ℝ≥0} (hM : ∀ t x, ‖v t x‖ ≤ M) : WeakContinuity v μ T := by
  refine ⟨h.continuous,?_⟩
  intro φ hφ hB s hs t ht
  obtain ⟨ψ,A,D,hA,hD,hψ,hψA,hψD,hlim⟩ := exists_compact_test_approximation hφ hB
  have hφD (x : Configuration d N) : ‖fderiv ℝ φ x‖ ≤ D := by
    obtain ⟨j,hj⟩ := (hlim x).exists
    rw [← hj.2]
    exact hψD j x
  have hGbound (j : ℕ) (r : ℝ) (x : Configuration d N) :
      ‖generator (v r) (ψ j) x‖ ≤ D*(M:ℝ) :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul (hψD j x) (hM r x) (norm_nonneg _) hD)
  have hGφbound (r : ℝ) (x : Configuration d N) : ‖generator (v r) φ x‖ ≤ D*(M:ℝ) :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul (hφD x) (hM r x) (norm_nonneg _) hD)
  have hGc (j : ℕ) : Continuous (fun p : ℝ × Configuration d N => generator (v p.1) (ψ j) p.2) :=
    (((hψ j).1.continuous_fderiv (by simp)).comp continuous_snd).clm_apply hv
  have hGφc : Continuous (fun p : ℝ × Configuration d N => generator (v p.1) φ p.2) :=
    ((hφ.continuous_fderiv (by simp)).comp continuous_snd).clm_apply hv
  have hGEc (j : ℕ) : Continuous (fun r => ∫ x, generator (v r) (ψ j) x ∂(μ r : Measure _)) :=
    continuous_integral_parameter_probability μ h.continuous _ (hGc j) (fun p => hGbound j p.1 p.2)
  have hGφEc : Continuous (fun r => ∫ x, generator (v r) φ x ∂(μ r : Measure _)) :=
    continuous_integral_parameter_probability μ h.continuous _ hGφc (fun p => hGφbound p.1 p.2)
  have hGEnorm (j : ℕ) (r : ℝ) :
      ‖∫ x, generator (v r) (ψ j) x ∂(μ r : Measure _)‖ ≤ D*(M:ℝ) := by
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
      (μ := (μ r : Measure _)) (Eventually.of_forall (hGbound j r))
  have hvallim (r : ℝ) : Tendsto (fun j => ∫ x, ψ j x ∂(μ r : Measure _)) atTop
      (𝓝 (∫ x, φ x ∂(μ r : Measure _))) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => A)
      (fun j => (hψ j).1.continuous.aestronglyMeasurable) (integrable_const _) ?_ ?_
    · intro j
      exact Eventually.of_forall (hψA j)
    · filter_upwards [] with x
      exact tendsto_const_nhds.congr' ((hlim x).mono (fun _ hj => hj.1.symm))
  have hgenlim (r : ℝ) : Tendsto (fun j => ∫ x, generator (v r) (ψ j) x ∂(μ r : Measure _)) atTop
      (𝓝 (∫ x, generator (v r) φ x ∂(μ r : Measure _))) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => D*(M:ℝ))
      (fun j => ((hGc j).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
      (integrable_const _) ?_ ?_
    · intro j
      exact Eventually.of_forall (hGbound j r)
    · filter_upwards [] with x
      apply tendsto_const_nhds.congr'
      filter_upwards [hlim x] with j hj
      simp only [generator,Function.comp_apply,id_eq,hj.2]
  have htimelim : Tendsto (fun j => ∫ r in s..t, ∫ x, generator (v r) (ψ j) x ∂(μ r : Measure _))
      atTop (𝓝 (∫ r in s..t, ∫ x, generator (v r) φ x ∂(μ r : Measure _))) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => D*(M:ℝ))
    · exact Eventually.of_forall (fun j => (hGEc j).aestronglyMeasurable)
    · exact Eventually.of_forall (fun j => Eventually.of_forall fun r _ => hGEnorm j r)
    · exact intervalIntegrable_const
    · exact Eventually.of_forall (fun r _ => hgenlim r)
  refine ⟨hGφEc.intervalIntegrable s t,?_⟩
  apply tendsto_nhds_unique ((hvallim t).sub (hvallim s))
  apply htimelim.congr'
  exact Eventually.of_forall (fun j => (h.equation (ψ j) (hψ j) s hs t ht).2.symm)

/-- The regular Wasserstein bound follows from the genuine compact-test
Eulerian equation, not from an assumed characteristic representation. -/
theorem CompactWeakContinuity.wassersteinSq_le_action
    {v : ℝ → Configuration d N → Configuration d N}
    {μ : ℝ → ProbabilityMeasure (Configuration d N)} {T : ℝ}
    (h : CompactWeakContinuity v μ T) {M K K₁ : ℝ≥0}
    (hv : Continuous (Function.uncurry v)) (hb : ∀ t x, ‖v t x‖ ≤ M)
    (hl : ∀ t, LipschitzWith K (v t)) (hT : 0 ≤ T)
    (hvs : ∀ t, ContDiff ℝ ∞ (v t)) (hvB : ∀ t, AllDerivativesBounded (v t))
    (hv₁ : ∀ t, LipschitzWith K₁ (fderiv ℝ (v t)))
    (hP : HasSecondMoment (μ 0 : Measure (Configuration d N)))
    {a b : ℝ} (ha : a ∈ Icc 0 T) (hbT : b ∈ Icc 0 T) (hab : a ≤ b) :
    wassersteinSq (μ a : Measure (Configuration d N)) (μ b : Measure (Configuration d N)) ≤
      ENNReal.ofReal ((∫ t in a..b, Real.sqrt (∫ x, productCost (v t x) 0
        ∂(μ t : Measure (Configuration d N)))) ^ 2) :=
  (h.toWeakContinuity hv hb).wassersteinSq_le_action hv hb hl hT hvs hvB hv₁ hP ha hbT hab

/-- The compact-test equation identifies the law with the actual constructed
characteristic pushforward, including singular initial probability laws. -/
theorem CompactWeakContinuity.eq_flowLaw
    {v : ℝ → Configuration d N → Configuration d N}
    {μ : ℝ → ProbabilityMeasure (Configuration d N)} {T : ℝ}
    (h : CompactWeakContinuity v μ T) {M K K₁ : ℝ≥0}
    (hv : Continuous (Function.uncurry v)) (hb : ∀ t x, ‖v t x‖ ≤ M)
    (hl : ∀ t, LipschitzWith K (v t)) (hT : 0 ≤ T)
    (hvs : ∀ t, ContDiff ℝ ∞ (v t)) (hvB : ∀ t, AllDerivativesBounded (v t))
    (hv₁ : ∀ t, LipschitzWith K₁ (fderiv ℝ (v t)))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    μ t = flowLaw hv hb hl hT (μ 0 : Measure (Configuration d N)) t :=
  (h.toWeakContinuity hv hb).eq_flowLaw hv hb hl hT hvs hvB hv₁ ht

/-- The real W₂ length estimate for a genuine compact-test Eulerian solution. -/
theorem CompactWeakContinuity.wasserstein_length_le_action
    {v : ℝ → Configuration d N → Configuration d N}
    {μ : ℝ → ProbabilityMeasure (Configuration d N)} {T : ℝ}
    (h : CompactWeakContinuity v μ T) {M K K₁ : ℝ≥0}
    (hv : Continuous (Function.uncurry v)) (hb : ∀ t x, ‖v t x‖ ≤ M)
    (hl : ∀ t, LipschitzWith K (v t)) (hT : 0 ≤ T)
    (hvs : ∀ t, ContDiff ℝ ∞ (v t)) (hvB : ∀ t, AllDerivativesBounded (v t))
    (hv₁ : ∀ t, LipschitzWith K₁ (fderiv ℝ (v t)))
    (hP : HasSecondMoment (μ 0 : Measure (Configuration d N)))
    {a b : ℝ} (ha : a ∈ Icc 0 T) (hbT : b ∈ Icc 0 T) (hab : a ≤ b) :
    Real.sqrt (wassersteinSq (μ a : Measure (Configuration d N))
      (μ b : Measure (Configuration d N))).toReal ≤
      ∫ t in a..b, Real.sqrt (∫ x, productCost (v t x) 0
        ∂(μ t : Measure (Configuration d N))) :=
  (h.toWeakContinuity hv hb).wasserstein_length_le_action hv hb hl hT hvs hvB hv₁ hP ha hbT hab

end SharpWasserstein.EulerianTransport
