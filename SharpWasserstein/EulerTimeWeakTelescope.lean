module

public import SharpWasserstein.Compat
public import SharpWasserstein.EulerTimeWeakStep

@[expose] public section

/-! Telescoping the proved Gaussian weak step along the actual Euler histories. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators
namespace SharpWasserstein.EulerTimeWeak

theorem expectation_zero {d N : ℕ} (μ : Measure (Configuration d N))
    (b : ℝ → Configuration d N → Configuration d N) (hb : ∀ t, Measurable (b t)) (δ : ℝ≥0)
    {f : Configuration d N → ℝ} (hf : Continuous f) :
    expectation μ b hb δ 0 f = ∫ x, f x ∂μ := by
  have hf' : Measurable (fun h : GaussianHistory (Configuration d N) (N*d) 0 => f (state 0 h)) :=
    hf.measurable.comp (state_measurable 0)
  unfold expectation law
  rw [gaussianHistoryLaw, gaussianInitialHistory,
    integral_map (by fun_prop : Measurable (fun x : Configuration d N =>
      (x, fun i : Fin 0 => (Fin.elim0 i : Position (N*d))))).aemeasurable
      hf'.aestronglyMeasurable]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    simp only [state, configurationEulerObservation, gaussianHistoryCurrent, id_eq,
      MeasurableEquiv.symm_apply_apply]

theorem expectation_eq_brownian_node {d N : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    (b : ℝ → Configuration d N → Configuration d N) (hb : ∀ t, Measurable (b t))
    (δ : ℝ≥0) (j : ℕ) (hj : (j : ℝ)*δ ≤ T)
    {f : Configuration d N → ℝ} (hf : Continuous f) :
    expectation μ b hb δ j f =
      ∫ p : Configuration d N × C(Icc 0 T, Configuration d N),
        f (Euler.nodes b p.1 (BoundedFlow.noiseExtension hT p.2) δ j)
          ∂μ.prod (BrownianNoise.configurationLaw d N T) := by
  have hg := configurationEuler_brownian_grid_hasLaw hT δ.coe_nonneg j hj μ id measurable_id
    (fun _ => b) (fun t => (hb t).comp measurable_snd)
  have hv : (NNReal.mk (2*(δ : ℝ)) (by positivity)) = 2*δ := by apply NNReal.eq; rfl
  have hg' : HasLaw (fun p : Configuration d N × C(Icc 0 T, Configuration d N) =>
      Euler.nodes b p.1 (BoundedFlow.noiseExtension hT p.2) δ j)
      ((law μ b hb δ j).map (state j)) (μ.prod (BrownianNoise.configurationLaw d N T)) := by
    simpa only [law,mean,state,hv,id_eq] using hg
  calc
    _ = ∫ y, f y ∂(law μ b hb δ j).map (state j) :=
      (integral_map (state_measurable j).aemeasurable hf.aestronglyMeasurable).symm
    _ = ∫ y, f y ∂(μ.prod (BrownianNoise.configurationLaw d N T)).map
        (fun p => Euler.nodes b p.1 (BoundedFlow.noiseExtension hT p.2) δ j) := by rw [hg'.map_eq]
    _ = _ := integral_map hg'.aemeasurable hf.aestronglyMeasurable

theorem expectation_telescope_error {d N : ℕ} (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    (b : ℝ → Configuration d N → Configuration d N) (hb : ∀ t, Continuous (b t)) (M : ℝ≥0)
    (hbound : ∀ t x, ‖b t x‖ ≤ M) {φ : Configuration d N → ℝ} (hφ : SmoothCompactTest φ) :
    ∃ C : ℝ≥0, ∀ (δ : ℝ≥0) (n : ℕ),
      ‖expectation μ b (fun t => (hb t).measurable) δ n φ - (∫ x, φ x ∂μ) -
        (δ : ℝ)*∑ j ∈ Finset.range n, expectation μ b (fun t => (hb t).measurable) δ j (generator (b ((j : ℝ)*δ)) φ)‖ ≤
      (n : ℝ)*δ*C*((M : ℝ)*δ+Real.sqrt (2*δ)*FrozenGaussian.noiseFirstMoment d N) := by
  obtain ⟨C,hC⟩ := expectation_step_error μ b hb M hbound hφ
  refine ⟨C, ?_⟩
  intro δ n
  induction n with
  | zero => simp [expectation_zero μ b (fun t => (hb t).measurable) δ hφ.1.continuous]
  | succ n ih =>
    let e := fun j => expectation μ b (fun t => (hb t).measurable) δ j φ
    let g := fun j => expectation μ b (fun t => (hb t).measurable) δ j (generator (b ((j : ℝ)*δ)) φ)
    have he : expectation μ b (fun t => (hb t).measurable) δ (n+1) φ - (∫ x, φ x ∂μ) -
        (δ : ℝ)*∑ j ∈ Finset.range (n+1), expectation μ b (fun t => (hb t).measurable) δ j (generator (b ((j : ℝ)*δ)) φ) =
        (e (n+1)-e n-(δ : ℝ)*g n) +
          (e n-(∫ x, φ x ∂μ)-(δ : ℝ)*∑ j ∈ Finset.range n, g j) := by
      rw [Finset.sum_range_succ]
      dsimp [e,g]
      ring
    rw [he]
    calc
      _ ≤ ‖e (n+1)-e n-(δ : ℝ)*g n‖ +
          ‖e n-(∫ x, φ x ∂μ)-(δ : ℝ)*∑ j ∈ Finset.range n, g j‖ := norm_add_le _ _
      _ ≤ (δ : ℝ)*C*((M : ℝ)*δ+Real.sqrt (2*δ)*FrozenGaussian.noiseFirstMoment d N) +
          (n : ℝ)*δ*C*((M : ℝ)*δ+Real.sqrt (2*δ)*FrozenGaussian.noiseFirstMoment d N) :=
        add_le_add (hC δ n) ih
      _ = _ := by push_cast; ring

end SharpWasserstein.EulerTimeWeak
