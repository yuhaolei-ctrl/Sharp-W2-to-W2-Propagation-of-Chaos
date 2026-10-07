module

public import SharpWasserstein.Compat
public import SharpWasserstein.EulerWeakTelescope
public import SharpWasserstein.EulerRiemannExpectation

@[expose] public section

/-! Passing the genuine Gaussian Euler telescoping identity to the constructed
continuous-forcing trajectories. The noise law is the actual independent
sqrt-two Brownian law; no martingale or weak-evolution identity is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology
namespace SharpWasserstein.EulerWeak

theorem brownian_trajectory_weak_equation {d N : ℕ} {T : ℝ} (hT : 0 < T)
    (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    (b : Configuration d N → Configuration d N)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (M K : ℝ≥0)
    (hbound : ∀ x, ‖b x‖ ≤ M) (hLip : LipschitzWith K b)
    (X : ℝ → Configuration d N × C(Icc 0 T, Configuration d N) → Configuration d N)
    (htraj : ∀ p, FiniteAdditiveTrajectory (fun _ => b)
      (BoundedFlow.noiseExtension hT.le p.2) p.1 T (fun t => X t p))
    (hXm : ∀ t ∈ Icc 0 T, Measurable (X t))
    {φ : Configuration d N → ℝ} (hφ : SmoothCompactTest φ) :
    (∫ p, φ (X T p) ∂μ.prod (BrownianNoise.configurationLaw d N T)) - (∫ x, φ x ∂μ) =
      ∫ s in (0 : ℝ)..T, ∫ p, generator b φ (X s p)
        ∂μ.prod (BrownianNoise.configurationLaw d N T) := by
  let P := μ.prod (BrownianNoise.configurationLaw d N T)
  let δ : ℕ → ℝ≥0 := fun n => ⟨T/(n+1 : ℝ), by positivity⟩
  let Y := fun n (p : Configuration d N × C(Icc 0 T, Configuration d N)) =>
    Euler.nodes (fun _ => b) p.1 (BoundedFlow.noiseExtension hT.le p.2) (δ n) (n+1)
  have hw (t : ℝ) : Measurable (fun p : Configuration d N × C(Icc 0 T, Configuration d N) =>
      BoundedFlow.noiseExtension hT.le p.2 t) :=
    (continuous_eval_const (projIcc 0 T hT.le t)).measurable.comp measurable_snd
  have hYm (n : ℕ) : Measurable (Y n) :=
    Euler.nodes_measurable (fun _ => hb.continuous.measurable) measurable_fst hw _ _
  obtain ⟨B,hB0,hB⟩ := FrozenGaussian.compact_bound hφ
  have he : Tendsto (fun n => ∫ p, φ (Y n p) ∂P) atTop (𝓝 (∫ p, φ (X T p) ∂P)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => B)
    · intro n
      exact (hφ.1.continuous.measurable.comp (hYm n)).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      exact Eventually.of_forall fun p => hB _
    · exact Eventually.of_forall fun p => hφ.1.continuous.continuousAt.tendsto.comp
        (Euler.trajectory_endpoint_tendsto (htraj p) (fun _ => hLip) hT)
  obtain ⟨L,hL⟩ := CompactGenerator.generator_lipschitz hφ hb
  obtain ⟨D,hD0,hD⟩ := FrozenGaussian.compact_bound (CompactGenerator.generator_smooth hφ hb)
  have hr := Euler.expected_nodes_riemann_tendsto (P := P) htraj (fun _ => hLip) hL
    (fun z => by simpa only [Real.norm_eq_abs] using hD z) measurable_fst hw hXm hT
  let R := fun n => (∫ p, φ (Y n p) ∂P) - (∫ x, φ x ∂μ) -
    (δ n : ℝ) * ∑ j ∈ Finset.range (n+1), ∫ p : Configuration d N × C(Icc 0 T, Configuration d N),
      generator b φ (Euler.nodes (fun _ => b) p.1 (BoundedFlow.noiseExtension hT.le p.2) (δ n) j) ∂P
  have hR : Tendsto R atTop (𝓝 ((∫ p, φ (X T p) ∂P) - (∫ x, φ x ∂μ) -
      ∫ s in (0 : ℝ)..T, ∫ p, generator b φ (X s p) ∂P)) :=
    (he.sub_const _).sub hr
  obtain ⟨C,hC⟩ := expectation_telescope_error μ b hb.continuous M hbound hφ
  have herror (n : ℕ) : ‖R n‖ ≤ T*C*((M : ℝ)*δ n +
      Real.sqrt (2*(δ n : ℝ))*FrozenGaussian.noiseFirstMoment d N) := by
    have hc := hC (δ n) (n+1)
    have ht : ((n+1 : ℕ) : ℝ)*(δ n : ℝ) = T := by
      dsimp [δ]
      push_cast
      exact mul_div_cancel₀ T (by positivity)
    rw [ht] at hc
    rw [expectation_eq_brownian_node hT.le μ b hb.continuous.measurable (δ n) (n+1)
      (le_of_eq ht) hφ.1.continuous] at hc
    have hs : (∑ j ∈ Finset.range (n+1), expectation μ b hb.continuous.measurable (δ n) j (generator b φ)) =
        ∑ j ∈ Finset.range (n+1), ∫ p : Configuration d N × C(Icc 0 T, Configuration d N),
          generator b φ (Euler.nodes (fun _ => b) p.1 (BoundedFlow.noiseExtension hT.le p.2) (δ n) j) ∂P := by
      apply Finset.sum_congr rfl
      intro j hj
      exact expectation_eq_brownian_node hT.le μ b hb.continuous.measurable (δ n) j
        (Euler.grid_time_mem_Icc hT.le n j (Finset.mem_range.mp hj).le).2 hL.continuous
    rw [hs] at hc
    exact hc
  have hmesh : Tendsto (fun n => (δ n : ℝ)) atTop (𝓝 0) := by
    change Tendsto (fun n : ℕ => T/(n+1 : ℝ)) atTop (𝓝 0)
    simpa only [mul_zero,div_eq_mul_inv,one_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul T
  have herrlim : Tendsto (fun n => T*C*((M : ℝ)*δ n +
      Real.sqrt (2*(δ n : ℝ))*FrozenGaussian.noiseFirstMoment d N)) atTop (𝓝 0) := by
    simpa only [mul_zero,Real.sqrt_zero,zero_mul,zero_add] using
      ((hmesh.const_mul (M : ℝ)).add (((hmesh.const_mul 2).sqrt).mul_const
        (FrozenGaussian.noiseFirstMoment d N))).const_mul (T*C)
  have hR0 : Tendsto R atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [herrlim.eventually (gt_mem_nhds hε)] with n hn
    simpa only [dist_zero_right] using (herror n).trans_lt hn
  exact sub_eq_zero.mp (tendsto_nhds_unique hR hR0)

end SharpWasserstein.EulerWeak
