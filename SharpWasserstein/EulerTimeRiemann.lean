module

public import SharpWasserstein.Compat
public import SharpWasserstein.EulerRiemannExpectation

@[expose] public section

/-! Expected Riemann sums for the actual Euler scheme. The proof uses only
the proved pathwise approximation, bounded domination and finite-sum Fubini. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Interval Topology
namespace SharpWasserstein.EulerTime
open Euler

variable {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]
  {P : Measure Ω} [IsFiniteMeasure P]
  {v : ℝ → E → E} {w X : ℝ → Ω → E} {x : Ω → E} {T B : ℝ} {K L : ℝ≥0} {g : ℝ → E → ℝ}

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem node_sum_difference_tendsto {v : ℝ → E → E} {w X : ℝ → E} {x : E} {T : ℝ}
    {K L : ℝ≥0} {g : ℝ → E → ℝ}
    (h : FiniteAdditiveTrajectory v w x T X) (hv : ∀ t, LipschitzWith K (v t))
    (hg : ∀ t, LipschitzWith L (g t)) (hT : 0 < T) :
    Tendsto (fun n : ℕ => (T/(n+1 : ℝ)) * ∑ j ∈ Finset.range (n+1),
      (g ((j : ℝ)*(T/(n+1 : ℝ))) (nodes v x w (T/(n+1 : ℝ)) j) - g ((j : ℝ)*(T/(n+1 : ℝ))) (X ((j : ℝ)*(T/(n+1 : ℝ)))))) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hpos : 0 < 2*T*((L : ℝ)+1) := by positivity
  filter_upwards [nodes_uniform_eventually h hv hT (div_pos hε hpos)] with n hn
  have hb := scaled_sum_bound (show 0 ≤ T/(n+1 : ℝ) by positivity) (n+1)
    (fun j => g ((j : ℝ)*(T/(n+1 : ℝ))) (nodes v x w (T/(n+1 : ℝ)) j)-g ((j : ℝ)*(T/(n+1 : ℝ))) (X ((j : ℝ)*(T/(n+1 : ℝ)))))
    (fun j hj => by
      have hl := (hg ((j : ℝ)*(T/(n+1 : ℝ)))).dist_le_mul (nodes v x w (T/(n+1 : ℝ)) j) (X ((j : ℝ)*(T/(n+1 : ℝ))))
      rw [Real.dist_eq,dist_eq_norm] at hl
      exact hl.trans (mul_le_mul_of_nonneg_left (hn j hj.le) L.coe_nonneg))
  have ht : ((n+1 : ℕ) : ℝ)*(T/(n+1 : ℝ)) = T := by
    push_cast
    exact mul_div_cancel₀ T (by positivity)
  rw [ht] at hb
  simp only [Real.dist_eq,sub_zero]
  refine hb.trans_lt ?_
  have hc : T*((L : ℝ)*(ε/(2*T*((L : ℝ)+1)))) < ε := by
    calc
      _ = (T*(L : ℝ)*ε)/(2*T*((L : ℝ)+1)) := by ring
      _ < ε := (div_lt_iff₀ hpos).mpr (by nlinarith [L.coe_nonneg,mul_pos hT hε])
  exact hc


set_option maxHeartbeats 800000 in
theorem node_sum_difference_expectation_tendsto
    (h : ∀ ω, FiniteAdditiveTrajectory v (fun t => w t ω) (x ω) T (fun t => X t ω))
    (hv : ∀ t, LipschitzWith K (v t)) (hg : ∀ t, LipschitzWith L (g t)) (hb : ∀ t z, |g t z| ≤ B)
    (hx : Measurable x) (hw : ∀ t, Measurable (w t))
    (hXm : ∀ t ∈ Icc 0 T, Measurable (X t)) (hT : 0 < T) :
    Tendsto (fun n : ℕ => ∫ ω, (T/(n+1 : ℝ)) * ∑ j ∈ Finset.range (n+1),
      (g ((j : ℝ)*(T/(n+1 : ℝ))) (nodes v (x ω) (fun t => w t ω) (T/(n+1 : ℝ)) j) -
        g ((j : ℝ)*(T/(n+1 : ℝ))) (X ((j : ℝ)*(T/(n+1 : ℝ))) ω)) ∂P) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => ∫ ω, (T/(n+1 : ℝ)) * ∑ j ∈ Finset.range (n+1),
      (g ((j : ℝ)*(T/(n+1 : ℝ))) (nodes v (x ω) (fun t => w t ω) (T/(n+1 : ℝ)) j) -
        g ((j : ℝ)*(T/(n+1 : ℝ))) (X ((j : ℝ)*(T/(n+1 : ℝ))) ω)) ∂P) atTop (𝓝 (∫ _ω, (0 : ℝ) ∂P)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => T*(2*B))
    · intro n
      apply Measurable.aestronglyMeasurable
      apply measurable_const.mul
      apply Finset.measurable_sum
      intro j hj
      exact ((hg _).continuous.measurable.comp (nodes_measurable
        (fun t => (hv t).continuous.measurable) hx hw _ j)).sub
        ((hg _).continuous.measurable.comp (hXm _
          (grid_time_mem_Icc hT.le n j (Finset.mem_range.mp hj).le)))
    · exact integrable_const _
    · intro n
      apply Eventually.of_forall
      intro ω
      have hs := scaled_sum_bound (show 0 ≤ T/(n+1 : ℝ) by positivity) (n+1)
        (fun j => g ((j : ℝ)*(T/(n+1 : ℝ))) (nodes v (x ω) (fun t => w t ω) (T/(n+1 : ℝ)) j) -
          g ((j : ℝ)*(T/(n+1 : ℝ))) (X ((j : ℝ)*(T/(n+1 : ℝ))) ω))
        (A := 2*B) (fun j _ => (abs_sub _ _).trans (by
          have h1 := hb ((j : ℝ)*(T/(n+1 : ℝ))) (nodes v (x ω) (fun t => w t ω) (T/(n+1 : ℝ)) j)
          have h2 := hb ((j : ℝ)*(T/(n+1 : ℝ))) (X ((j : ℝ)*(T/(n+1 : ℝ))) ω)
          linarith))
      have ht : ((n+1 : ℕ) : ℝ)*(T/(n+1 : ℝ)) = T := by
        push_cast
        exact mul_div_cancel₀ T (by positivity)
      rw [ht] at hs
      simpa only [Real.norm_eq_abs] using hs
    · apply Eventually.of_forall
      intro ω
      exact node_sum_difference_tendsto (E := E) (v := v) (w := fun t => w t ω)
        (X := fun t => X t ω) (x := x ω) (T := T) (K := K) (L := L) (g := g) (h ω) hv hg hT
  simpa only [integral_zero] using hlim

omit [NormedSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E] in
theorem trajectory_mean_continuousOn
    (h : ∀ ω, ContinuousOn (fun t => X t ω) (Icc 0 T))
    (hgc : Continuous (Function.uncurry g)) (hb : ∀ t z, |g t z| ≤ B) (hXm : ∀ t ∈ Icc 0 T, Measurable (X t)) :
    ContinuousOn (fun t => ∫ ω, g t (X t ω) ∂P) (Icc 0 T) := by
  apply continuousOn_iff_continuous_restrict.mpr
  apply continuous_of_dominated (bound := fun _ => B)
  · intro t
    exact ((hgc.comp (continuous_const.prodMk continuous_id)).measurable.comp (hXm t t.property)).aestronglyMeasurable
  · intro t
    exact Eventually.of_forall (fun ω => by simpa only [Real.norm_eq_abs] using hb t (X t ω))
  · exact integrable_const B
  · exact Eventually.of_forall (fun ω => hgc.comp (continuous_subtype_val.prodMk (h ω).restrict))

theorem expected_nodes_riemann_tendsto
    (h : ∀ ω, FiniteAdditiveTrajectory v (fun t => w t ω) (x ω) T (fun t => X t ω))
    (hv : ∀ t, LipschitzWith K (v t)) (hg : ∀ t, LipschitzWith L (g t))
    (hgc : Continuous (Function.uncurry g)) (hb : ∀ t z, |g t z| ≤ B)
    (hx : Measurable x) (hw : ∀ t, Measurable (w t))
    (hXm : ∀ t ∈ Icc 0 T, Measurable (X t)) (hT : 0 < T) :
    Tendsto (fun n : ℕ => (T/(n+1 : ℝ)) * ∑ j ∈ Finset.range (n+1),
      ∫ ω, g ((j : ℝ)*(T/(n+1 : ℝ))) (nodes v (x ω) (fun t => w t ω) (T/(n+1 : ℝ)) j) ∂P)
      atTop (𝓝 (∫ s in (0 : ℝ)..T, ∫ ω, g s (X s ω) ∂P)) := by
  have hc := trajectory_mean_continuousOn (P := P) (fun ω => (h ω).continuous) hgc hb hXm
  have hr := riemann_tendsto hc hT
  have hd := node_sum_difference_expectation_tendsto h hv hg hb hx hw hXm hT (P := P)
  have hsum := hd.add hr
  simp only [zero_add] at hsum
  apply hsum.congr'
  apply Eventually.of_forall
  intro n
  dsimp only
  have hni (j : ℕ) : Integrable (fun ω =>
      g ((j : ℝ)*(T/(n+1 : ℝ))) (nodes v (x ω) (fun t => w t ω) (T/(n+1 : ℝ)) j)) P :=
    bounded_observable_integrable (hg _).continuous (hb _)
      (nodes_measurable (fun t => (hv t).continuous.measurable) hx hw _ j)
  have hxi (j : ℕ) (hj : j ∈ Finset.range (n+1)) :
      Integrable (fun ω => g ((j : ℝ)*(T/(n+1 : ℝ))) (X ((j : ℝ)*(T/(n+1 : ℝ))) ω)) P :=
    bounded_observable_integrable (hg _).continuous (hb _)
      (hXm _ (grid_time_mem_Icc hT.le n j (Finset.mem_range.mp hj).le))
  have hdi (j : ℕ) (hj : j ∈ Finset.range (n+1)) : Integrable (fun ω =>
      g ((j : ℝ)*(T/(n+1 : ℝ))) (nodes v (x ω) (fun t => w t ω) (T/(n+1 : ℝ)) j) -
        g ((j : ℝ)*(T/(n+1 : ℝ))) (X ((j : ℝ)*(T/(n+1 : ℝ))) ω)) P := (hni j).sub (hxi j hj)
  rw [integral_const_mul,integral_finsetSum _ hdi]
  have he := Finset.sum_congr rfl (fun j hj => integral_sub (hni j) (hxi j hj))
  rw [he]
  rw [Finset.sum_sub_distrib]
  ring

end SharpWasserstein.EulerTime
