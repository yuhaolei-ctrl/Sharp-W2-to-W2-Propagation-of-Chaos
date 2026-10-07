module

public import SharpWasserstein.Compat
public import SharpWasserstein.EulerRiemann

@[expose] public section

/-! Expected Riemann sums for the actual Euler scheme. The proof uses only
the proved pathwise approximation, bounded domination and finite-sum Fubini. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Interval Topology
namespace SharpWasserstein.Euler

variable {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]
  {P : Measure Ω} [IsFiniteMeasure P]
  {v : ℝ → E → E} {w X : ℝ → Ω → E} {x : Ω → E} {T B : ℝ} {K L : ℝ≥0} {g : E → ℝ}

omit [NormedSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E] in
theorem bounded_observable_integrable (hg : Continuous g) (hb : ∀ z, |g z| ≤ B)
    {Y : Ω → E} (hY : Measurable Y) : Integrable (fun ω => g (Y ω)) P :=
  Integrable.mono' (integrable_const B) (hg.measurable.comp hY).aestronglyMeasurable
    (Eventually.of_forall (fun ω => by simpa only [Real.norm_eq_abs] using hb (Y ω)))

set_option maxHeartbeats 800000 in
theorem node_sum_difference_expectation_tendsto
    (h : ∀ ω, FiniteAdditiveTrajectory v (fun t => w t ω) (x ω) T (fun t => X t ω))
    (hv : ∀ t, LipschitzWith K (v t)) (hg : LipschitzWith L g) (hb : ∀ z, |g z| ≤ B)
    (hx : Measurable x) (hw : ∀ t, Measurable (w t))
    (hXm : ∀ t ∈ Icc 0 T, Measurable (X t)) (hT : 0 < T) :
    Tendsto (fun n : ℕ => ∫ ω, (T/(n+1 : ℝ)) * ∑ j ∈ Finset.range (n+1),
      (g (nodes v (x ω) (fun t => w t ω) (T/(n+1 : ℝ)) j) -
        g (X ((j : ℝ)*(T/(n+1 : ℝ))) ω)) ∂P) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => ∫ ω, (T/(n+1 : ℝ)) * ∑ j ∈ Finset.range (n+1),
      (g (nodes v (x ω) (fun t => w t ω) (T/(n+1 : ℝ)) j) -
        g (X ((j : ℝ)*(T/(n+1 : ℝ))) ω)) ∂P) atTop (𝓝 (∫ _ω, (0 : ℝ) ∂P)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => T*(2*B))
    · intro n
      apply Measurable.aestronglyMeasurable
      apply measurable_const.mul
      apply Finset.measurable_sum
      intro j hj
      exact (hg.continuous.measurable.comp (nodes_measurable
        (fun t => (hv t).continuous.measurable) hx hw _ j)).sub
        (hg.continuous.measurable.comp (hXm _
          (grid_time_mem_Icc hT.le n j (Finset.mem_range.mp hj).le)))
    · exact integrable_const _
    · intro n
      apply Eventually.of_forall
      intro ω
      have hs := scaled_sum_bound (show 0 ≤ T/(n+1 : ℝ) by positivity) (n+1)
        (fun j => g (nodes v (x ω) (fun t => w t ω) (T/(n+1 : ℝ)) j) -
          g (X ((j : ℝ)*(T/(n+1 : ℝ))) ω))
        (A := 2*B) (fun j _ => (abs_sub _ _).trans (by
          have h1 := hb (nodes v (x ω) (fun t => w t ω) (T/(n+1 : ℝ)) j)
          have h2 := hb (X ((j : ℝ)*(T/(n+1 : ℝ))) ω)
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
    (hg : Continuous g) (hb : ∀ z, |g z| ≤ B) (hXm : ∀ t ∈ Icc 0 T, Measurable (X t)) :
    ContinuousOn (fun t => ∫ ω, g (X t ω) ∂P) (Icc 0 T) := by
  apply continuousOn_iff_continuous_restrict.mpr
  apply continuous_of_dominated (bound := fun _ => B)
  · intro t
    exact (hg.measurable.comp (hXm t t.property)).aestronglyMeasurable
  · intro t
    exact Eventually.of_forall (fun ω => by simpa only [Real.norm_eq_abs] using hb (X t ω))
  · exact integrable_const B
  · exact Eventually.of_forall (fun ω => hg.comp (h ω).restrict)

theorem expected_nodes_riemann_tendsto
    (h : ∀ ω, FiniteAdditiveTrajectory v (fun t => w t ω) (x ω) T (fun t => X t ω))
    (hv : ∀ t, LipschitzWith K (v t)) (hg : LipschitzWith L g) (hb : ∀ z, |g z| ≤ B)
    (hx : Measurable x) (hw : ∀ t, Measurable (w t))
    (hXm : ∀ t ∈ Icc 0 T, Measurable (X t)) (hT : 0 < T) :
    Tendsto (fun n : ℕ => (T/(n+1 : ℝ)) * ∑ j ∈ Finset.range (n+1),
      ∫ ω, g (nodes v (x ω) (fun t => w t ω) (T/(n+1 : ℝ)) j) ∂P)
      atTop (𝓝 (∫ s in (0 : ℝ)..T, ∫ ω, g (X s ω) ∂P)) := by
  have hc := trajectory_mean_continuousOn (P := P) (fun ω => (h ω).continuous) hg.continuous hb hXm
  have hr := riemann_tendsto hc hT
  have hd := node_sum_difference_expectation_tendsto h hv hg hb hx hw hXm hT (P := P)
  have hsum := hd.add hr
  simp only [zero_add] at hsum
  apply hsum.congr'
  apply Eventually.of_forall
  intro n
  dsimp only
  have hni (j : ℕ) : Integrable (fun ω =>
      g (nodes v (x ω) (fun t => w t ω) (T/(n+1 : ℝ)) j)) P :=
    bounded_observable_integrable hg.continuous hb
      (nodes_measurable (fun t => (hv t).continuous.measurable) hx hw _ j)
  have hxi (j : ℕ) (hj : j ∈ Finset.range (n+1)) :
      Integrable (fun ω => g (X ((j : ℝ)*(T/(n+1 : ℝ))) ω)) P :=
    bounded_observable_integrable hg.continuous hb
      (hXm _ (grid_time_mem_Icc hT.le n j (Finset.mem_range.mp hj).le))
  have hdi (j : ℕ) (hj : j ∈ Finset.range (n+1)) : Integrable (fun ω =>
      g (nodes v (x ω) (fun t => w t ω) (T/(n+1 : ℝ)) j) -
        g (X ((j : ℝ)*(T/(n+1 : ℝ))) ω)) P := (hni j).sub (hxi j hj)
  rw [integral_const_mul,integral_finsetSum _ hdi]
  have he := Finset.sum_congr rfl (fun j hj => integral_sub (hni j) (hxi j hj))
  rw [he]
  rw [Finset.sum_sub_distrib]
  ring

end SharpWasserstein.Euler
