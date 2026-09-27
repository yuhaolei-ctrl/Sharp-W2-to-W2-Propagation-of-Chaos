import SharpWasserstein.EulerLaw

/-! Riemann sums along the actual Euler trajectories. The time mesh and
Gaussian increments used by the weak-generator proof are kept explicit. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Interval Topology
namespace SharpWasserstein.Euler

theorem continuous_step_error {f : ℝ → ℝ} {T : ℝ}
    (hf : ContinuousOn f (Icc 0 T)) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ δ, 0 ≤ δ → δ ≤ η → ∀ j : ℕ, ((j+1 : ℕ) : ℝ)*δ ≤ T →
      |δ*f (j*δ) - ∫ s in (j : ℝ)*δ..((j+1 : ℕ) : ℝ)*δ, f s| ≤ δ*ε := by
  obtain ⟨η,hη,hu⟩ := Metric.uniformContinuousOn_iff_le.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) ε hε
  refine ⟨η,hη,fun δ hδ hδη j hj => ?_⟩
  have ha : 0 ≤ (j : ℝ)*δ := by positivity
  have hab : (j : ℝ)*δ ≤ ((j+1 : ℕ) : ℝ)*δ := by push_cast; nlinarith
  have hlen : ((j+1 : ℕ) : ℝ)*δ-(j : ℝ)*δ = δ := by push_cast; ring
  have hi : IntervalIntegrable f volume ((j : ℝ)*δ) (((j+1 : ℕ) : ℝ)*δ) :=
    (hf.mono (Icc_subset_Icc ha hj)).intervalIntegrable_of_Icc hab
  have he : δ*f (j*δ) - ∫ s in (j : ℝ)*δ..((j+1 : ℕ) : ℝ)*δ, f s =
      ∫ s in (j : ℝ)*δ..((j+1 : ℕ) : ℝ)*δ, (f (j*δ)-f s) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hi,
      intervalIntegral.integral_const,hlen,smul_eq_mul]
  rw [he,← Real.norm_eq_abs]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (j : ℝ)*δ) (b := ((j+1 : ℕ) : ℝ)*δ)
    (f := fun s => f (j*δ)-f s) (C := ε) (fun s hs => by
      rw [uIoc_of_le hab] at hs
      have hd : dist ((j : ℝ)*δ) s ≤ η := by
        rw [Real.dist_eq,abs_of_nonpos (by linarith [hs.1.le])]
        linarith [hs.2]
      simpa only [dist_eq_norm] using hu _ ⟨ha,hab.trans hj⟩ s
        ⟨ha.trans hs.1.le,hs.2.trans hj⟩ hd)
  rw [hlen,abs_of_nonneg hδ] at hb
  simpa only [mul_comm] using hb

theorem riemann_error_le {f : ℝ → ℝ} {T δ ε : ℝ}
    (hf : ContinuousOn f (Icc 0 T)) (hδ : 0 ≤ δ) (m : ℕ) (hm : (m : ℝ)*δ ≤ T)
    (hs : ∀ j < m, |δ*f (j*δ) - ∫ s in (j : ℝ)*δ..((j+1 : ℕ) : ℝ)*δ, f s| ≤ δ*ε) :
    |δ * ∑ j ∈ Finset.range m, f (j*δ) - ∫ s in (0 : ℝ)..(m : ℝ)*δ, f s| ≤
      (m : ℝ)*δ*ε := by
  have hi (j : ℕ) (hj : j < m) : IntervalIntegrable f volume
      ((j : ℝ)*δ) (((j+1 : ℕ) : ℝ)*δ) := by
    have hhi : ((j+1 : ℕ) : ℝ)*δ ≤ T :=
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hj) hδ).trans hm
    have hab : (j : ℝ)*δ ≤ ((j+1 : ℕ) : ℝ)*δ := by push_cast; nlinarith
    exact (hf.mono (Icc_subset_Icc (by positivity) hhi)).intervalIntegrable_of_Icc hab
  have he := intervalIntegral.sum_integral_adjacent_intervals (n := m)
    (a := fun j => (j : ℝ)*δ) hi
  simp only [Nat.cast_zero,zero_mul] at he
  rw [← he,Finset.mul_sum,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ Finset.range m,
        |δ*f (j*δ) - ∫ s in (j : ℝ)*δ..((j+1 : ℕ) : ℝ)*δ, f s| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range m, δ*ε := Finset.sum_le_sum fun j hj => hs j (Finset.mem_range.mp hj)
    _ = _ := by simp; ring

theorem riemann_tendsto {f : ℝ → ℝ} {T : ℝ} (hf : ContinuousOn f (Icc 0 T)) (hT : 0 < T) :
    Tendsto (fun n : ℕ => (T/(n+1 : ℝ)) * ∑ j ∈ Finset.range (n+1),
      f ((j : ℝ)*(T/(n+1 : ℝ)))) atTop (𝓝 (∫ s in (0 : ℝ)..T, f s)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨η,hη,he⟩ := continuous_step_error hf (div_pos hε (show 0 < 2*T by positivity))
  have hmesh : Tendsto (fun n : ℕ => T/(n+1 : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero,div_eq_mul_inv,one_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul T
  filter_upwards [hmesh.eventually (gt_mem_nhds hη)] with n hn
  have ht : ((n+1 : ℕ) : ℝ)*(T/(n+1 : ℝ)) = T := by
    push_cast
    exact mul_div_cancel₀ T (by positivity)
  have hb := riemann_error_le hf (show 0 ≤ T/(n+1 : ℝ) by positivity) (n+1) (by rw [ht])
    (fun j hj => he _ (by positivity) hn.le j
      ((mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hj) (by positivity)).trans (le_of_eq ht)))
  rw [ht] at hb
  rw [Real.dist_eq]
  refine hb.trans_lt ?_
  have heq : T * (ε / (2*T)) = ε/2 := by field_simp
  rw [heq]
  linarith

theorem scaled_sum_bound {δ A : ℝ} (hδ : 0 ≤ δ) (m : ℕ) (f : ℕ → ℝ)
    (hf : ∀ j < m, |f j| ≤ A) :
    |δ * ∑ j ∈ Finset.range m, f j| ≤ (m : ℝ)*δ*A := by
  rw [abs_mul,abs_of_nonneg hδ]
  calc
    _ ≤ δ * ∑ j ∈ Finset.range m, |f j| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hδ
    _ ≤ δ * ∑ _j ∈ Finset.range m, A := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun j hj => hf j (Finset.mem_range.mp hj)) hδ
    _ = _ := by simp; ring

theorem grid_time_mem_Icc {T : ℝ} (hT : 0 ≤ T) (n j : ℕ) (hj : j ≤ n+1) :
    (j : ℝ)*(T/(n+1 : ℝ)) ∈ Icc 0 T := by
  refine ⟨by positivity, ?_⟩
  have he : ((n+1 : ℕ) : ℝ)*(T/(n+1 : ℝ)) = T := by
    push_cast
    exact mul_div_cancel₀ T (by positivity)
  exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hj) (by positivity)).trans (le_of_eq he)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem nodes_uniform_eventually {v : ℝ → E → E} {w X : ℝ → E} {x : E} {T : ℝ} {K : ℝ≥0}
    (h : FiniteAdditiveTrajectory v w x T X) (hv : ∀ t, LipschitzWith K (v t))
    (hT : 0 < T) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ j ≤ n+1,
      ‖nodes v x w (T/(n+1 : ℝ)) j - X ((j : ℝ)*(T/(n+1 : ℝ)))‖ ≤ ε := by
  let C := T*Real.exp ((K : ℝ)*T)
  have hC : 0 < C := mul_pos hT (Real.exp_pos _)
  obtain ⟨η,hη,he⟩ := trajectory_nodes_uniform_error h hv hT.le (div_pos hε hC)
  have hmesh : Tendsto (fun n : ℕ => T/(n+1 : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero,div_eq_mul_inv,one_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul T
  filter_upwards [hmesh.eventually (gt_mem_nhds hη)] with n hn j hj
  have ht : ((n+1 : ℕ) : ℝ)*(T/(n+1 : ℝ)) = T := by
    push_cast
    exact mul_div_cancel₀ T (by positivity)
  have hbound := he _ (by positivity) hn.le j
    ((mul_le_mul_of_nonneg_right (by exact_mod_cast hj) (by positivity)).trans (le_of_eq ht))
  have heq : (ε/C)*T*Real.exp ((K : ℝ)*T) = ε := by
    rw [mul_assoc]
    exact div_mul_cancel₀ ε hC.ne'
  rwa [heq] at hbound

theorem node_sum_difference_tendsto {v : ℝ → E → E} {w X : ℝ → E} {x : E} {T : ℝ}
    {K L : ℝ≥0} {g : E → ℝ}
    (h : FiniteAdditiveTrajectory v w x T X) (hv : ∀ t, LipschitzWith K (v t))
    (hg : LipschitzWith L g) (hT : 0 < T) :
    Tendsto (fun n : ℕ => (T/(n+1 : ℝ)) * ∑ j ∈ Finset.range (n+1),
      (g (nodes v x w (T/(n+1 : ℝ)) j) - g (X ((j : ℝ)*(T/(n+1 : ℝ)))))) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hpos : 0 < 2*T*((L : ℝ)+1) := by positivity
  filter_upwards [nodes_uniform_eventually h hv hT (div_pos hε hpos)] with n hn
  have hb := scaled_sum_bound (show 0 ≤ T/(n+1 : ℝ) by positivity) (n+1)
    (fun j => g (nodes v x w (T/(n+1 : ℝ)) j)-g (X ((j : ℝ)*(T/(n+1 : ℝ)))))
    (fun j hj => by
      have hl := hg.dist_le_mul (nodes v x w (T/(n+1 : ℝ)) j) (X ((j : ℝ)*(T/(n+1 : ℝ))))
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

end SharpWasserstein.Euler
