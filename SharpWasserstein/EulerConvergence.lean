import SharpWasserstein.BoundedFlow
import Mathlib.Analysis.SpecificLimits.Basic

/-! Explicit Euler nodes for continuous additive forcing and their convergence
to the actual integral solution. Local errors are derived from the trajectory
integral and continuity of its drift, rather than assumed of a diffusion. -/

noncomputable section
open Set MeasureTheory
open scoped NNReal Interval

namespace SharpWasserstein.Euler

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def nodes (v : ℝ → E → E) (x : E) (w : ℝ → E) (δ : ℝ) : ℕ → E
  | 0 => x + w 0
  | n+1 => nodes v x w δ n + δ • v (n * δ) (nodes v x w δ n) +
    (w ((n+1) * δ) - w (n * δ))

def residual (v : ℝ → E → E) (w X : ℝ → E) (δ : ℝ) (n : ℕ) : E :=
  X ((n+1) * δ) - (X (n * δ) + δ • v (n * δ) (X (n * δ)) +
    (w ((n+1) * δ) - w (n * δ)))

theorem error_step {v : ℝ → E → E} {w X : ℝ → E} {x : E} {δ : ℝ}
    {K : ℝ≥0} (hδ : 0 ≤ δ) (hv : ∀ t, LipschitzWith K (v t)) (n : ℕ) :
    ‖nodes v x w δ (n+1) - X ((n+1) * δ)‖ ≤
      (1 + (K : ℝ) * δ) * ‖nodes v x w δ n - X (n * δ)‖ + ‖residual v w X δ n‖ := by
  have heq : nodes v x w δ (n+1) - X ((n+1) * δ) =
      (nodes v x w δ n - X (n * δ)) +
        δ • (v (n * δ) (nodes v x w δ n) - v (n * δ) (X (n * δ))) - residual v w X δ n := by
    simp only [nodes, residual, smul_sub]
    abel
  rw [heq]
  have hvn := (hv (n * δ)).dist_le_mul (nodes v x w δ n) (X (n * δ))
  simp only [dist_eq_norm] at hvn
  calc
    _ ≤ ‖nodes v x w δ n - X (n * δ)‖ +
        ‖δ • (v (n * δ) (nodes v x w δ n) - v (n * δ) (X (n * δ)))‖ +
          ‖residual v w X δ n‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hδ]
      nlinarith [mul_le_mul_of_nonneg_left hvn hδ]

/-- A finite discrete Grönwall estimate, with no strict positivity of K. -/
theorem discrete_gronwall {a : ℕ → ℝ} {q c : ℝ} {N : ℕ}
    (hq : 1 ≤ q) (hc : 0 ≤ c) (ha : a 0 ≤ 0)
    (hstep : ∀ n < N, a (n+1) ≤ q * a n + c) :
    ∀ n ≤ N, a n ≤ c * n * q ^ n := by
  intro n hn
  induction n with
  | zero => simpa using ha
  | succ n ih =>
    have hnN : n < N := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn
    have hi := mul_le_mul_of_nonneg_left (ih hnN.le) (by linarith : 0 ≤ q)
    have hpow : 1 ≤ q ^ (n+1) := one_le_pow₀ hq
    have hc' := mul_le_mul_of_nonneg_left hpow hc
    have hs := hstep n hnN
    rw [pow_succ] at hc'
    rw [Nat.cast_add, Nat.cast_one, pow_succ]
    nlinarith

theorem node_error_le {v : ℝ → E → E} {w X : ℝ → E} {x : E} {δ ε : ℝ}
    {K : ℝ≥0} {N : ℕ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hv : ∀ t, LipschitzWith K (v t)) (hzero : X 0 = x + w 0)
    (hres : ∀ n < N, ‖residual v w X δ n‖ ≤ δ * ε) :
    ‖nodes v x w δ N - X (N * δ)‖ ≤ δ * ε * N * (1 + (K : ℝ) * δ) ^ N := by
  apply discrete_gronwall (a := fun n => ‖nodes v x w δ n - X (n * δ)‖)
    (q := 1 + (K : ℝ) * δ) (c := δ * ε) (N := N)
    (by have h := mul_nonneg K.coe_nonneg hδ; linarith) (by positivity) _ _ N le_rfl
  · simp [nodes, hzero]
  · intro n hn
    simpa only [Nat.cast_add, Nat.cast_one] using
      (error_step (x := x) hδ hv n).trans (add_le_add le_rfl (hres n hn))

theorem trajectory_step [CompleteSpace E]
    {v : ℝ → E → E} {w X : ℝ → E} {x : E} {T a b : ℝ}
    (h : FiniteAdditiveTrajectory v w x T X) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    X b = X a + (∫ s in a..b, v s (X s)) + (w b - w a) := by
  have hia : IntervalIntegrable (fun s => v s (X s)) volume 0 a :=
    (h.driftContinuous.mono (Icc_subset_Icc_right (hab.trans hb))).intervalIntegrable_of_Icc ha
  have hiab : IntervalIntegrable (fun s => v s (X s)) volume a b :=
    (h.driftContinuous.mono (Icc_subset_Icc ha hb)).intervalIntegrable_of_Icc hab
  rw [h.equation b ⟨ha.trans hab, hb⟩, h.equation a ⟨ha, hab.trans hb⟩,
    ← intervalIntegral.integral_add_adjacent_intervals hia hiab]
  abel

theorem residual_eq_integral [CompleteSpace E]
    {v : ℝ → E → E} {w X : ℝ → E} {x : E} {T δ : ℝ}
    (h : FiniteAdditiveTrajectory v w x T X) (hδ : 0 ≤ δ)
    (n : ℕ) (hn : ((n+1 : ℕ) : ℝ) * δ ≤ T) :
    residual v w X δ n =
      ∫ s in (n : ℝ) * δ..((n+1 : ℕ) : ℝ) * δ, (v s (X s) - v (n * δ) (X (n * δ))) := by
  have ha : 0 ≤ (n : ℝ) * δ := by positivity
  have hab : (n : ℝ) * δ ≤ ((n+1 : ℕ) : ℝ) * δ := by push_cast; nlinarith
  have hi : IntervalIntegrable (fun s => v s (X s)) volume ((n : ℝ)*δ) (((n+1 : ℕ) : ℝ)*δ) :=
    (h.driftContinuous.mono (Icc_subset_Icc ha hn)).intervalIntegrable_of_Icc hab
  rw [intervalIntegral.integral_sub hi intervalIntegrable_const, intervalIntegral.integral_const]
  have hlen : ((n+1 : ℕ) : ℝ) * δ - (n : ℝ) * δ = δ := by push_cast; ring
  rw [hlen]
  unfold residual
  have hs := trajectory_step h ha hab hn
  simp only [Nat.cast_add, Nat.cast_one] at hs ⊢
  rw [hs]
  abel

theorem trajectory_residual_small [CompleteSpace E]
    {v : ℝ → E → E} {w X : ℝ → E} {x : E} {T : ℝ}
    (h : FiniteAdditiveTrajectory v w x T X) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ δ, 0 ≤ δ → δ ≤ η → ∀ n : ℕ, ((n+1 : ℕ) : ℝ) * δ ≤ T →
      ‖residual v w X δ n‖ ≤ δ * ε := by
  obtain ⟨η, hη, hm⟩ := Metric.uniformContinuousOn_iff_le.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous h.driftContinuous) ε hε
  refine ⟨η, hη, fun δ hδ hδη n hn => ?_⟩
  have ha : 0 ≤ (n : ℝ) * δ := by positivity
  have hab : (n : ℝ) * δ ≤ ((n+1 : ℕ) : ℝ) * δ := by push_cast; nlinarith
  have hlen : ((n+1 : ℕ) : ℝ) * δ - (n : ℝ) * δ = δ := by push_cast; ring
  rw [residual_eq_integral h hδ n hn]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (n : ℝ)*δ) (b := ((n+1 : ℕ) : ℝ)*δ)
    (f := fun s => v s (X s) - v (n * δ) (X (n * δ))) (C := ε) (by
      intro s hs
      rw [uIoc_of_le hab] at hs
      have hd : dist s ((n : ℝ)*δ) ≤ η := by
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hs.1.le)]
        linarith [hs.2]
      simpa only [dist_eq_norm] using
        (hm s ⟨ha.trans hs.1.le, hs.2.trans hn⟩ _ ⟨ha, hab.trans hn⟩ hd))
  rw [hlen, abs_of_nonneg hδ] at hi
  simpa only [mul_comm] using hi

theorem growth_factor_le {K : ℝ≥0} {δ T : ℝ} (hδ : 0 ≤ δ)
    (N : ℕ) (hN : (N : ℝ) * δ ≤ T) :
    (1 + (K : ℝ) * δ) ^ N ≤ Real.exp ((K : ℝ) * T) := by
  calc
    _ ≤ (Real.exp ((K : ℝ) * δ)) ^ N :=
      pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp ((K : ℝ) * δ)]) N
    _ = Real.exp ((K : ℝ) * ((N : ℝ) * δ)) := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hN K.coe_nonneg)

/-- Uniform control of every node whose mesh stays within the horizon. -/
theorem trajectory_nodes_uniform_error [CompleteSpace E]
    {v : ℝ → E → E} {w X : ℝ → E} {x : E} {T : ℝ} {K : ℝ≥0}
    (h : FiniteAdditiveTrajectory v w x T X) (hv : ∀ t, LipschitzWith K (v t))
    (hT : 0 ≤ T) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ δ, 0 ≤ δ → δ ≤ η → ∀ N : ℕ, (N : ℝ) * δ ≤ T →
      ‖nodes v x w δ N - X (N * δ)‖ ≤ ε * T * Real.exp ((K : ℝ) * T) := by
  obtain ⟨η,hη,hr⟩ := trajectory_residual_small h hε
  refine ⟨η,hη,fun δ hδ hδη N hN => ?_⟩
  have hz : X 0 = x + w 0 := by simpa using h.equation 0 ⟨le_rfl,hT⟩
  have he := node_error_le hδ hε.le hv hz (N := N) (fun n hn => hr δ hδ hδη n
    ((mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hn) hδ).trans hN))
  have hg := growth_factor_le (K := K) hδ N hN
  calc
    _ ≤ δ * ε * N * (1 + (K : ℝ) * δ) ^ N := he
    _ ≤ (ε * T) * Real.exp ((K : ℝ) * T) :=
      mul_le_mul (by nlinarith) hg (by positivity) (by positivity)

/-- Euler nodes converge at the endpoint for every continuous additive input,
including every path of the constructed Brownian modification. -/
theorem trajectory_endpoint_tendsto [CompleteSpace E]
    {v : ℝ → E → E} {w X : ℝ → E} {x : E} {T : ℝ} {K : ℝ≥0}
    (h : FiniteAdditiveTrajectory v w x T X) (hv : ∀ t, LipschitzWith K (v t))
    (hT : 0 < T) :
    Filter.Tendsto (fun n : ℕ => nodes v x w (T / (n+1)) (n+1)) Filter.atTop (nhds (X T)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let C := T * Real.exp ((K : ℝ) * T)
  have hC : 0 < C := mul_pos hT (Real.exp_pos _)
  obtain ⟨η,hη,he⟩ := trajectory_nodes_uniform_error h hv hT.le
    (show 0 < ε / (2 * C) from div_pos hε (by positivity))
  have hmesh : Filter.Tendsto (fun n : ℕ => T / (n+1 : ℝ)) Filter.atTop (nhds 0) := by
    simpa only [mul_zero, div_eq_mul_inv, one_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul T
  filter_upwards [hmesh.eventually (gt_mem_nhds hη)] with n hn
  have hnp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have htime : ((n+1 : ℕ) : ℝ) * (T / ((n : ℝ) + 1)) = T := by
    push_cast
    exact mul_div_cancel₀ T (ne_of_gt hnp)
  have herr := he (T / ((n : ℝ) + 1)) (by positivity) hn.le (n+1) (by rw [htime])
  rw [htime] at herr
  rw [dist_eq_norm]
  have heps : ε / (2 * C) * T * Real.exp ((K : ℝ) * T) = ε / 2 := by
    dsimp [C]
    field_simp
  rw [heps] at herr
  exact herr.trans_lt (by linarith)

theorem nodes_compensated_norm_le {v : ℝ → E → E} {w : ℝ → E} {x : E} {δ M : ℝ}
    (hδ : 0 ≤ δ) (hb : ∀ t y, ‖v t y‖ ≤ M) (n : ℕ) :
    ‖nodes v x w δ n - x - w (n * δ)‖ ≤ M * ((n : ℝ) * δ) := by
  induction n with
  | zero => simp [nodes]
  | succ n ih =>
    have heq : nodes v x w δ (n+1) - x - w (((n+1 : ℕ) : ℝ) * δ) =
        (nodes v x w δ n - x - w (n * δ)) + δ • v (n * δ) (nodes v x w δ n) := by
      simp only [nodes, Nat.cast_add, Nat.cast_one]
      abel
    rw [heq]
    calc
      _ ≤ ‖nodes v x w δ n - x - w (n * δ)‖ + ‖δ • v (n * δ) (nodes v x w δ n)‖ := norm_add_le _ _
      _ ≤ M * ((n : ℝ) * δ) + δ * M := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hδ]
        exact add_le_add ih (mul_le_mul_of_nonneg_left (hb _ _) hδ)
      _ = _ := by push_cast; ring

/-- Bounded drift gives a deterministic domination, without any moment of
the supremum of the noise. This is used to pass Euler laws in quadratic cost. -/
theorem trajectory_endpoint_error_bound [CompleteSpace E]
    {v : ℝ → E → E} {w X : ℝ → E} {x : E} {T M : ℝ}
    (h : FiniteAdditiveTrajectory v w x T X) (hb : ∀ t y, ‖v t y‖ ≤ M)
    (hT : 0 ≤ T) (n : ℕ) :
    ‖nodes v x w (T / (n+1)) (n+1) - X T‖ ≤ 2 * M * T := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have htime : ((n+1 : ℕ) : ℝ) * (T / ((n : ℝ) + 1)) = T := by
    push_cast
    exact mul_div_cancel₀ T (ne_of_gt hn)
  have he := nodes_compensated_norm_le (w := w) (x := x)
    (show 0 ≤ T / ((n : ℝ) + 1) by positivity) hb (n+1)
  rw [htime] at he
  have hi : ‖X T - x - w T‖ ≤ M * T := by
    have heq : X T - x - w T = ∫ s in (0 : ℝ)..T, v s (X s) := by
      rw [h.equation T ⟨hT,le_rfl⟩]
      abel
    rw [heq]
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := T) (fun s _ => hb s (X s))
    simpa [abs_of_nonneg hT] using hi
  have heq : nodes v x w (T / (n+1)) (n+1) - X T =
      (nodes v x w (T / (n+1)) (n+1) - x - w T) - (X T - x - w T) := by abel
  rw [heq]
  exact (norm_sub_le _ _).trans (by linarith)

end SharpWasserstein.Euler
