module

public import SharpWasserstein.Compat
public import SharpWasserstein.FlowJacobianDriftStability

@[expose] public section

/-! Dominated convergence of actual drift-derivative coefficients and the
resulting uniform-in-time operator convergence of genuine flow Jacobians. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal Topology Interval
namespace SharpWasserstein.FlowJacobianDrift
open FlowInitialDerivative
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Uniformly bounded continuous coefficient fields converge in the actual
integrated operator norm from pointwise convergence alone. -/
theorem coefficient_error_integral_tendsto
    {A : ℕ → ℝ → E →L[ℝ] E} {B : ℝ → E →L[ℝ] E} {K : ℝ≥0} {T : ℝ}
    (hAc : ∀ n, Continuous (A n)) (hBc : Continuous B)
    (hA : ∀ n s, ‖A n s‖ ≤ K) (hB : ∀ s, ‖B s‖ ≤ K)
    (hconv : ∀ s ∈ Icc 0 T, Tendsto (fun n => A n s) atTop (𝓝 (B s))) (hT : 0 ≤ T) :
    Tendsto (fun n => ∫ s in (0:ℝ)..T,‖B s-A n s‖) atTop (𝓝 0) := by
  have hh := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (a := 0) (b := T) (μ := volume) (f := fun _ => (0:ℝ)) (bound := fun _ => 2*(K:ℝ))
    (F := fun n s => ‖B s-A n s‖)
    (Eventually.of_forall (fun n => ((hBc.sub (hAc n)).norm).aestronglyMeasurable))
    (Eventually.of_forall (fun n => Eventually.of_forall (fun s _ => by
      rw [norm_norm]
      exact (norm_sub_le _ _).trans (by linarith [hB s,hA n s]))))
    intervalIntegrable_const
    (Eventually.of_forall (fun s hs => by
      have hsT : s ∈ Icc 0 T := by
        rw [uIoc_of_le hT] at hs
        exact ⟨hs.1.le,hs.2⟩
      simpa only [sub_self,norm_zero] using ((tendsto_const_nhds (x := B s)).sub (hconv s hsT)).norm))
  simpa only [intervalIntegral.integral_zero] using hh

/-- Stability of the actual variational equations is uniform on the full
finite horizon, even when coefficient convergence is merely pointwise. -/
theorem variation_tendstoUniformlyOn
    {A J : ℕ → ℝ → E →L[ℝ] E} {B H : ℝ → E →L[ℝ] E} {K : ℝ≥0} {T : ℝ}
    (hT : 0 ≤ T) (hAc : ∀ n, Continuous (A n)) (hBc : Continuous B)
    (hJ : ∀ n, LinearVariation (A n) T (J n)) (hH : LinearVariation B T H)
    (hA : ∀ n s, ‖A n s‖ ≤ K) (hB : ∀ s, ‖B s‖ ≤ K)
    (hconv : ∀ s ∈ Icc 0 T, Tendsto (fun n => A n s) atTop (𝓝 (B s))) :
    TendstoUniformlyOn J H atTop (Icc 0 T) := by
  let D : ℕ → ℝ := fun n => (∫ s in (0:ℝ)..T,‖B s-A n s‖)*Real.exp ((K:ℝ)*T)^2
  have hD : Tendsto D atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (coefficient_error_integral_tendsto hAc hBc hA hB hconv hT).mul_const (Real.exp ((K:ℝ)*T)^2)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hD.eventually (gt_mem_nhds hε)] with n hn t ht
  rw [dist_eq_norm,norm_sub_rev]
  apply lt_of_le_of_lt _ hn
  apply (variation_difference_le_integral hT (hAc n) hBc (hJ n) hH
    (fun s _ => hA n s) (fun s _ => hB s) ht).trans
  calc
    _ ≤ ((∫ s in (0:ℝ)..T,‖B s-A n s‖)*Real.exp ((K:ℝ)*T))*Real.exp ((K:ℝ)*T) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 K.coe_nonneg))
        (mul_nonneg (intervalIntegral.integral_nonneg_of_forall hT (fun _ => norm_nonneg _)) (Real.exp_pos _).le)
    _ = D n := by dsimp [D]; ring

variable [FiniteDimensional ℝ E]

/-- Actual flow convergence and moving-point convergence of the drift's first
derivative imply convergence of the actual initial Jacobians. Second-derivative
Lipschitz constants may depend on the approximation index. -/
theorem jacobian_tendstoUniformlyOn
    {bk : ℕ → E → E} {b : E → E} {M K K₁ : ℝ≥0} {K₁k : ℕ → ℝ≥0}
    (hbk : ∀ n x, ‖bk n x‖ ≤ M) (hLipk : ∀ n, LipschitzWith K (bk n))
    (hbdk : ∀ n, Differentiable ℝ (bk n)) (hDbk : ∀ n, LipschitzWith (K₁k n) (fderiv ℝ (bk n)))
    (hb : ∀ x, ‖b x‖ ≤ M) (hLip : LipschitzWith K b)
    (hbd : Differentiable ℝ b) (hDb : LipschitzWith K₁ (fderiv ℝ b))
    {T : ℝ} (hT : 0 ≤ T) (wk : ℕ → C(Icc 0 T,E)) (w : C(Icc 0 T,E)) (xk : ℕ → E) (x : E)
    (hflow : ∀ s ∈ Icc 0 T, Tendsto (fun n => autonomousFlow (hbk n) (hLipk n) hT (xk n) (wk n) s)
      atTop (𝓝 (autonomousFlow hb hLip hT x w s)))
    (hderiv : ∀ (yk : ℕ → E) (y : E), Tendsto yk atTop (𝓝 y) →
      Tendsto (fun n => fderiv ℝ (bk n) (yk n)) atTop (𝓝 (fderiv ℝ b y))) :
    TendstoUniformlyOn (fun n => jacobian (hbk n) (hLipk n) hT (wk n) (xk n))
      (jacobian hb hLip hT w x) atTop (Icc 0 T) := by
  apply variation_tendstoUniformlyOn hT
    (fun n => coefficient_continuous (hbk n) (hLipk n) (hDbk n) hT (wk n) (xk n))
    (coefficient_continuous hb hLip hDb hT w x)
    (fun n => jacobian_linearVariation (hbk n) (hLipk n) (hbdk n) (hDbk n) hT (wk n) (xk n))
    (jacobian_linearVariation hb hLip hbd hDb hT w x)
    (fun n => coefficient_norm_le (hbk n) (hLipk n) hT (wk n) (xk n))
    (coefficient_norm_le hb hLip hT w x)
  intro s hs
  simpa only [coefficient,projIcc_of_mem _ hs] using hderiv _ _ (hflow s hs)

/-- Endpoint convergence in the actual continuous-linear-operator norm. -/
theorem fderiv_flow_tendsto
    {bk : ℕ → E → E} {b : E → E} {M K K₁ : ℝ≥0} {K₁k : ℕ → ℝ≥0}
    (hbk : ∀ n x, ‖bk n x‖ ≤ M) (hLipk : ∀ n, LipschitzWith K (bk n))
    (hbdk : ∀ n, Differentiable ℝ (bk n)) (hDbk : ∀ n, LipschitzWith (K₁k n) (fderiv ℝ (bk n)))
    (hb : ∀ x, ‖b x‖ ≤ M) (hLip : LipschitzWith K b)
    (hbd : Differentiable ℝ b) (hDb : LipschitzWith K₁ (fderiv ℝ b))
    {T : ℝ} (hT : 0 ≤ T) (wk : ℕ → C(Icc 0 T,E)) (w : C(Icc 0 T,E)) (xk : ℕ → E) (x : E)
    (hflow : ∀ s ∈ Icc 0 T, Tendsto (fun n => autonomousFlow (hbk n) (hLipk n) hT (xk n) (wk n) s)
      atTop (𝓝 (autonomousFlow hb hLip hT x w s)))
    (hderiv : ∀ (yk : ℕ → E) (y : E), Tendsto yk atTop (𝓝 y) →
      Tendsto (fun n => fderiv ℝ (bk n) (yk n)) atTop (𝓝 (fderiv ℝ b y)))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    Tendsto (fun n => fderiv ℝ (fun y => autonomousFlow (hbk n) (hLipk n) hT y (wk n) t) (xk n))
      atTop (𝓝 (fderiv ℝ (fun y => autonomousFlow hb hLip hT y w t) x)) := by
  simpa only [jacobian,projIcc_of_mem _ ht] using
    (jacobian_tendstoUniformlyOn hbk hLipk hbdk hDbk hb hLip hbd hDb hT wk w xk x hflow hderiv).tendsto_at ht

end SharpWasserstein.FlowJacobianDrift
