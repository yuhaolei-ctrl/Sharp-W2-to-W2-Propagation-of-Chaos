import SharpWasserstein.FlowDependence
import SharpWasserstein.FlowCausality
import SharpWasserstein.EulerLaw
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-! Stability under approximation of the drift. The error is required only
along the limiting trajectory, so locally uniform drift approximation suffices. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal Interval Topology
namespace SharpWasserstein

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem FiniteAdditiveTrajectory.drift_stability
    {u v : ℝ → E → E} {w X Y : ℝ → E} {x y : E} {K : ℝ≥0} {T t δ : ℝ}
    (hu : ∀ s ∈ Icc 0 T, LipschitzWith K (u s)) (hw : ContinuousOn w (Icc 0 T))
    (hd : ∀ s ∈ Icc 0 T, ‖u s (Y s)-v s (Y s)‖ ≤ δ)
    (hX : FiniteAdditiveTrajectory u w x T X) (hY : FiniteAdditiveTrajectory v w y T Y)
    (ht : t ∈ Icc 0 T) :
    ‖X t-Y t‖ ≤ gronwallBound ‖x-y‖ K δ t := by
  let Z := fun s => (X s-w s)-(Y s-w s)
  have heq (s : ℝ) : Z s = X s-Y s := by dsimp [Z]; abel
  have hi : Z 0 = x-y := by
    rw [heq,hX.equation 0 ⟨le_rfl,ht.1.trans ht.2⟩,hY.equation 0 ⟨le_rfl,ht.1.trans ht.2⟩]
    simp
  have hc : ContinuousOn Z (Icc 0 t) :=
    ((hX.continuous.sub hw).sub (hY.continuous.sub hw)).mono (Icc_subset_Icc_right ht.2)
  have hz : ∀ s ∈ Ico 0 t, HasDerivWithinAt Z (u s (X s)-v s (Y s)) (Ici s) s := by
    intro s hs
    have hsT : s ∈ Ico 0 T := ⟨hs.1,hs.2.trans_le ht.2⟩
    exact (hX.compensated_derivative_right hsT).sub (hY.compensated_derivative_right hsT)
  have hb : ∀ s ∈ Ico 0 t, ‖u s (X s)-v s (Y s)‖ ≤ (K : ℝ)*‖Z s‖+δ := by
    intro s hs
    have hsT : s ∈ Icc 0 T := ⟨hs.1,hs.2.le.trans ht.2⟩
    have he : u s (X s)-v s (Y s) = (u s (X s)-u s (Y s))+(u s (Y s)-v s (Y s)) := by abel
    rw [he,heq]
    exact (norm_add_le _ _).trans (add_le_add
      (by simpa only [dist_eq_norm] using (hu s hsT).dist_le_mul (X s) (Y s)) (hd s hsT))
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le hc hz
    (show ‖Z 0‖ ≤ ‖x-y‖ by rw [hi]) hb t ⟨ht.1,le_rfl⟩
  simpa only [heq,sub_zero] using hg

theorem gronwallBound_linear_error (K δ t : ℝ) :
    gronwallBound 0 K δ t = δ * gronwallBound 0 K 1 t := by
  by_cases hK : K = 0
  · simp [hK,gronwallBound_K0]
  · simp only [gronwallBound_of_K_ne_0 hK,zero_mul,zero_add]
    ring

/-- The approximating drifts need only converge uniformly along this path.
The conclusion is uniform over the entire finite time interval. -/
theorem finiteTrajectory_tendsto_uniform_of_drift_approximation
    {u : ℕ → ℝ → E → E} {v : ℝ → E → E} {w Y : ℝ → E} {X : ℕ → ℝ → E}
    {x : E} {K : ℝ≥0} {T : ℝ}
    (hu : ∀ n s, LipschitzWith K (u n s)) (hw : ContinuousOn w (Icc 0 T))
    (hX : ∀ n, FiniteAdditiveTrajectory (u n) w x T (X n))
    (hY : FiniteAdditiveTrajectory v w x T Y)
    (hd : ∀ ε > 0, ∀ᶠ n in atTop, ∀ s ∈ Icc 0 T, ‖u n s (Y s)-v s (Y s)‖ ≤ ε) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ t ∈ Icc 0 T, ‖X n t-Y t‖ < ε := by
  intro ε hε
  let C := gronwallBound 0 K 1 T
  let δ := ε/(2*(|C|+1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  filter_upwards [hd δ hδ] with n hn t ht
  have he := (hX n).drift_stability (fun s _ => hu n s) hw hn hY ht
  simp only [sub_self,norm_zero] at he
  have hm := gronwallBound_mono (δ := 0) (K := K) (ε := δ) le_rfl hδ.le K.coe_nonneg ht.2
  have hc : δ*C < ε := by
    have hh : δ*(2*(|C|+1)) = ε := div_mul_cancel₀ ε (by positivity)
    have hp : 0 < δ*(|C|+1) := mul_pos hδ (by positivity)
    have hm' := mul_le_mul_of_nonneg_left (le_abs_self C) hδ.le
    nlinarith
  apply (he.trans hm).trans_lt
  rw [gronwallBound_linear_error (K : ℝ) δ T]
  exact hc

theorem finiteTrajectory_tendsto_of_drift_approximation
    {u : ℕ → ℝ → E → E} {v : ℝ → E → E} {w Y : ℝ → E} {X : ℕ → ℝ → E}
    {x : E} {K : ℝ≥0} {T t : ℝ}
    (hu : ∀ n s, LipschitzWith K (u n s)) (hw : ContinuousOn w (Icc 0 T))
    (hX : ∀ n, FiniteAdditiveTrajectory (u n) w x T (X n))
    (hY : FiniteAdditiveTrajectory v w x T Y)
    (hd : ∀ ε > 0, ∀ᶠ n in atTop, ∀ s ∈ Icc 0 T, ‖u n s (Y s)-v s (Y s)‖ ≤ ε)
    (ht : t ∈ Icc 0 T) : Tendsto (fun n => X n t) atTop (𝓝 (Y t)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [finiteTrajectory_tendsto_uniform_of_drift_approximation
    hu hw hX hY hd ε hε] with n hn
  simpa only [dist_eq_norm] using hn t ht

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem locallyUniformDrift_along_trajectory
    {u : ℕ → ℝ → E → E} {v : ℝ → E → E} {Y : ℝ → E} {T : ℝ}
    (hd : TendstoLocallyUniformly (fun n => Function.uncurry (u n)) (Function.uncurry v) atTop)
    (hY : ContinuousOn Y (Icc 0 T)) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ s ∈ Icc 0 T, ‖u n s (Y s)-v s (Y s)‖ ≤ ε := by
  let S := (fun s => (s,Y s)) '' Icc 0 T
  have hS : IsCompact S := isCompact_Icc.image_of_continuousOn (continuousOn_id.prodMk hY)
  have hu := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hS).mp
    hd.tendstoLocallyUniformlyOn
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu ε hε] with n hn s hs
  have he := hn (s,Y s) ⟨s,hs,rfl⟩
  simpa only [Function.uncurry_apply_pair,dist_eq_norm,norm_sub_rev] using he.le

theorem finiteTrajectory_tendsto_of_locallyUniform_drift
    {u : ℕ → ℝ → E → E} {v : ℝ → E → E} {w Y : ℝ → E} {X : ℕ → ℝ → E}
    {x : E} {K : ℝ≥0} {T t : ℝ}
    (hu : ∀ n s, LipschitzWith K (u n s)) (hw : ContinuousOn w (Icc 0 T))
    (hX : ∀ n, FiniteAdditiveTrajectory (u n) w x T (X n))
    (hY : FiniteAdditiveTrajectory v w x T Y)
    (hd : TendstoLocallyUniformly (fun n => Function.uncurry (u n)) (Function.uncurry v) atTop)
    (ht : t ∈ Icc 0 T) : Tendsto (fun n => X n t) atTop (𝓝 (Y t)) :=
  finiteTrajectory_tendsto_of_drift_approximation hu hw hX hY
    (locallyUniformDrift_along_trajectory hd hY.continuous) ht

omit [CompleteSpace E] in
theorem FiniteAdditiveTrajectory.sameInput_difference_bound
    {u v : ℝ → E → E} {w X Y : ℝ → E} {x : E} {T t M : ℝ}
    (hu : ∀ s ∈ Icc 0 T, ∀ z, ‖u s z‖ ≤ M) (hv : ∀ s ∈ Icc 0 T, ∀ z, ‖v s z‖ ≤ M)
    (hX : FiniteAdditiveTrajectory u w x T X) (hY : FiniteAdditiveTrajectory v w x T Y)
    (ht : t ∈ Icc 0 T) : ‖X t-Y t‖ ≤ 2*M*t := by
  have hix : ‖∫ s in (0 : ℝ)..t, u s (X s)‖ ≤ M*t := by
    have he := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := t) (f := fun s => u s (X s)) (fun s hs => by
        rw [uIoc_of_le ht.1] at hs
        exact hu s ⟨hs.1.le,hs.2.trans ht.2⟩ (X s))
    simpa [abs_of_nonneg ht.1,mul_comm] using he
  have hiy : ‖∫ s in (0 : ℝ)..t, v s (Y s)‖ ≤ M*t := by
    have he := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := t) (f := fun s => v s (Y s)) (fun s hs => by
        rw [uIoc_of_le ht.1] at hs
        exact hv s ⟨hs.1.le,hs.2.trans ht.2⟩ (Y s))
    simpa [abs_of_nonneg ht.1,mul_comm] using he
  have he : X t-Y t = (∫ s in (0 : ℝ)..t, u s (X s))-(∫ s in (0 : ℝ)..t, v s (Y s)) := by
    rw [hX.equation t ht,hY.equation t ht]
    abel
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith)

end SharpWasserstein
