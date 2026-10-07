module

public import SharpWasserstein.Compat
public import SharpWasserstein.EulerianTransportEquation
public import SharpWasserstein.SmoothBoundedCharacteristic

@[expose] public section

/-! Uniqueness of the genuine zero-diffusion weak continuity equation.
Deterministic Euler characteristic tests are constructed explicitly, their
errors telescope, and the mesh is sent to zero. No flow representation or
smoothness of an exact backward PDE solution is assumed. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal ContDiff BigOperators
namespace SharpWasserstein.EulerianTransport
open NoiseAverage
variable {d N : ℕ} {v : ℝ → Configuration d N → Configuration d N}
  {μ ν : ℝ → ProbabilityMeasure (Configuration d N)}

/-- A weak continuity equation restricts to a smaller time interval. -/
theorem WeakContinuity.mono {S T : ℝ} (h : WeakContinuity v μ T) (hST : S ≤ T) :
    WeakContinuity v μ S :=
  ⟨h.continuous, fun φ hφ hB s hs t ht => h.equation φ hφ hB s
    ⟨hs.1, hs.2.trans hST⟩ t ⟨ht.1, ht.2.trans hST⟩⟩

theorem WeakContinuity.uniform_backward_step_error {T : ℝ} (h : WeakContinuity v μ T)
    {K M : ℝ≥0} (hvC : Continuous (Function.uncurry v))
    (hv : ∀ r, LipschitzWith K (v r)) (hM : ∀ r x, ‖v r x‖ ≤ M)
    (L L₁ : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ≥0, (δ:ℝ) < η → ∀ s ∈ Icc 0 T, s+(δ:ℝ) ∈ Icc 0 T →
      ∀ φ : Configuration d N → ℝ, ContDiff ℝ ∞ φ → AllDerivativesBounded φ →
        LipschitzWith L φ → LipschitzWith L₁ (fderiv ℝ φ) →
        ‖(∫ x, φ x ∂(μ (s+δ) : Measure _))-(∫ x, step (v s) δ φ x ∂(μ s : Measure _))‖ ≤
          (δ:ℝ)*(ε+(L₁:ℝ)*(M:ℝ)^2*(δ:ℝ)) := by
  obtain ⟨η,hη,he⟩ := h.uniform_weak_step_error hvC hv hM L L₁ hε
  refine ⟨η,hη,fun δ hδ s hs hst φ hφ hB hL hL₁ => ?_⟩
  have hw := he s hs (s+δ) hst (le_add_of_nonneg_right δ.coe_nonneg)
    (by simpa only [add_sub_cancel_left] using hδ) φ hφ hB hL hL₁
  simp only [add_sub_cancel_left] at hw
  have hg := integral_step_error_bound (hv s) (hM s) hφ hB hL hL₁ (μ s : Measure _) δ
  have halg : (∫ x, φ x ∂(μ (s+δ) : Measure _))-(∫ x, step (v s) δ φ x ∂(μ s : Measure _)) =
      ((∫ x, φ x ∂(μ (s+δ) : Measure _))-(∫ x, φ x ∂(μ s : Measure _))-
        (δ:ℝ)*(∫ x, generator (v s) φ x ∂(μ s : Measure _)))-
      ((∫ x, step (v s) δ φ x ∂(μ s : Measure _))-(∫ x, φ x ∂(μ s : Measure _))-
        (δ:ℝ)*(∫ x, generator (v s) φ x ∂(μ s : Measure _))) := by ring
  rw [halg]
  exact (norm_sub_le _ _).trans ((add_le_add hw hg).trans_eq (by ring))

/-- The actual weak law is compared with the constructed finite Euler characteristic tests. -/
theorem WeakContinuity.backward_telescope_error (T : ℝ≥0) (h : WeakContinuity v μ T)
    {K K₁ M L L₁ : ℝ≥0} (hvC : Continuous (Function.uncurry v))
    (hv : ∀ t, ContDiff ℝ ∞ (v t)) (hvB : ∀ t, AllDerivativesBounded (v t))
    (hvL : ∀ t, LipschitzWith K (v t))
    (hv₁ : ∀ t, LipschitzWith K₁ (fderiv ℝ (v t)))
    (hM : ∀ t x, ‖v t x‖ ≤ M) {φ : Configuration d N → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφB : AllDerivativesBounded φ)
    (hL : LipschitzWith L φ) (hL₁ : LipschitzWith L₁ (fderiv ℝ φ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
      ∀ δ : ℝ≥0, ∀ n : ℕ, (n:ℝ≥0)*δ ≤ T → (δ:ℝ) < η →
      ‖(∫ x, φ x ∂(μ ((n:ℝ)*δ) : Measure _))-
        (∫ x, backward v δ φ n 0 x ∂(μ 0 : Measure _))‖ ≤
          (n:ℝ)*δ*(ε+C*(δ:ℝ)) := by
  obtain ⟨U,U₁,hU⟩ := uniform_backward_derivative_bounds hv hvB hvL hv₁ hφ hφB hL hL₁ T
  let C : ℝ := (U₁:ℝ)*(M:ℝ)^2
  refine ⟨C,by dsimp [C]; positivity,fun ε hε => ?_⟩
  obtain ⟨η,hη,he⟩ := h.uniform_backward_step_error hvC hvL hM U U₁ hε
  refine ⟨η,hη,fun δ n hn hδ => ?_⟩
  let a : ℕ → ℝ := fun j => ∫ x, backward v δ φ (n-j) j x ∂(μ ((j:ℝ)*δ) : Measure _)
  let B : ℝ := ε+C*(δ:ℝ)
  have htime (j : ℕ) (hj : j ≤ n) : (j:ℝ)*δ ∈ Icc 0 (T:ℝ) := by
    constructor
    · positivity
    · have hjn : (j:ℝ≥0)*δ ≤ T := (mul_le_mul_of_nonneg_right
        (show (j:ℝ≥0) ≤ (n:ℝ≥0) from Nat.cast_le.mpr hj) (show (0:ℝ≥0) ≤ δ from zero_le)).trans hn
      exact_mod_cast hjn
  have hstep {j : ℕ} (hj : j < n) : dist (a j) (a (j+1)) ≤ (δ:ℝ)*B := by
    let r := n-(j+1)
    have hr : (r:ℝ≥0)*δ ≤ T :=
      (mul_le_mul_of_nonneg_right (show (r:ℝ≥0) ≤ (n:ℝ≥0) from Nat.cast_le.mpr (Nat.sub_le _ _))
        (show (0:ℝ≥0) ≤ δ from zero_le)).trans hn
    have hreg := smooth_backward hv hvB δ hφ hφB r (j+1)
    have hLip := hU δ r (j+1) hr
    have hst : (j:ℝ)*δ+(δ:ℝ) ∈ Icc 0 (T:ℝ) := by
      convert htime (j+1) (by omega) using 1
      push_cast
      ring
    have hh := he δ hδ ((j:ℝ)*δ) (htime j (by omega)) hst
      (backward v δ φ r (j+1)) hreg.1 hreg.2 hLip.1 hLip.2
    have hnr : n-j = r+1 := by dsimp [r]; omega
    have htj : ((j+1:ℕ):ℝ)*(δ:ℝ) = (j:ℝ)*δ+(δ:ℝ) := by push_cast; ring
    rw [dist_comm,dist_eq_norm]
    dsimp only [a]
    rw [hnr,backward,htj]
    exact hh
  have ht := dist_le_range_sum_of_dist_le (f := a) (d := fun _ => (δ:ℝ)*B) n hstep
  have hsum : (∑ _j ∈ Finset.range n, (δ:ℝ)*B) = (n:ℝ)*δ*B := by simp [mul_assoc]
  rw [hsum,dist_comm,dist_eq_norm] at ht
  simpa only [a,Nat.sub_self,Nat.sub_zero,backward,Nat.cast_zero,zero_mul] using ht

theorem WeakContinuity.integral_eq_of_same_initial (T : ℝ≥0)
    (hμ : WeakContinuity v μ T) (hν : WeakContinuity v ν T)
    {K K₁ M L L₁ : ℝ≥0} (hvC : Continuous (Function.uncurry v))
    (hv : ∀ t, ContDiff ℝ ∞ (v t)) (hvB : ∀ t, AllDerivativesBounded (v t))
    (hvL : ∀ t, LipschitzWith K (v t))
    (hv₁ : ∀ t, LipschitzWith K₁ (fderiv ℝ (v t))) (hM : ∀ t x, ‖v t x‖ ≤ M)
    {φ : Configuration d N → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφB : AllDerivativesBounded φ)
    (hL : LipschitzWith L φ) (hL₁ : LipschitzWith L₁ (fderiv ℝ φ)) (h₀ : μ 0 = ν 0) :
    (∫ x, φ x ∂(μ T : Measure _)) = ∫ x, φ x ∂(ν T : Measure _) := by
  obtain ⟨C₁,_,h₁⟩ := hμ.backward_telescope_error T hvC hv hvB hvL hv₁ hM hφ hφB hL hL₁
  obtain ⟨C₂,_,h₂⟩ := hν.backward_telescope_error T hvC hv hvB hvL hv₁ hM hφ hφB hL hL₁
  let δ : ℕ → ℝ≥0 := fun n => T/(n+1)
  have hgrid (n : ℕ) : ((n+1:ℕ):ℝ≥0)*δ n = T := by
    dsimp [δ]
    push_cast
    rw [mul_comm]
    exact div_mul_cancel₀ _ (by positivity)
  have hgrid' (n : ℕ) : ((n+1:ℕ):ℝ)*(δ n:ℝ) = (T:ℝ) := by exact_mod_cast hgrid n
  have hmesh : Tendsto (fun n => (δ n:ℝ)) atTop (𝓝 0) := by
    change Tendsto (fun n : ℕ => (T:ℝ)/(n+1:ℝ)) atTop (𝓝 0)
    simpa only [mul_zero,div_eq_mul_inv,one_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (T:ℝ)
  have hbnd (ε : ℝ) (hε : 0 < ε) :
      ‖(∫ x, φ x ∂(μ T : Measure _))-(∫ x, φ x ∂(ν T : Measure _))‖ ≤ (T:ℝ)*(2*ε) := by
    obtain ⟨η₁,hη₁,hp⟩ := h₁ ε hε
    obtain ⟨η₂,hη₂,hq⟩ := h₂ ε hε
    have hevent : ∀ᶠ n in atTop,
        ‖(∫ x, φ x ∂(μ T : Measure _))-(∫ x, φ x ∂(ν T : Measure _))‖ ≤
          (T:ℝ)*(2*ε+(C₁+C₂)*(δ n:ℝ)) := by
      filter_upwards [hmesh.eventually (gt_mem_nhds hη₁),hmesh.eventually (gt_mem_nhds hη₂)] with n hn₁ hn₂
      have hp' := hp (δ n) (n+1) (hgrid n).le hn₁
      have hq' := hq (δ n) (n+1) (hgrid n).le hn₂
      rw [hgrid' n] at hp' hq'
      rw [← h₀] at hq'
      have he : (∫ x, φ x ∂(μ T : Measure _))-(∫ x, φ x ∂(ν T : Measure _)) =
          ((∫ x, φ x ∂(μ T : Measure _))-(∫ x, backward v (δ n) φ (n+1) 0 x ∂(μ 0 : Measure _)))-
          ((∫ x, φ x ∂(ν T : Measure _))-(∫ x, backward v (δ n) φ (n+1) 0 x ∂(μ 0 : Measure _))) := by ring
      rw [he]
      exact (norm_sub_le _ _).trans ((add_le_add hp' hq').trans_eq (by ring))
    have hlim : Tendsto (fun n => (T:ℝ)*(2*ε+(C₁+C₂)*(δ n:ℝ))) atTop (𝓝 ((T:ℝ)*(2*ε))) := by
      simpa only [mul_zero,add_zero] using ((hmesh.const_mul (C₁+C₂)).const_add (2*ε)).const_mul (T:ℝ)
    exact ge_of_tendsto hlim hevent
  have hz : ‖(∫ x, φ x ∂(μ T : Measure _))-(∫ x, φ x ∂(ν T : Measure _))‖ ≤ 0 := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hd : 0 < 2*(T:ℝ)+1 := by positivity
    have hh := hbnd (ε/(2*(T:ℝ)+1)) (div_pos hε hd)
    have hc : (T:ℝ)*(2*(ε/(2*(T:ℝ)+1))) ≤ ε := by
      have he := div_mul_cancel₀ ε hd.ne'
      nlinarith [div_pos hε hd]
    simpa only [zero_add] using hh.trans hc
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hz (norm_nonneg _)))

/-- The actual weak continuity equation determines the full probability law.
Only uniform first/second spatial bounds are used; time differentiability is absent. -/
theorem WeakContinuity.eq_of_same_initial {T : ℝ}
    (hμ : WeakContinuity v μ T) (hν : WeakContinuity v ν T)
    {K K₁ M : ℝ≥0} (hvC : Continuous (Function.uncurry v))
    (hv : ∀ t, ContDiff ℝ ∞ (v t)) (hvB : ∀ t, AllDerivativesBounded (v t))
    (hvL : ∀ t, LipschitzWith K (v t))
    (hv₁ : ∀ t, LipschitzWith K₁ (fderiv ℝ (v t))) (hM : ∀ t x, ‖v t x‖ ≤ M)
    (h₀ : μ 0 = ν 0) {t : ℝ} (ht : t ∈ Icc 0 T) : μ t = ν t := by
  apply ProbabilityMeasure.toMeasure_injective
  apply measure_eq_of_integral_smooth_bounded_eq
  intro φ hφ hφB
  have hφ' := (contDiff_infty_iff_fderiv.mp hφ).2
  obtain ⟨L,hL⟩ := hφB.lipschitz (hφ.differentiable (by simp))
  obtain ⟨L₁,hL₁⟩ := hφB.fderiv.lipschitz (hφ'.differentiable (by simp))
  exact (hμ.mono ht.2).integral_eq_of_same_initial ⟨t,ht.1⟩ (hν.mono ht.2)
    hvC hv hvB hvL hv₁ hM hφ hφB hL hL₁ h₀

end SharpWasserstein.EulerianTransport
