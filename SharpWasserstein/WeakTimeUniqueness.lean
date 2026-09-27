import SharpWasserstein.WeakTimeBackwardTelescope
import SharpWasserstein.SmoothBoundedCharacteristic

/-! Uniqueness of actual weak Fokker--Planck evolutions for jointly continuous
bounded time-dependent drifts with uniform spatial derivative bounds. The
proof compares actual time-dependent Gaussian Euler tests and lets the mesh vanish. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal ContDiff
namespace SharpWasserstein.WeakEvolution
open WeightedTangent NoiseAverage BackwardEuler
variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  {v : ℝ → Configuration d N → Configuration d N} {P Q : ℝ → Measure (Configuration d N)}
  (hP : WeakEvolution v P) (hQ : WeakEvolution v Q)
include hP hQ

theorem integral_eq_of_same_initial_time_bounded_derivatives {K K₁ K₂ M L L₁ L₂ : ℝ≥0}
    (hvC : Continuous (Function.uncurry v))
    (hv : ∀ t, ContDiff ℝ ∞ (v t)) (hvB : ∀ t, AllDerivativesBounded (v t))
    (hvL : ∀ t, LipschitzWith K (v t))
    (hv₁ : ∀ t, LipschitzWith K₁ (fderiv ℝ (v t)))
    (hv₂ : ∀ t, LipschitzWith K₂ (fderiv ℝ (fderiv ℝ (v t))))
    (hM : ∀ t x, ‖v t x‖ ≤ M) {φ : Configuration d N → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφB : AllDerivativesBounded φ)
    (hL : LipschitzWith L φ) (hL₁ : LipschitzWith L₁ (fderiv ℝ φ))
    (hL₂ : LipschitzWith L₂ (fderiv ℝ (fderiv ℝ φ))) (h₀ : P 0 = Q 0) (T : ℝ≥0) :
    (∫ x, φ x ∂P T) = ∫ x, φ x ∂Q T := by
  obtain ⟨C₁,_,h₁⟩ := time_backward_telescope_error hP hvC hv hvB hvL hv₁ hv₂ hM hφ hφB hL hL₁ hL₂ T
  obtain ⟨C₂,_,h₂⟩ := time_backward_telescope_error hQ hvC hv hvB hvL hv₁ hv₂ hM hφ hφB hL hL₁ hL₂ T
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
  let R : ℕ → ℝ := fun n => (M:ℝ)*δ n+Real.sqrt (2*(δ n:ℝ))*FrozenGaussian.noiseFirstMoment d N
  have hR : Tendsto R atTop (𝓝 0) := by
    simpa only [mul_zero,Real.sqrt_zero,zero_mul,zero_add] using
      (hmesh.const_mul (M:ℝ)).add (((hmesh.const_mul 2).sqrt).mul_const (FrozenGaussian.noiseFirstMoment d N))
  have hbnd (ε : ℝ) (hε : 0 < ε) : ‖(∫ x, φ x ∂P T)-(∫ x, φ x ∂Q T)‖ ≤ (T:ℝ)*(2*ε) := by
    obtain ⟨η₁,hη₁,hp⟩ := h₁ ε hε
    obtain ⟨η₂,hη₂,hq⟩ := h₂ ε hε
    have hevent : ∀ᶠ n in atTop, ‖(∫ x, φ x ∂P T)-(∫ x, φ x ∂Q T)‖ ≤
        (T:ℝ)*(2*ε+(C₁+C₂)*R n) := by
      filter_upwards [hmesh.eventually (gt_mem_nhds hη₁),hmesh.eventually (gt_mem_nhds hη₂)] with n hn₁ hn₂
      have hp' := hp (δ n) (n+1) (hgrid n).le hn₁
      have hq' := hq (δ n) (n+1) (hgrid n).le hn₂
      rw [hgrid' n] at hp' hq'
      rw [← h₀] at hq'
      have he : (∫ x, φ x ∂P T)-(∫ x, φ x ∂Q T) =
          ((∫ x, φ x ∂P T)-(∫ x, backwardTime v (δ n) φ (n+1) 0 x ∂P 0))-
          ((∫ x, φ x ∂Q T)-(∫ x, backwardTime v (δ n) φ (n+1) 0 x ∂P 0)) := by ring
      rw [he]
      exact (norm_sub_le _ _).trans ((add_le_add hp' hq').trans_eq (by dsimp [R]; ring))
    have hlim : Tendsto (fun n => (T:ℝ)*(2*ε+(C₁+C₂)*R n)) atTop (𝓝 ((T:ℝ)*(2*ε))) := by
      simpa only [mul_zero,add_zero] using ((hR.const_mul (C₁+C₂)).const_add (2*ε)).const_mul (T:ℝ)
    exact ge_of_tendsto hlim hevent
  have hz : ‖(∫ x, φ x ∂P T)-(∫ x, φ x ∂Q T)‖ ≤ 0 := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hd : 0 < 2*(T:ℝ)+1 := by positivity
    have hh := hbnd (ε/(2*(T:ℝ)+1)) (div_pos hε hd)
    have hc : (T:ℝ)*(2*(ε/(2*(T:ℝ)+1))) ≤ ε := by
      have he := div_mul_cancel₀ ε hd.ne'
      nlinarith [div_pos hε hd]
    simpa only [zero_add] using hh.trans hc
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hz (norm_nonneg _)))

/-- Equality of full probability laws for the actual time-dependent weak
solutions. Uniform bounds on the first three spatial derivatives suffice;
no derivative with respect to time is required. -/
theorem eq_of_same_initial_time_dependent {K K₁ K₂ M : ℝ≥0}
    (hvC : Continuous (Function.uncurry v))
    (hv : ∀ t, ContDiff ℝ ∞ (v t)) (hvB : ∀ t, AllDerivativesBounded (v t))
    (hvL : ∀ t, LipschitzWith K (v t))
    (hv₁ : ∀ t, LipschitzWith K₁ (fderiv ℝ (v t)))
    (hv₂ : ∀ t, LipschitzWith K₂ (fderiv ℝ (fderiv ℝ (v t))))
    (hM : ∀ t x, ‖v t x‖ ≤ M) (h₀ : P 0 = Q 0)
    {t : ℝ} (ht : 0 ≤ t) : P t = Q t := by
  letI := hP.probability t ht
  letI := hQ.probability t ht
  apply measure_eq_of_integral_smooth_bounded_eq
  intro φ hφ hφB
  have hφ' := (contDiff_infty_iff_fderiv.mp hφ).2
  have hφ'' := (contDiff_infty_iff_fderiv.mp hφ').2
  obtain ⟨L,hL⟩ := hφB.lipschitz (hφ.differentiable (by simp))
  obtain ⟨L₁,hL₁⟩ := hφB.fderiv.lipschitz (hφ'.differentiable (by simp))
  obtain ⟨L₂,hL₂⟩ := hφB.fderiv.fderiv.lipschitz (hφ''.differentiable (by simp))
  exact integral_eq_of_same_initial_time_bounded_derivatives hP hQ hvC hv hvB hvL hv₁ hv₂
    hM hφ hφB hL hL₁ hL₂ h₀ ⟨t,ht⟩

end SharpWasserstein.WeakEvolution
