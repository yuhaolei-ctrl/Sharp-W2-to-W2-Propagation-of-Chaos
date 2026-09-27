import SharpWasserstein.WeakBackwardEulerTelescope
import SharpWasserstein.SmoothBoundedCharacteristic

/-! Uniqueness of the stated weak Fokker--Planck evolution for an autonomous
smooth drift with bounded derivatives. The proof compares two arbitrary weak
solutions by actual backward Gaussian Euler tests and lets the mesh vanish. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal ContDiff
namespace SharpWasserstein.WeakEvolution
open WeightedTangent NoiseAverage BackwardEuler
variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  {b : Configuration d N → Configuration d N} {P Q : ℝ → Measure (Configuration d N)}
  (hP : WeakEvolution (fun _ => b) P) (hQ : WeakEvolution (fun _ => b) Q)
include hP hQ

theorem integral_eq_of_same_initial_bounded_derivatives {K K₁ K₂ M L L₁ L₂ : ℝ≥0}
    (hb : ContDiff ℝ ∞ b) (hbB : AllDerivativesBounded b) (hbL : LipschitzWith K b)
    (hb₁ : LipschitzWith K₁ (fderiv ℝ b)) (hb₂ : LipschitzWith K₂ (fderiv ℝ (fderiv ℝ b)))
    (hM : ∀ x, ‖b x‖ ≤ M) {φ : Configuration d N → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφB : AllDerivativesBounded φ)
    (hL : LipschitzWith L φ) (hL₁ : LipschitzWith L₁ (fderiv ℝ φ))
    (hL₂ : LipschitzWith L₂ (fderiv ℝ (fderiv ℝ φ))) (h₀ : P 0 = Q 0) (T : ℝ≥0) :
    (∫ x, φ x ∂P T) = ∫ x, φ x ∂Q T := by
  obtain ⟨C₁,_,h₁⟩ := backward_telescope_error hP hb hbB hbL hb₁ hb₂ hM hφ hφB hL hL₁ hL₂ T
  obtain ⟨C₂,_,h₂⟩ := backward_telescope_error hQ hb hbB hbL hb₁ hb₂ hM hφ hφB hL hL₁ hL₂ T
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
          ((∫ x, φ x ∂P T)-(∫ x, backward b (δ n) φ (n+1) x ∂P 0))-
          ((∫ x, φ x ∂Q T)-(∫ x, backward b (δ n) φ (n+1) x ∂P 0)) := by ring
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

/-- The full probability laws coincide at every nonnegative time. Spatial
derivative constants used only by the uniqueness argument are derived from
the stated actual bounded smoothness, not added as hypotheses. -/
theorem eq_of_same_initial_autonomous
    (hb : ContDiff ℝ ∞ b) (hbB : AllDerivativesBounded b) (h₀ : P 0 = Q 0)
    {t : ℝ} (ht : 0 ≤ t) : P t = Q t := by
  letI := hP.probability t ht
  letI := hQ.probability t ht
  apply measure_eq_of_integral_smooth_bounded_eq
  intro φ hφ hφB
  have hb' := (contDiff_infty_iff_fderiv.mp hb).2
  have hb'' := (contDiff_infty_iff_fderiv.mp hb').2
  obtain ⟨K,hK⟩ := hbB.lipschitz (hb.differentiable (by simp))
  obtain ⟨K₁,hK₁⟩ := hbB.fderiv.lipschitz (hb'.differentiable (by simp))
  obtain ⟨K₂,hK₂⟩ := hbB.fderiv.fderiv.lipschitz (hb''.differentiable (by simp))
  obtain ⟨M,hM₀,hM⟩ := hbB.bounded
  have hφ' := (contDiff_infty_iff_fderiv.mp hφ).2
  have hφ'' := (contDiff_infty_iff_fderiv.mp hφ').2
  obtain ⟨L,hL⟩ := hφB.lipschitz (hφ.differentiable (by simp))
  obtain ⟨L₁,hL₁⟩ := hφB.fderiv.lipschitz (hφ'.differentiable (by simp))
  obtain ⟨L₂,hL₂⟩ := hφB.fderiv.fderiv.lipschitz (hφ''.differentiable (by simp))
  exact integral_eq_of_same_initial_bounded_derivatives hP hQ hb hbB hK hK₁ hK₂
    (M := ⟨M,hM₀⟩) hM hφ hφB hL hL₁ hL₂ h₀ ⟨t,ht⟩

end SharpWasserstein.WeakEvolution
