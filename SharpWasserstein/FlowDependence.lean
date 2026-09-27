import SharpWasserstein.FiniteTrajectory

/-! Continuous dependence on both the initial value and the continuous
additive forcing, proved from the actual finite-horizon integral equations. -/

noncomputable section
open Set MeasureTheory
open scoped NNReal Interval

namespace SharpWasserstein

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Perturbing the forcing is controlled in its uniform norm. -/
theorem FiniteAdditiveTrajectory.forcing_stability
    {v : ℝ → E → E} {w z X Y : ℝ → E} {x₀ y₀ : E} {K : ℝ≥0} {T t δ : ℝ}
    (hv : ∀ s ∈ Icc 0 T, LipschitzWith K (v s))
    (hw : ContinuousOn w (Icc 0 T)) (hz : ContinuousOn z (Icc 0 T))
    (hnoise : ∀ s ∈ Icc 0 T, ‖w s - z s‖ ≤ δ)
    (hX : FiniteAdditiveTrajectory v w x₀ T X)
    (hY : FiniteAdditiveTrajectory v z y₀ T Y) (ht : t ∈ Icc 0 T) :
    ‖X t - Y t‖ ≤ (‖x₀ - y₀‖ + δ) * Real.exp ((K : ℝ) * t) := by
  let Z : ℝ → E := fun s => (X s - w s) - (Y s - z s)
  have hi : Z 0 = x₀ - y₀ := by
    dsimp [Z]
    rw [hX.equation 0 ⟨le_rfl, ht.1.trans ht.2⟩,
      hY.equation 0 ⟨le_rfl, ht.1.trans ht.2⟩]
    simp
  have hc : ContinuousOn Z (Icc 0 t) :=
    ((hX.continuous.sub hw).sub (hY.continuous.sub hz)).mono (Icc_subset_Icc_right ht.2)
  have hd : ∀ s ∈ Ico 0 t, HasDerivWithinAt Z
      (v s (X s) - v s (Y s)) (Ici s) s := by
    intro s hs
    have hsT : s ∈ Ico 0 T := ⟨hs.1, hs.2.trans_le ht.2⟩
    exact (hX.compensated_derivative_right hsT).sub (hY.compensated_derivative_right hsT)
  have heq : ∀ s, X s - Y s = Z s + (w s - z s) := by intro s; dsimp [Z]; abel
  have hnorm : ∀ s ∈ Icc 0 T, ‖X s - Y s‖ ≤ ‖Z s‖ + δ := by
    intro s hs
    rw [heq s]
    exact (norm_add_le _ _).trans (add_le_add le_rfl (hnoise s hs))
  have hb : ∀ s ∈ Ico 0 t,
      ‖v s (X s) - v s (Y s)‖ ≤ (K : ℝ) * ‖Z s‖ + (K : ℝ) * δ := by
    intro s hs
    have hsT : s ∈ Icc 0 T := ⟨hs.1, hs.2.le.trans ht.2⟩
    have hl := (hv s hsT).dist_le_mul (X s) (Y s)
    simp only [dist_eq_norm] at hl
    exact hl.trans (by simpa only [mul_add] using
      mul_le_mul_of_nonneg_left (hnorm s hsT) K.coe_nonneg)
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le hc hd
    (show ‖Z 0‖ ≤ ‖x₀ - y₀‖ by rw [hi]) hb t ⟨ht.1, le_rfl⟩
  have hfinal : gronwallBound ‖x₀ - y₀‖ K (K * δ) t + δ =
      (‖x₀ - y₀‖ + δ) * Real.exp ((K : ℝ) * t) := by
    by_cases hK : (K : ℝ) = 0
    · simp [hK, gronwallBound_K0]
    · rw [gronwallBound_of_K_ne_0 hK]
      field_simp
      ring
  calc
    ‖X t - Y t‖ ≤ ‖Z t‖ + δ := hnorm t ht
    _ ≤ gronwallBound ‖x₀ - y₀‖ K (K * δ) t + δ := by
      simpa only [sub_zero] using add_le_add hg (le_refl δ)
    _ = _ := hfinal

end SharpWasserstein
