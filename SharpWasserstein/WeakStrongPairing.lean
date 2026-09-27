import SharpWasserstein.WeakDerivativeClosure

/-! A bounded weak factor can be paired with a strongly converging factor.
Only the fixed limiting test pairing is required to converge. -/

noncomputable section
namespace SharpWasserstein.WeakStrongPairing
open Filter
open scoped Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Joint pairing convergence derived from a uniform bound, one weak pairing,
and genuine strong convergence of the second factor. -/
theorem inner_tendsto {ι : Type*} {L : Filter ι} {v w : ι → H} {vLimit wLimit : H}
    {C : ℝ} (hv : ∀ᶠ k in L, ‖v k‖ ≤ C)
    (hw : Tendsto w L (𝓝 wLimit))
    (ht : Tendsto (fun k => ⟪v k, wLimit⟫_ℝ) L (𝓝 ⟪vLimit, wLimit⟫_ℝ)) :
    Tendsto (fun k => ⟪v k, w k⟫_ℝ) L (𝓝 ⟪vLimit, wLimit⟫_ℝ) := by
  have hn : Tendsto (fun k => ‖⟪v k, w k - wLimit⟫_ℝ‖) L (𝓝 (0 : ℝ)) := by
    apply squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) _
      (show Tendsto (fun k => C * ‖w k - wLimit‖) L (𝓝 (0 : ℝ)) from by
        simpa using ((hw.sub (tendsto_const_nhds (x := wLimit))).norm.const_mul C))
    filter_upwards [hv] with k hk
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hk (norm_nonneg _))
  have hr : Tendsto (fun k => ⟪v k, w k - wLimit⟫_ℝ) L (𝓝 (0 : ℝ)) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hn
  have h := ht.add hr
  convert h using 1
  · funext k
    simp only [inner_sub_right]
    ring
  · simp

end SharpWasserstein.WeakStrongPairing
