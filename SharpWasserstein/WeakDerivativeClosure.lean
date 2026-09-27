import SharpWasserstein.WeakDerivativeLimit

/-! Closed test-space representatives and extension of weak convergence from
actual tests to their Hilbert closure. These are used for products with weak
Hessians, without postulating arbitrary `L²` test density. -/

noncomputable section
namespace SharpWasserstein.WeakDerivativeClosure
open Set Filter WeakDerivativeLimit
open scoped InnerProductSpace Topology

variable {T H : Type*} [AddCommGroup T] [Module ℝ T]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Projection preserves all test pairings and cannot increase the representing norm. -/
theorem exists_representative_in_testClosure (e : T →ₗ[ℝ] H) (v : H) :
    ∃ w : H, w ∈ testClosure e ∧ ‖w‖ ≤ ‖v‖ ∧ ∀ φ, ⟪w, e φ⟫_ℝ = ⟪v, e φ⟫_ℝ := by
  let S := testClosure e
  letI : CompleteSpace S := (Submodule.isClosed_topologicalClosure e.range).completeSpace_coe
  refine ⟨(S.orthogonalProjectionOnto v : H), (S.orthogonalProjectionOnto v).property,
    S.norm_orthogonalProjectionOnto_apply_le v, fun φ => ?_⟩
  have hφ : e φ ∈ S := e.range.le_topologicalClosure (LinearMap.mem_range_self e φ)
  change ⟪S.orthogonalProjectionOnto v, (⟨e φ, hφ⟩ : S)⟫_ℝ = _
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]

variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]

/-- The weak derivative of the strong limit can be chosen in the actual closed test space. -/
theorem exists_weakDerivative_in_testClosure {ι : Type*} {L : Filter ι} [NeBot L]
    (value : T →ₗ[ℝ] H₁) (derivative : T →ₗ[ℝ] H₀)
    {u : ι → H₀} {uLimit : H₀} (hu : Tendsto u L (𝓝 uLimit))
    (v : ι → H₁) {C : ℝ} (hC : 0 ≤ C) (hv : ∀ᶠ k in L, ‖v k‖ ≤ C)
    (he : ∀ φ, ∀ᶠ k in L, ⟪v k,value φ⟫_ℝ = -⟪u k,derivative φ⟫_ℝ) :
    ∃ w : H₁, w ∈ testClosure value ∧ ‖w‖ ≤ C ∧
      ∀ φ, ⟪w,value φ⟫_ℝ = -⟪uLimit,derivative φ⟫_ℝ := by
  obtain ⟨w, hw, heq⟩ := exists_weakDerivative_of_strong_limit value derivative hu v hC hv he
  obtain ⟨w', hw'mem, hw', hw'eq⟩ := exists_representative_in_testClosure value w
  exact ⟨w', hw'mem, hw'.trans hw, fun φ => (hw'eq φ).trans (heq φ)⟩

omit [CompleteSpace H] in
/-- Uniform boundedness extends convergence of test pairings to every point of
those tests' actual Hilbert closure. No weak convergence is assumed. -/
theorem inner_tendsto_of_tests {ι : Type*} {L : Filter ι}
    (e : T →ₗ[ℝ] H) {v : ι → H} {w : H} {C : ℝ} (hC : 0 ≤ C)
    (hv : ∀ᶠ k in L, ‖v k‖ ≤ C)
    (he : ∀ φ, Tendsto (fun k => ⟪v k, e φ⟫_ℝ) L (𝓝 ⟪w, e φ⟫_ℝ))
    (z : H) (hz : z ∈ testClosure e) :
    Tendsto (fun k => ⟪v k, z⟫_ℝ) L (𝓝 ⟪w, z⟫_ℝ) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  change z ∈ e.range.topologicalClosure at hz
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff] at hz
  obtain ⟨z', hz', hdist⟩ := hz (ε / (2 * (C + ‖w‖ + 1))) (by positivity)
  obtain ⟨φ, rfl⟩ := hz'
  have ht := Metric.tendsto_nhds.mp (he φ) (ε / 2) (by positivity)
  filter_upwards [hv, ht] with k hk hnear
  have heq : ⟪v k, z⟫_ℝ - ⟪w, z⟫_ℝ = (⟪v k, e φ⟫_ℝ - ⟪w, e φ⟫_ℝ) +
      (⟪v k, z - e φ⟫_ℝ - ⟪w, z - e φ⟫_ℝ) := by simp only [inner_sub_right]; ring
  have hrem : ‖⟪v k, z - e φ⟫_ℝ - ⟪w, z - e φ⟫_ℝ‖ ≤
      (C + ‖w‖) * ‖z - e φ‖ := by
    calc
      _ ≤ ‖⟪v k, z - e φ⟫_ℝ‖ + ‖⟪w, z - e φ⟫_ℝ‖ := norm_sub_le _ _
      _ ≤ ‖v k‖ * ‖z - e φ‖ + ‖w‖ * ‖z - e φ‖ :=
        add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
      _ ≤ _ := by nlinarith [norm_nonneg (z - e φ)]
  rw [dist_eq_norm] at hnear hdist ⊢
  rw [heq]
  have hsmall : (C + ‖w‖) * ‖z - e φ‖ < ε / 2 := by
    have hd := (lt_div_iff₀ (show 0 < 2 * (C + ‖w‖ + 1) by positivity)).mp hdist
    nlinarith [norm_nonneg (z - e φ)]
  exact (norm_add_le _ _).trans_lt (by linarith)

end SharpWasserstein.WeakDerivativeClosure
