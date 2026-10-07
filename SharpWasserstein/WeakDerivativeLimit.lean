module

public import SharpWasserstein.Compat
public import SharpWasserstein.DenseVariational

@[expose] public section

/-! Construct weak derivatives of a strong Hilbert-space limit from genuine
distributional identities and a uniform derivative bound. No weakly convergent
subsequence or pre-existing weak derivative is assumed. -/
noncomputable section
open Set Filter
open scoped InnerProductSpace Topology
namespace SharpWasserstein.WeakDerivativeLimit

variable {T H : Type*} [AddCommGroup T] [Module ℝ T]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def testClosure (e : T →ₗ[ℝ] H) : Submodule ℝ H := e.range.topologicalClosure

def intoClosure (e : T →ₗ[ℝ] H) : T →ₗ[ℝ] testClosure e :=
  e.codRestrict (testClosure e) (fun φ => e.range.le_topologicalClosure (LinearMap.mem_range_self e φ))

theorem dense_intoClosure (e : T →ₗ[ℝ] H) : DenseRange (intoClosure e) := by
  rw [DenseRange,Subtype.dense_iff]
  intro v hv
  change v ∈ closure (Set.range e) at hv
  convert hv using 1
  congr 1
  ext w
  simp only [Set.mem_image,Set.mem_range]
  constructor
  · rintro ⟨z,⟨φ,rfl⟩,rfl⟩
    exact ⟨φ,rfl⟩
  · rintro ⟨φ,rfl⟩
    exact ⟨intoClosure e φ,⟨φ,rfl⟩,rfl⟩

theorem exists_representative_of_bound [CompleteSpace H]
    (σ : T →ₗ[ℝ] ℝ) (e : T →ₗ[ℝ] H) {C : ℝ} (hC : 0 ≤ C)
    (hσ : ∀ φ, ‖σ φ‖ ≤ C*‖e φ‖) :
    ∃ v : H, ‖v‖ ≤ C ∧ ∀ φ, ⟪v,e φ⟫_ℝ = σ φ := by
  letI : CompleteSpace (testClosure e) := (Submodule.isClosed_topologicalClosure e.range).completeSpace_coe
  let ℓ := σ.extendOfNorm (intoClosure e)
  let v := TangentEnergy.rieszRepresentative ℓ
  have hv : ‖v‖ ≤ C := by
    have hn := LinearMap.norm_extendOfNorm_apply_le (f := σ) (dense_intoClosure e) C hσ v
    change ‖ℓ v‖ ≤ C*‖v‖ at hn
    rw [← TangentEnergy.inner_rieszRepresentative ℓ v] at hn
    change ‖⟪v,v⟫_ℝ‖ ≤ C*‖v‖ at hn
    rw [real_inner_self_eq_norm_sq,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)] at hn
    nlinarith [norm_nonneg v]
  refine ⟨v.val,hv,?_⟩
  intro φ
  change ⟪v,intoClosure e φ⟫_ℝ = σ φ
  rw [TangentEnergy.inner_rieszRepresentative]
  exact LinearMap.extendOfNorm_eq (dense_intoClosure e) ⟨C,hσ⟩ φ

variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]

def distribution (derivative : T →ₗ[ℝ] H₀) (u : H₀) : T →ₗ[ℝ] ℝ where
  toFun φ := -⟪u,derivative φ⟫_ℝ
  map_add' φ ψ := by simp only [map_add,inner_add_right]; ring
  map_smul' c φ := by simp [inner_smul_right]

/-- A uniform bound and actual test identities produce a bounded weak
derivative of the strong limit. The identities may hold only eventually for
each test, so finite Fourier/Galerkin approximations are covered. -/
theorem exists_weakDerivative_of_strong_limit {ι : Type*} {L : Filter ι} [NeBot L]
    (value : T →ₗ[ℝ] H₁) (derivative : T →ₗ[ℝ] H₀)
    {u : ι → H₀} {uLimit : H₀} (hu : Tendsto u L (𝓝 uLimit))
    (v : ι → H₁) {C : ℝ} (hC : 0 ≤ C) (hv : ∀ᶠ k in L, ‖v k‖ ≤ C)
    (he : ∀ φ, ∀ᶠ k in L, ⟪v k,value φ⟫_ℝ = -⟪u k,derivative φ⟫_ℝ) :
    ∃ vLimit : H₁, ‖vLimit‖ ≤ C ∧ ∀ φ, ⟪vLimit,value φ⟫_ℝ = -⟪uLimit,derivative φ⟫_ℝ := by
  apply exists_representative_of_bound (distribution derivative uLimit) value hC
  intro φ
  have hp : Tendsto (fun k => ‖-⟪u k,derivative φ⟫_ℝ‖) L (𝓝 ‖-⟪uLimit,derivative φ⟫_ℝ‖) :=
    ((hu.inner tendsto_const_nhds).neg).norm
  apply le_of_tendsto hp
  filter_upwards [hv,he φ] with k hk heq
  rw [← heq]
  exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hk (norm_nonneg _))

end SharpWasserstein.WeakDerivativeLimit
