module

public import SharpWasserstein.Compat
public import SharpWasserstein.EuclideanDrift
public import SharpWasserstein.ConfigurationEuclidean
public import SharpWasserstein.WeightedMarginal
public import SharpWasserstein.DriftEnergyIdentity

@[expose] public section

/-! Actual Euclidean external-force field. Configuration blocks use the existing
kernel on coordinate spaces; every stated norm is the true Euclidean norm. -/
noncomputable section
namespace SharpWasserstein.ExternalInteraction
open WeightedTangent WeightedMarginal BochnerIdentity PDEPairings
open scoped BigOperators InnerProductSpace ContDiff
variable {d m : ℕ}

/-- The extra-particle coordinate projection. -/
def suffixProjection (n k : ℕ) : Point (n+k) →L[ℝ] Point k where
  toFun x := WithLp.toLp 2 (fun i => x (i.natAdd n))
  map_add' x y := rfl
  map_smul' c x := rfl
  cont := (PiLp.continuous_toLp 2 (fun _ : Fin k => ℝ)).comp (by fun_prop)

theorem suffixProjection_apply (n k : ℕ) (x : Point (n+k)) :
    suffixProjection n k x = WithLp.toLp 2 (fun i => x (i.natAdd n)) := rfl

/-- Orthogonal coordinate decomposition, with no ambient sup-norm loss. -/
theorem prefix_suffix_norm_sq (n k : ℕ) (z : Point (n+k)) :
    ‖prefixProjection n k z‖^2 + ‖suffixProjection n k z‖^2 = ‖z‖^2 := by
  simp [EuclideanSpace.real_norm_sq_eq,prefixProjection_apply,suffixProjection_apply,Fin.sum_univ_add]

theorem prefix_norm_le (n k : ℕ) (z : Point (n+k)) : ‖prefixProjection n k z‖ ≤ ‖z‖ := by
  have hh := prefix_suffix_norm_sq n k z
  nlinarith [sq_nonneg ‖suffixProjection n k z‖,norm_nonneg (prefixProjection n k z),norm_nonneg z]

theorem suffix_norm_le (n k : ℕ) (z : Point (n+k)) : ‖suffixProjection n k z‖ ≤ ‖z‖ := by
  have hh := prefix_suffix_norm_sq n k z
  nlinarith [sq_nonneg ‖prefixProjection n k z‖,norm_nonneg (suffixProjection n k z),norm_nonneg z]

/-- The actual visible particle positions in a Euclidean configuration. -/
def positions (z : Point (m*d+d)) : Configuration d m :=
  (configurationEuclidean d m).symm (prefixProjection (m*d) d z)

/-- The actual external particle position. -/
def externalPosition (z : Point (m*d+d)) : Position d :=
  fun a => suffixProjection (m*d) d z a

/-- Stack the genuine interaction blocks against the same external particle. -/
def force (b : Position d → Position d → Position d) (z : Point (m*d+d)) : Point (m*d) :=
  configurationEuclidean d m (fun i => b (positions z i) (externalPosition z))

theorem force_smooth {b : Position d → Position d → Position d} (hb : BoundedSmoothKernel b) :
    ContDiff ℝ ∞ (force (m := m) b) := by
  apply (configurationEuclidean d m).contDiff.comp
  apply contDiff_pi.mpr
  intro i
  exact hb.smooth.comp ((contDiff_pi.mp
    ((configurationEuclidean d m).symm.contDiff.comp (prefixProjection (m*d) d).contDiff) i).prodMk
    (contDiff_pi.mpr (fun a =>
      (PiLp.proj 2 (fun _ : Fin d => ℝ) a).contDiff.comp (suffixProjection (m*d) d).contDiff)))

/-- A bounded kernel gives exactly `m` blocks, rather than a quadratic particle loss. -/
theorem force_norm_sq_le {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
    (hbound : KernelBounds b M L₁ L₂) (hM : 0 ≤ M) (z : Point (m*d+d)) :
    ‖force b z‖^2 ≤ (d:ℝ)*(m:ℝ)*M^2 := by
  rw [force,configurationEuclidean_norm_sq]
  calc
    (∑ i, ∑ a, (b (positions z i) (externalPosition z) a)^2) ≤
        ∑ _i : Fin m, (d:ℝ)*M^2 := by
      apply Finset.sum_le_sum
      intro i _
      apply (positionSq_le_norm_sq _).trans
      exact mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (norm_nonneg _) hM).mpr (hbound.value _ _)) (Nat.cast_nonneg d)
    _ = _ := by simp; ring

theorem externalPosition_sq_le (z : Point (m*d+d)) :
    positionSq (externalPosition z) ≤ ‖z‖^2 := by
  have he : positionSq (externalPosition z) = ‖suffixProjection (m*d) d z‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    rfl
  rw [he]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (suffix_norm_le _ _ _)

/-- Genuine Euclidean squared difference bound for the full external field. -/
theorem force_difference_sq_le {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
    (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
    (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (z z' : Point (m*d+d)) :
    ‖force b z-force b z'‖^2 ≤ 2*(d:ℝ)*
      (L₁^2*‖prefixProjection (m*d) d (z-z')‖^2+
        (m:ℝ)*L₂^2*‖suffixProjection (m*d) d (z-z')‖^2) := by
  rw [force,force,← map_sub,configurationEuclidean_norm_sq]
  calc
    (∑ i, ∑ a, (b (positions z i) (externalPosition z) a-
      b (positions z' i) (externalPosition z') a)^2) ≤
      ∑ i : Fin m, 2*(d:ℝ)*(L₁^2*positionSq (positions z i-positions z' i)+
        L₂^2*positionSq (externalPosition z-externalPosition z')) := by
      apply Finset.sum_le_sum
      intro i _
      exact kernel_joint_quadratic_difference hb hbound hL₁ hL₂ _ _ _ _
    _ = _ := by
      have hp : (∑ i : Fin m, positionSq (positions z i-positions z' i)) =
          ‖prefixProjection (m*d) d (z-z')‖^2 := by
        change (∑ i : Fin m, ∑ a : Fin d, ((positions z-positions z') i a)^2) = _
        rw [← configurationEuclidean_norm_sq]
        simp only [positions,← map_sub,ContinuousLinearEquiv.apply_symm_apply]
      have hy : positionSq (externalPosition z-externalPosition z') =
          ‖suffixProjection (m*d) d (z-z')‖^2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
        rfl
      simp only [mul_add,Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,
        Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,hp,hy]
      ring

/-- The derivative bound is linear in `m` after squaring. -/
theorem force_difference_sq_le_uniform {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
    (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
    (hm : 1 ≤ m) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (z z' : Point (m*d+d)) :
    ‖force b z-force b z'‖^2 ≤ (2*(d:ℝ)*(m:ℝ)*(L₁^2+L₂^2))*‖z-z'‖^2 := by
  apply (force_difference_sq_le hb hbound hL₁ hL₂ z z').trans
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hp := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (prefix_norm_le (m*d) d (z-z'))
  have hs := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (suffix_norm_le (m*d) d (z-z'))
  have h₁ := mul_le_mul_of_nonneg_left hp (sq_nonneg L₁)
  have h₂ := mul_le_mul_of_nonneg_left hs (mul_nonneg (Nat.cast_nonneg m) (sq_nonneg L₂))
  have h₃ := mul_le_mul_of_nonneg_right hmR (show 0 ≤ L₁^2*‖z-z'‖^2 by positivity)
  have hh : L₁^2*‖prefixProjection (m*d) d (z-z')‖^2+
      (m:ℝ)*L₂^2*‖suffixProjection (m*d) d (z-z')‖^2 ≤
      (m:ℝ)*(L₁^2+L₂^2)*‖z-z'‖^2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hh (show 0 ≤ 2*(d:ℝ) by positivity)]

/-- The genuine Fréchet Jacobian inherits the proved Euclidean Lipschitz bound. -/
theorem force_fderiv_norm_sq_le {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
    (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
    (hm : 1 ≤ m) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (z : Point (m*d+d)) :
    ‖fderiv ℝ (force b) z‖^2 ≤ 2*(d:ℝ)*(m:ℝ)*(L₁^2+L₂^2) := by
  let C : ℝ := 2*(d:ℝ)*(m:ℝ)*(L₁^2+L₂^2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hl : LipschitzWith ⟨Real.sqrt C,Real.sqrt_nonneg C⟩ (force (m := m) b) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm,dist_eq_norm]
    have hh := force_difference_sq_le_uniform hb hbound hm hL₁ hL₂ x y
    have hr := Real.sq_sqrt hC
    have hprod : 0 ≤ Real.sqrt C*‖x-y‖ := by positivity
    apply (sq_le_sq₀ (norm_nonneg _) hprod).mp
    nlinarith
  have hh := norm_fderiv_le_of_lipschitz ℝ hl (x₀ := z)
  have hs := (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg C)).mpr hh
  rwa [Real.sq_sqrt hC] at hs

end SharpWasserstein.ExternalInteraction
