module

public import SharpWasserstein.Compat
public import SharpWasserstein.GaussianEulerBackwardThird
public import SharpWasserstein.ConfigurationEuclidean

@[expose] public section

/-! Explicit norm and Lipschitz bounds on the actual diffusion generator from
bounds on the first three derivatives of a test. -/
noncomputable section
open scoped NNReal BigOperators
namespace SharpWasserstein
variable {d N : ℕ}

theorem coordinateVector_norm_le_one (i : Fin N) (a : Fin d) :
    ‖coordinateVector i a‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro j
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro c
  simp only [coordinateVector]
  split_ifs <;> norm_num

theorem lipschitz_clm_apply_const_of_norm_le_one
    {D E F : Type*} [PseudoMetricSpace D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {A : D → E →L[ℝ] F}
    {L : ℝ≥0} (hA : LipschitzWith L A) {e : E} (he : ‖e‖ ≤ 1) :
    LipschitzWith L (fun x => A x e) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, ← sub_apply]
  calc
    _ ≤ ‖A x-A y‖*‖e‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖A x-A y‖ := by nlinarith [norm_nonneg (A x-A y)]
    _ ≤ _ := by simpa only [dist_eq_norm] using hA.dist_le_mul x y

theorem coordinateDerivative_twice_eq_secondFDeriv {φ : Configuration d N → ℝ}
    (hφ : ContDiff ℝ 2 φ) (i : Fin N) (a : Fin d) (x : Configuration d N) :
    coordinateDerivative (coordinateDerivative φ i a) i a x =
      fderiv ℝ (fderiv ℝ φ) x (coordinateVector i a) (coordinateVector i a) := by
  have hd := ((hφ.fderiv_right (by norm_num) : ContDiff ℝ 1 _).differentiable (by norm_num) x).hasFDerivAt
  have h := hd.clm_apply (hasFDerivAt_const (coordinateVector i a) x)
  have he := h.fderiv
  simp only [ContinuousLinearMap.comp_zero, zero_add] at he
  unfold coordinateDerivative
  rw [he]
  rfl

theorem coordinateDerivative_lipschitz {φ : Configuration d N → ℝ} {L₁ : ℝ≥0}
    (hL₁ : LipschitzWith L₁ (fderiv ℝ φ)) (i : Fin N) (a : Fin d) :
    LipschitzWith L₁ (coordinateDerivative φ i a) :=
  lipschitz_clm_apply_const_of_norm_le_one hL₁ (coordinateVector_norm_le_one i a)

theorem coordinateDerivative_twice_lipschitz {φ : Configuration d N → ℝ}
    (hφ : ContDiff ℝ 2 φ) {L₂ : ℝ≥0} (hL₂ : LipschitzWith L₂ (fderiv ℝ (fderiv ℝ φ)))
    (i : Fin N) (a : Fin d) : LipschitzWith L₂ (coordinateDerivative (coordinateDerivative φ i a) i a) := by
  have he : coordinateDerivative (coordinateDerivative φ i a) i a = fun x =>
      fderiv ℝ (fderiv ℝ φ) x (coordinateVector i a) (coordinateVector i a) :=
    funext (coordinateDerivative_twice_eq_secondFDeriv hφ i a)
  rw [he]
  exact lipschitz_clm_apply_const_of_norm_le_one
    (lipschitz_clm_apply_const_of_norm_le_one hL₂ (coordinateVector_norm_le_one i a))
    (coordinateVector_norm_le_one i a)

theorem laplacian_lipschitz_of_derivatives {φ : Configuration d N → ℝ}
    (hφ : ContDiff ℝ 2 φ) {L₂ : ℝ≥0} (hL₂ : LipschitzWith L₂ (fderiv ℝ (fderiv ℝ φ))) :
    LipschitzWith ((N*d:ℕ)*L₂) (laplacian φ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  simp only [laplacian, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : Fin N, ∑ a : Fin d,
        ‖coordinateDerivative (coordinateDerivative φ i a) i a x-
          coordinateDerivative (coordinateDerivative φ i a) i a y‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
    _ ≤ ∑ _i : Fin N, ∑ _a : Fin d, (L₂:ℝ)*dist x y := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro a _
      simpa only [dist_eq_norm] using (coordinateDerivative_twice_lipschitz hφ hL₂ i a).dist_le_mul x y
    _ = _ := by simp [mul_assoc, Nat.cast_mul]

theorem laplacian_norm_le_of_derivatives {φ : Configuration d N → ℝ}
    (hφ : ContDiff ℝ 2 φ) {L₁ : ℝ≥0} (hL₁ : LipschitzWith L₁ (fderiv ℝ φ))
    (x : Configuration d N) : ‖laplacian φ x‖ ≤ (N*d:ℕ)*L₁ := by
  have hb (i : Fin N) (a : Fin d) :
      ‖coordinateDerivative (coordinateDerivative φ i a) i a x‖ ≤ L₁ := by
    rw [coordinateDerivative_twice_eq_secondFDeriv hφ]
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ φ) x (coordinateVector i a)‖*‖coordinateVector i a‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖fderiv ℝ (fderiv ℝ φ) x‖*‖coordinateVector i a‖*‖coordinateVector i a‖ := by
        gcongr
        exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ (L₁:ℝ)*1*1 := by
        gcongr
        · exact norm_fderiv_le_of_lipschitz ℝ hL₁
        · exact coordinateVector_norm_le_one i a
        · exact coordinateVector_norm_le_one i a
      _ = _ := by ring
  calc
    _ ≤ ∑ i : Fin N, ∑ a : Fin d, ‖coordinateDerivative (coordinateDerivative φ i a) i a x‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
    _ ≤ ∑ _i : Fin N, ∑ _a : Fin d, (L₁:ℝ) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun a _ => hb i a
    _ = _ := by simp [mul_assoc, Nat.cast_mul]

theorem generator_eq_laplacian_add_fderiv (b : Configuration d N → Configuration d N)
    (φ : Configuration d N → ℝ) (x : Configuration d N) :
    generator b φ x = laplacian φ x + fderiv ℝ φ x (b x) := by
  rw [generator, fderiv_eq_sum_coordinateDerivative]

theorem generator_norm_le_of_derivatives {φ : Configuration d N → ℝ}
    (hφ : ContDiff ℝ 2 φ) {L L₁ M : ℝ≥0} (hL : LipschitzWith L φ)
    (hL₁ : LipschitzWith L₁ (fderiv ℝ φ)) {b : Configuration d N → Configuration d N}
    (hb : ∀ x, ‖b x‖ ≤ M) (x : Configuration d N) :
    ‖generator b φ x‖ ≤ (N*d:ℕ)*L₁ + L*M := by
  rw [generator_eq_laplacian_add_fderiv]
  exact (norm_add_le _ _).trans (add_le_add (laplacian_norm_le_of_derivatives hφ hL₁ x)
    ((ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul (norm_fderiv_le_of_lipschitz ℝ hL) (hb x) (norm_nonneg _) L.coe_nonneg)))

theorem generator_lipschitz_of_derivatives {φ : Configuration d N → ℝ}
    (hφ : ContDiff ℝ 2 φ) {L L₁ L₂ K M : ℝ≥0} (hL : LipschitzWith L φ)
    (hL₁ : LipschitzWith L₁ (fderiv ℝ φ)) (hL₂ : LipschitzWith L₂ (fderiv ℝ (fderiv ℝ φ)))
    {b : Configuration d N → Configuration d N} (hb : LipschitzWith K b) (hM : ∀ x, ‖b x‖ ≤ M) :
    LipschitzWith ((N*d:ℕ)*L₂ + L₁*M + L*K) (generator b φ) := by
  have hadv : LipschitzWith (L₁*M+L*K) (fun x => fderiv ℝ φ x (b x)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm]
    have he : fderiv ℝ φ x (b x)-fderiv ℝ φ y (b y) =
        (fderiv ℝ φ x-fderiv ℝ φ y) (b x)+fderiv ℝ φ y (b x-b y) := by
      simp only [sub_apply, map_sub]
      ring
    rw [he]
    calc
      _ ≤ ‖(fderiv ℝ φ x-fderiv ℝ φ y) (b x)‖+‖fderiv ℝ φ y (b x-b y)‖ := norm_add_le _ _
      _ ≤ ‖fderiv ℝ φ x-fderiv ℝ φ y‖*‖b x‖+‖fderiv ℝ φ y‖*‖b x-b y‖ :=
        add_le_add (ContinuousLinearMap.le_opNorm _ _) (ContinuousLinearMap.le_opNorm _ _)
      _ ≤ ((L₁:ℝ)*‖x-y‖)*M + L*((K:ℝ)*‖x-y‖) :=
        add_le_add (mul_le_mul (hL₁.norm_sub_le x y) (hM x) (norm_nonneg _) (by positivity))
          (mul_le_mul (norm_fderiv_le_of_lipschitz ℝ hL) (hb.norm_sub_le x y) (norm_nonneg _) L.coe_nonneg)
      _ = _ := by simp only [NNReal.coe_add, NNReal.coe_mul, dist_eq_norm]; ring
  have h := (laplacian_lipschitz_of_derivatives hφ hL₂).add hadv
  have he : generator b φ = fun x => laplacian φ x + fderiv ℝ φ x (b x) :=
    funext (generator_eq_laplacian_add_fderiv b φ)
  rw [he]
  simpa only [add_assoc] using h

end SharpWasserstein
