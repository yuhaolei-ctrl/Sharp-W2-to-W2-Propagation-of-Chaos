import SharpWasserstein.DerivativeCompositionBounds
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! Third-order chain-rule estimates for the actual Fréchet derivative. -/
noncomputable section
set_option maxHeartbeats 400000
open scoped NNReal
namespace SharpWasserstein
variable {D E F G : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

omit [NormedSpace ℝ D] in
theorem lipschitz_clm_comp_bounded {A : D → F →L[ℝ] G} {B : D → E →L[ℝ] F}
    {A₀ A₁ B₀ B₁ : ℝ≥0} (ha : ∀ x, ‖A x‖ ≤ A₀) (hb : ∀ x, ‖B x‖ ≤ B₀)
    (hA : LipschitzWith A₁ A) (hB : LipschitzWith B₁ B) :
    LipschitzWith (A₁*B₀ + A₀*B₁) (fun x => (A x).comp (B x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  have heq : (A x).comp (B x) - (A y).comp (B y) =
      (A x-A y).comp (B x) + (A y).comp (B x-B y) := by
    rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
    abel
  rw [heq]
  calc
    _ ≤ ‖(A x-A y).comp (B x)‖ + ‖(A y).comp (B x-B y)‖ := norm_add_le _ _
    _ ≤ ‖A x-A y‖ * ‖B x‖ + ‖A y‖ * ‖B x-B y‖ :=
      add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _)
    _ ≤ ((A₁:ℝ)*‖x-y‖)*B₀ + A₀*((B₁:ℝ)*‖x-y‖) :=
      add_le_add (mul_le_mul (hA.norm_sub_le x y) (hb x) (norm_nonneg _) (by positivity))
        (mul_le_mul (ha y) (hB.norm_sub_le x y) (norm_nonneg _) A₀.coe_nonneg)
    _ = _ := by simp only [NNReal.coe_add, NNReal.coe_mul, dist_eq_norm]; ring

theorem compL_lipschitz_one : LipschitzWith 1 (ContinuousLinearMap.compL ℝ E F G) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  rw [dist_eq_norm, ← map_sub]
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  exact (ContinuousLinearMap.compL ℝ E F G (a-b)).opNorm_le_bound (norm_nonneg _)
    (fun z => ContinuousLinearMap.opNorm_comp_le (a-b) z)

theorem compL_flip_lipschitz_one : LipschitzWith 1 (ContinuousLinearMap.compL ℝ E F G).flip := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  rw [dist_eq_norm, ← map_sub]
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  apply ((ContinuousLinearMap.compL ℝ E F G).flip (a-b)).opNorm_le_bound (norm_nonneg _)
  intro z
  simpa only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply, mul_comm] using
    ContinuousLinearMap.opNorm_comp_le z (a-b)

/-- Genuine third derivative chain-rule coefficient, expressed as a Lipschitz
bound on the actual second derivative. -/
theorem lipschitz_secondFDeriv_comp {f : E → F} {g : D → E}
    {L₀ L₁ L₂ K₀ K₁ K₂ : ℝ≥0} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hf₀ : LipschitzWith L₀ f) (hf₁ : LipschitzWith L₁ (fderiv ℝ f))
    (hf₂ : LipschitzWith L₂ (fderiv ℝ (fderiv ℝ f)))
    (hg₀ : LipschitzWith K₀ g) (hg₁ : LipschitzWith K₁ (fderiv ℝ g))
    (hg₂ : LipschitzWith K₂ (fderiv ℝ (fderiv ℝ g))) :
    LipschitzWith (L₂*K₀^3 + 3*L₁*K₀*K₁ + L₀*K₂)
      (fderiv ℝ (fderiv ℝ (f ∘ g))) := by
  let c := fderiv ℝ f ∘ g
  let b := fderiv ℝ g
  have hfd := hf.differentiable (by norm_num)
  have hgd := hg.differentiable (by norm_num)
  have hdfd : Differentiable ℝ (fderiv ℝ f) := (hf.fderiv_right (by norm_num) : ContDiff ℝ 1 _).differentiable (by norm_num)
  have hdbd : Differentiable ℝ b := (hg.fderiv_right (by norm_num) : ContDiff ℝ 1 _).differentiable (by norm_num)
  have hcd : Differentiable ℝ c := hdfd.comp hgd
  have hcL : LipschitzWith (L₁*K₀) c := hf₁.comp hg₀
  have hdcL : LipschitzWith (L₂*K₀^2+L₁*K₁) (fderiv ℝ c) :=
    lipschitz_fderiv_comp hdfd hgd hf₁ hf₂ hg₀ hg₁
  have heq : fderiv ℝ (f ∘ g) = fun x => (c x).comp (b x) := by
    funext x
    exact fderiv_comp x (hfd _) (hgd x)
  rw [heq]
  have hder : fderiv ℝ (fun x => (c x).comp (b x)) = fun x =>
      (ContinuousLinearMap.compL ℝ D E F (c x)).comp (fderiv ℝ b x) +
      ((ContinuousLinearMap.compL ℝ D E F).flip (b x)).comp (fderiv ℝ c x) := by
    funext x
    exact fderiv_clm_comp (hcd x) (hdbd x)
  rw [hder]
  have ha : ∀ x, ‖ContinuousLinearMap.compL ℝ D E F (c x)‖ ≤ L₀ := by
    intro x
    have hn := (compL_lipschitz_one (E := D) (F := E) (G := F)).norm_sub_le (c x) 0
    simp only [map_zero, sub_zero, NNReal.coe_one, one_mul] at hn
    exact hn.trans (norm_fderiv_le_of_lipschitz ℝ hf₀)
  have ha' : ∀ x, ‖(ContinuousLinearMap.compL ℝ D E F).flip (b x)‖ ≤ K₀ := by
    intro x
    have hn := (compL_flip_lipschitz_one (E := D) (F := E) (G := F)).norm_sub_le (b x) 0
    simp only [map_zero, sub_zero, NNReal.coe_one, one_mul] at hn
    exact hn.trans (norm_fderiv_le_of_lipschitz ℝ hg₀)
  have h1 := lipschitz_clm_comp_bounded ha
    (fun x => norm_fderiv_le_of_lipschitz ℝ hg₁ (x₀ := x))
    (show LipschitzWith (L₁*K₀) (fun x => ContinuousLinearMap.compL ℝ D E F (c x)) from
      by simpa only [one_mul, Function.comp_def] using compL_lipschitz_one.comp hcL) hg₂
  have h2 := lipschitz_clm_comp_bounded ha'
    (fun x => norm_fderiv_le_of_lipschitz ℝ hcL (x₀ := x))
    (show LipschitzWith K₁ (fun x => (ContinuousLinearMap.compL ℝ D E F).flip (b x)) from
      by simpa only [one_mul, Function.comp_def] using compL_flip_lipschitz_one.comp hg₁) hdcL
  convert h1.add h2 using 1 <;> first | ring | rfl

end SharpWasserstein
