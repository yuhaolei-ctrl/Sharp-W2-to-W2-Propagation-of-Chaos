import SharpWasserstein.PeriodicSourceConvolutionPrimal

/-! Actual bounded derivatives are preserved by the genuine diffusion
operator with bounded smooth drift. This permits repeated primal equations
on translated periodic kernels, with no test regularity left as a premise. -/
noncomputable section
open scoped ContDiff BigOperators
namespace SharpWasserstein
namespace NoiseAverage
variable {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The actual Leibniz estimate supplies a global bound at every order. -/
theorem AllDerivativesBounded.clm_apply {f : E → F →L[ℝ] G} {g : E → F}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hBf : AllDerivativesBounded f) (hBg : AllDerivativesBounded g) :
    AllDerivativesBounded (fun x => f x (g x)) := by
  choose C hC hCf using hBf
  choose D hD hDg using hBg
  intro n
  refine ⟨∑ i ∈ Finset.range (n+1),(n.choose i:ℝ)*C i*D (n-i),
    Finset.sum_nonneg (fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC i)) (hD _)),fun x => ?_⟩
  apply (norm_iteratedFDeriv_clm_apply hf hg x
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).trans
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (hCf i x) (Nat.cast_nonneg _)) (hDg (n-i) x)
    (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hC i))
end NoiseAverage

namespace PeriodicSourceConvolution
open NoiseAverage PropagatedSourceEquation WeightedTangent
variable {d N : ℕ}

theorem coordinateDerivative_smooth {F : Configuration d N → ℝ}
    (hF : ContDiff ℝ ∞ F) (i : Fin N) (a : Fin d) :
    ContDiff ℝ ∞ (coordinateDerivative F i a) :=
  ((contDiff_infty_iff_fderiv.mp hF).2).clm_apply contDiff_const

theorem coordinateDerivative_bounded {F : Configuration d N → ℝ}
    (hF : ContDiff ℝ ∞ F) (hBF : AllDerivativesBounded F) (i : Fin N) (a : Fin d) :
    AllDerivativesBounded (coordinateDerivative F i a) :=
  hBF.fderiv.linear_comp (contDiff_infty_iff_fderiv.mp hF).2
    (ContinuousLinearMap.apply ℝ ℝ (coordinateVector i a))

theorem generator_smooth {b : Configuration d N → Configuration d N} {F : Configuration d N → ℝ}
    (hb : ContDiff ℝ ∞ b) (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (generator b F) := by
  have hLap : ContDiff ℝ ∞ (laplacian F) :=
    ContDiff.sum (fun i _ => ContDiff.sum (fun a _ =>
      coordinateDerivative_smooth (coordinateDerivative_smooth hF i a) i a))
  have he : generator b F = fun x => laplacian F x+fderiv ℝ F x (b x) :=
    funext (generator_eq_laplacian_add_fderiv b F)
  rw [he]
  exact hLap.add ((contDiff_infty_iff_fderiv.mp hF).2.clm_apply hb)

theorem generator_bounded {b : Configuration d N → Configuration d N} {F : Configuration d N → ℝ}
    (hb : ContDiff ℝ ∞ b) (hBb : AllDerivativesBounded b)
    (hF : ContDiff ℝ ∞ F) (hBF : AllDerivativesBounded F) : AllDerivativesBounded (generator b F) := by
  have hcoord (i : Fin N) (a : Fin d) := coordinateDerivative_smooth (coordinateDerivative_smooth hF i a) i a
  have hLap : ContDiff ℝ ∞ (laplacian F) := ContDiff.sum (fun i _ => ContDiff.sum (fun a _ => hcoord i a))
  have hBLap : AllDerivativesBounded (laplacian F) := by
    exact AllDerivativesBounded.sum Finset.univ (fun i _ => ContDiff.sum (fun a _ => hcoord i a))
      (fun i _ => AllDerivativesBounded.sum Finset.univ (fun a _ => hcoord i a)
        (fun a _ => coordinateDerivative_bounded (coordinateDerivative_smooth hF i a)
          (coordinateDerivative_bounded hF hBF i a) i a))
  have he : generator b F = fun x => laplacian F x+fderiv ℝ F x (b x) :=
    funext (generator_eq_laplacian_add_fderiv b F)
  rw [he]
  exact hBLap.add hLap ((contDiff_infty_iff_fderiv.mp hF).2.clm_apply hb)
    (hBF.fderiv.clm_apply (contDiff_infty_iff_fderiv.mp hF).2 hb hBb)

theorem euclideanGenerator_smooth {b : Configuration d N → Configuration d N} {F : Point (N*d) → ℝ}
    (hb : ContDiff ℝ ∞ b) (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (euclideanGenerator b F) :=
  (generator_smooth hb (hF.comp (configurationEuclidean d N).contDiff)).comp
    (configurationEuclidean d N).symm.contDiff

theorem euclideanGenerator_bounded {b : Configuration d N → Configuration d N} {F : Point (N*d) → ℝ}
    (hb : ContDiff ℝ ∞ b) (hBb : AllDerivativesBounded b)
    (hF : ContDiff ℝ ∞ F) (hBF : AllDerivativesBounded F) :
    AllDerivativesBounded (euclideanGenerator b F) :=
  (generator_bounded hb hBb (hF.comp (configurationEuclidean d N).contDiff)
    (hBF.comp_linear hF (configurationEuclidean d N).toContinuousLinearMap)).comp_linear
    (generator_smooth hb (hF.comp (configurationEuclidean d N).contDiff))
    (configurationEuclidean d N).symm.toContinuousLinearMap

end PeriodicSourceConvolution
end SharpWasserstein
