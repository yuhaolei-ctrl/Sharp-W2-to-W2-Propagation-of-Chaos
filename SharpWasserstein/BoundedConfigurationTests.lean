import SharpWasserstein.ConstantDriftLaw
import SharpWasserstein.BoundedDerivativeComposition

/-! Bounded smooth configuration tests are admitted by the actual weak and
Gaussian generator equations. The required Euclidean gradient and Laplacian
bounds are proved from bounded genuine iterated Fréchet derivatives. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal Interval ContDiff BigOperators
namespace SharpWasserstein
open WeightedTangent NoiseAverage

/-- Euclidean coordinate conversion preserves bounded derivatives of every
order; its differential is the actual fixed continuous linear equivalence. -/
theorem allDerivativesBounded_euclideanTest {d N : ℕ} {φ : Configuration d N → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hB : AllDerivativesBounded φ) :
    AllDerivativesBounded (euclideanTest φ) := by
  apply AllDerivativesBounded.comp_of_fderiv hφ (configurationEuclidean d N).symm.contDiff hB
  have he : fderiv ℝ ((configurationEuclidean d N).symm : Point (N*d) → Configuration d N) =
      fun _ => (configurationEuclidean d N).symm.toContinuousLinearMap := by
    funext x
    exact (configurationEuclidean d N).symm.toContinuousLinearMap.fderiv
  rw [he]
  exact allDerivativesBounded_const _

/-- Global bounds for a function, its actual gradient, and its actual
Laplacian follow from bounded derivatives of orders zero, one and two. -/
theorem euclidean_bounds_of_allDerivativesBounded {n : ℕ} {f : Point n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hB : AllDerivativesBounded f) :
    ∃ A B D : ℝ, (∀ x,|f x| ≤ A) ∧ (∀ x,‖gradient f x‖ ≤ B) ∧
      (∀ x,|PDEPairings.laplacian f x| ≤ D) := by
  obtain ⟨A,_,hA⟩ := hB.bounded
  obtain ⟨B,_,hB₁⟩ := hB.fderiv.bounded
  obtain ⟨C,_,hB₂⟩ := hB.fderiv.fderiv.bounded
  refine ⟨A,B,(n : ℝ)*C,?_,?_,?_⟩
  · simpa only [Real.norm_eq_abs] using hA
  · intro x
    rw [SmoothCutoff.norm_gradient_eq_fderiv]
    exact hB₁ x
  · intro x
    have hcoord (i : Fin n) :
        ‖PDEPairings.directionDeriv (EuclideanSpace.single i 1)
          (PDEPairings.directionDeriv (EuclideanSpace.single i 1) f) x‖ ≤ C := by
      rw [BochnerIdentity.directionDeriv_twice_eq_fderiv (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))]
      have he : ‖(EuclideanSpace.single i 1 : Point n)‖ = 1 := by simp
      calc
        ‖fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)‖ ≤
            ‖fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1)‖ * ‖(EuclideanSpace.single i 1 : Point n)‖ :=
          (fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1)).le_opNorm _
        _ ≤ (‖fderiv ℝ (fderiv ℝ f) x‖ * ‖(EuclideanSpace.single i 1 : Point n)‖) *
            ‖(EuclideanSpace.single i 1 : Point n)‖ :=
          mul_le_mul_of_nonneg_right ((fderiv ℝ (fderiv ℝ f) x).le_opNorm _) (norm_nonneg _)
        _ ≤ C := by simpa only [he,mul_one] using hB₂ x
    calc
      |PDEPairings.laplacian f x| = ‖PDEPairings.laplacian f x‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∑ i : Fin n,‖PDEPairings.directionDeriv (EuclideanSpace.single i 1)
          (PDEPairings.directionDeriv (EuclideanSpace.single i 1) f) x‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin n,C := Finset.sum_le_sum (fun i _ => hcoord i)
      _ = (n : ℝ)*C := by simp

namespace WeakEvolution
variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  {v : ℝ → Configuration d N → Configuration d N} {P : ℝ → Measure (Configuration d N)}

/-- Configuration-space bounded smooth tests satisfy the actual integrated
weak equation. No additional weak-test identity is assumed. -/
theorem equation_bounded_configuration (h : WeakEvolution v P)
    (hv : ∀ s,0 ≤ s → Measurable (v s)) {M : ℝ}
    (hM : ∀ s,0 ≤ s → ∀ x,‖configurationEuclidean d N (v s x)‖ ≤ M)
    {φ : Configuration d N → ℝ} (hφ : ContDiff ℝ ∞ φ) (hB : AllDerivativesBounded φ)
    (t : ℝ) (ht : 0 ≤ t) :
    IntervalIntegrable (fun s => ∫ x,generator (v s) φ x ∂P s) volume 0 t ∧
      (∫ x,φ x ∂P t)-(∫ x,φ x ∂P 0) =
        ∫ s in (0 : ℝ)..t,∫ x,generator (v s) φ x ∂P s := by
  have hf := hφ.comp (configurationEuclidean d N).symm.contDiff
  obtain ⟨A,B,D,hA,hB₁,hD⟩ := euclidean_bounds_of_allDerivativesBounded hf
    (allDerivativesBounded_euclideanTest hφ hB)
  have he : euclideanTest φ ∘ configurationEuclidean d N = φ := by
    funext x
    exact euclideanTest_apply φ x
  have hh := equation_bounded_smooth h hv hM (euclideanTest φ) hf hA hB₁ hD t ht
  simpa only [he,euclideanTest_apply] using hh

end WeakEvolution
namespace FrozenGaussian
variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]

/-- The frozen Gaussian generator identity applies directly to genuine
configuration tests with bounded derivatives of every order. -/
theorem timeExpectation_sub_eq_integral_bounded_configuration
    {φ : Configuration d N → ℝ} (hφ : ContDiff ℝ ∞ φ) (hB : AllDerivativesBounded φ)
    (x u : Configuration d N) {t : ℝ} (ht : 0 ≤ t) :
    timeExpectation φ x u t-φ x =
      ∫ s in (0 : ℝ)..t,timeExpectation (generator (fun _ => u) φ) x u s := by
  have hf := hφ.comp (configurationEuclidean d N).symm.contDiff
  obtain ⟨A,B,D,hA,hB₁,hD⟩ := euclidean_bounds_of_allDerivativesBounded hf
    (allDerivativesBounded_euclideanTest hφ hB)
  have he : euclideanTest φ ∘ configurationEuclidean d N = φ := by
    funext z
    exact euclideanTest_apply φ z
  simpa only [he,euclideanTest_apply] using
    timeExpectation_sub_eq_integral_bounded_smooth (euclideanTest φ) hf hA hB₁ hD x u ht

end FrozenGaussian
end SharpWasserstein
