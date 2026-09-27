import SharpWasserstein.FiniteGradientTrialDiffusion
import SharpWasserstein.BoundedWeakTests
import SharpWasserstein.WeightedPeriodicCoefficientEvolution

/-! Exact finite-sum calculus for the actual Euclidean generator, used to
identify the differentiated coefficient energy with its literal diffusion
and drift integrals. -/
noncomputable section
open scoped ContDiff InnerProductSpace BigOperators
namespace SharpWasserstein.FiniteGeneratorCalculus
open WeightedTangent FiniteGradientTrial BochnerIdentity PDEPairings
variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- The genuine Euclidean diffusion generator with physical drift. -/
def generator (b : Point n → Point n) (f : Point n → ℝ) (x : Point n) : ℝ :=
  PDEPairings.laplacian f x+⟪b x,gradient f x⟫_ℝ

theorem generator_potential (b : Point n → Point n) (a : ι → Point n → ℝ)
    (ha : ∀ i,ContDiff ℝ ∞ (a i)) (c : EuclideanSpace ℝ ι) :
    generator b (potential a c) = potential (fun i => generator b (a i)) c := by
  funext x
  have hfun : potential a c = fun y => ∑ i,c i*a i y := by
    funext y
    simp [potential]
  have hl : PDEPairings.laplacian (potential a c) x = ∑ i,c i*PDEPairings.laplacian (a i) x := by
    rw [hfun,laplacian_sum Finset.univ (fun i y => c i*a i y)
      (fun i _ => contDiff_two_of_smooth (contDiff_const.mul (ha i)))]
    apply Finset.sum_congr rfl
    intro i _
    exact laplacian_const_mul (ha i) (c i) x
  change PDEPairings.laplacian (potential a c) x+⟪b x,gradient (potential a c) x⟫_ℝ = _
  rw [hl,potential_gradient a ha]
  simp [potential,generator,inner_sum,real_inner_smul_right,mul_add,Finset.sum_add_distrib]

theorem gradientSquare_potential (a : ι → Point n → ℝ)
    (ha : ∀ i,ContDiff ℝ ∞ (a i)) (c : EuclideanSpace ℝ ι) (x : Point n) :
    ‖gradient (potential a c) x‖^2 =
      ∑ i,∑ j,(c i*c j)*⟪gradient (a i) x,gradient (a j) x⟫_ℝ := by
  rw [← real_inner_self_eq_norm_sq,potential_gradient a ha]
  simp only [sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [real_inner_comm (gradient (a i) x) (gradient (a j) x)]
  ring

/-- Generator linearity acts on the actual squared gradient, including all
cross terms, rather than an assumed quadratic matrix form. -/
theorem generator_gradientSquare_potential (b : Point n → Point n)
    (a : ι → Point n → ℝ) (ha : ∀ i,ContDiff ℝ ∞ (a i))
    (c : EuclideanSpace ℝ ι) (x : Point n) :
    generator b (fun y => ‖gradient (potential a c) y‖^2) x =
      ∑ i,∑ j,(c i*c j)*generator b
        (fun y => ⟪gradient (a i) y,gradient (a j) y⟫_ℝ) x := by
  let A : (ι × ι) → Point n → ℝ := fun ij y => ⟪gradient (a ij.1) y,gradient (a ij.2) y⟫_ℝ
  let C : EuclideanSpace ℝ (ι × ι) := WithLp.toLp 2 (fun ij => c ij.1*c ij.2)
  have hs : (fun y => ‖gradient (potential a c) y‖^2) = potential A C := by
    funext y
    rw [gradientSquare_potential a ha]
    simp [potential,A,C,Fintype.sum_prod_type]
  have hA : ∀ ij,ContDiff ℝ ∞ (A ij) := fun ij =>
    (smooth_gradient (ha ij.1)).inner ℝ (smooth_gradient (ha ij.2))
  rw [hs,generator_potential b A hA C]
  simp [potential,A,C,Fintype.sum_prod_type]

end SharpWasserstein.FiniteGeneratorCalculus
