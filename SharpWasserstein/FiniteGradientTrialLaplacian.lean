module

public import SharpWasserstein.Compat
public import SharpWasserstein.FiniteGradientTrialPairing
public import SharpWasserstein.BochnerIdentity

@[expose] public section

/-! The Laplacian acts diagonally on an actual finite eigenfunction family.
Testing the genuine coefficient-regularized Gram equation against that
Laplacian retains an additional nonpositive diffusion penalty. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace BigOperators
namespace SharpWasserstein.FiniteGradientTrial
open WeightedTangent PDEPairings BochnerIdentity
variable {n : ℕ} {ι : Type*} [Fintype ι]

theorem laplacian_const_mul {f : Point n → ℝ} (hf : ContDiff ℝ ∞ f) (c : ℝ) (x : Point n) :
    laplacian (fun y => c*f y) x = c*laplacian f x := by
  have hd (v : Point n) : directionDeriv v (fun y => c*f y) = fun y => c*directionDeriv v f y :=
    funext (directionDeriv_const_mul (hf.differentiable (by simp)) c v)
  unfold laplacian
  simp_rw [hd,directionDeriv_const_mul ((smooth_directionDeriv hf _).differentiable (by simp))]
  exact (Finset.mul_sum _ _ _).symm

def diagonalCoefficients (Λ : ι → ℝ) (c : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => Λ i*c i)

theorem inner_diagonalCoefficients (Λ : ι → ℝ) (c : EuclideanSpace ℝ ι) :
    ⟪c,diagonalCoefficients Λ c⟫_ℝ = ∑ i,Λ i*(c i)^2 := by
  simp only [PiLp.inner_apply,RCLike.inner_apply,RCLike.conj_to_real,diagonalCoefficients]
  apply Finset.sum_congr rfl
  intro i _
  change Λ i*c i*c i = Λ i*(c i)^2
  ring

theorem potential_laplacian (a : ι → Point n → ℝ) (ha : ∀ i, ContDiff ℝ ∞ (a i))
    (Λ : ι → ℝ) (hΛ : ∀ i x, laplacian (a i) x = -Λ i*a i x)
    (c : EuclideanSpace ℝ ι) :
    laplacian (potential a c) = potential a (-diagonalCoefficients Λ c) := by
  have hp : potential a c = fun x => ∑ i,c i*a i x := by
    funext x
    simp only [potential,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [hp]
  funext x
  rw [laplacian_sum Finset.univ (fun i y => c i*a i y)
    (fun i _ => contDiff_two_of_smooth (contDiff_const.mul (ha i)))]
  simp only [potential,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [laplacian_const_mul (ha i),hΛ i]
  change c i*(-Λ i*a i x) = -(Λ i*c i)*a i x
  ring

variable [MeasurableSpace (Point n)] [BorelSpace (Point n)]
  (μ : Measure (Point n)) [IsFiniteMeasure μ]
  (a : ι → Point n → ℝ) (ha : ∀ i, ContDiff ℝ ∞ (a i))
  (hB : ∀ i, ∃ B : ℝ, ∀ x, ‖gradient (a i) x‖ ≤ B)

/-- Exact Laplacian pairing of the constructed optimizer. The coefficient
penalty has the negative sign required by the dissipative energy identity. -/
theorem solution_laplacian_pairing (δ : ℝ) (hδ : 0 < δ) (U : Lp (Point n) 2 μ)
    (Λ : ι → ℝ) (hΛ : ∀ i x, laplacian (a i) x = -Λ i*a i x) :
    let c := RegularizedTrialEnergy.solution (gradientMap μ a ha hB) δ U
    (∫ x,⟪gradient (laplacian (potential a c)) x,U x⟫_ℝ ∂μ) =
      (∫ x,⟪gradient (potential a c) x,gradient (laplacian (potential a c)) x⟫_ℝ ∂μ) -
        δ*(∑ i,Λ i*(c i)^2) := by
  dsimp only
  let c := RegularizedTrialEnergy.solution (gradientMap μ a ha hB) δ U
  have he := RegularizedTrialEnergy.solution_tested (gradientMap μ a ha hB) δ hδ U
    (-diagonalCoefficients Λ c)
  rw [gradientMap_pairing,gradientMap_source_pairing] at he
  change (∫ x,⟪gradient (potential a c) x,gradient (potential a (-diagonalCoefficients Λ c)) x⟫_ℝ ∂μ) +
    δ*⟪c,-diagonalCoefficients Λ c⟫_ℝ = _ at he
  rw [← potential_laplacian a ha Λ hΛ c,inner_neg_right,inner_diagonalCoefficients] at he
  change (∫ x,⟪gradient (laplacian (potential a c)) x,U x⟫_ℝ ∂μ) = _
  linarith

end SharpWasserstein.FiniteGradientTrial
