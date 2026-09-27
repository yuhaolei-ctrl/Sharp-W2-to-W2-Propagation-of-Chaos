import SharpWasserstein.FiniteGradientTrialLaplacian
import SharpWasserstein.BoundedHessianIntegrability

/-! Exact diffusion dissipation for the coefficient-regularized optimizer
under an arbitrary finite measure. No density, density derivative, or
unproved integration by parts for that measure is used. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace BigOperators
namespace SharpWasserstein.FiniteGradientTrial
open WeightedTangent PDEPairings BochnerIdentity NoiseAverage
variable {n : ℕ} {ι : Type*} [Fintype ι]

theorem potential_allDerivativesBounded (a : ι → Point n → ℝ)
    (ha : ∀ i, ContDiff ℝ ∞ (a i)) (hBa : ∀ i, AllDerivativesBounded (a i))
    (c : EuclideanSpace ℝ ι) : AllDerivativesBounded (potential a c) := by
  convert (AllDerivativesBounded.sum Finset.univ
    (fun i _ => (ha i).const_smul (c i))
    (fun i _ => (hBa i).const_smul (ha i) (c i))) using 1
  funext x
  simp only [potential,Finset.sum_apply,Pi.smul_apply]

variable [MeasurableSpace (Point n)] [BorelSpace (Point n)]
  (μ : Measure (Point n)) [IsFiniteMeasure μ]
  (a : ι → Point n → ℝ) (ha : ∀ i, ContDiff ℝ ∞ (a i))
  (hB : ∀ i, ∃ B : ℝ, ∀ x, ‖gradient (a i) x‖ ≤ B)

include ha hB in
theorem potential_gradient_memLp (c : EuclideanSpace ℝ ι) :
    MemLp (gradient (potential a c)) 2 μ :=
  (memLp_congr_ae (gradientMap_ae μ a ha hB c)).mp (Lp.memLp _)

/-- The exact negative Hessian term survives coefficient regularization;
the additional diagonal coefficient penalty has the same dissipative sign. -/
theorem solution_diffusion_identity (δ : ℝ) (hδ : 0 < δ) (U : Lp (Point n) 2 μ)
    (hBa : ∀ i, AllDerivativesBounded (a i))
    (Λ : ι → ℝ) (hΛ : ∀ i x, laplacian (a i) x = -Λ i*a i x) :
    let c := RegularizedTrialEnergy.solution (gradientMap μ a ha hB) δ U
    2*(∫ x,⟪gradient (laplacian (potential a c)) x,U x⟫_ℝ ∂μ) -
      (∫ x,laplacian (fun y => ‖gradient (potential a c) y‖^2) x ∂μ) =
    -2*(∫ x,HierarchyAlgebra.frobeniusSq (hessian (potential a c) x) ∂μ) -
      2*δ*(∑ i,Λ i*(c i)^2) := by
  dsimp only
  let c := RegularizedTrialEnergy.solution (gradientMap μ a ha hB) δ U
  have hf := potential_smooth a ha c
  have hb := potential_allDerivativesBounded a ha hBa c
  have hH := hessian_square_integrable μ hf hb
  have hg := potential_gradient_memLp μ a ha hB c
  have hΔ : MemLp (gradient (laplacian (potential a c))) 2 μ := by
    rw [potential_laplacian a ha Λ hΛ c]
    exact potential_gradient_memLp μ a ha hB _
  have hi : Integrable (fun x => ⟪gradient (potential a c) x,
      gradient (laplacian (potential a c)) x⟫_ℝ) μ := by
    apply (L2.integrable_inner (𝕜 := ℝ) (hg.toLp _) (hΔ.toLp _)).congr
    filter_upwards [hg.coeFn_toLp,hΔ.coeFn_toLp] with x hx hy
    rw [hx,hy]
  have he : (∫ x,laplacian (fun y => ‖gradient (potential a c) y‖^2) x ∂μ) =
      2*(∫ x,HierarchyAlgebra.frobeniusSq (hessian (potential a c) x) ∂μ) +
      2*(∫ x,⟪gradient (potential a c) x,gradient (laplacian (potential a c)) x⟫_ℝ ∂μ) := by
    simp_rw [laplacian_gradient_norm_sq hf]
    rw [integral_add (hH.const_mul 2) (hi.const_mul 2),integral_const_mul,integral_const_mul]
  have hp := solution_laplacian_pairing μ a ha hB δ hδ U Λ hΛ
  change (∫ x,⟪gradient (laplacian (potential a c)) x,U x⟫_ℝ ∂μ) = _ at hp
  change 2*(∫ x,⟪gradient (laplacian (potential a c)) x,U x⟫_ℝ ∂μ) -
    (∫ x,laplacian (fun y => ‖gradient (potential a c) y‖^2) x ∂μ) = _
  rw [hp,he]
  ring

end SharpWasserstein.FiniteGradientTrial
