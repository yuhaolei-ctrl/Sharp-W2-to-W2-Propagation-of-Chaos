module

public import SharpWasserstein.Compat
public import SharpWasserstein.PDEPairings
public import SharpWasserstein.HierarchyAlgebra
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

@[expose] public section

/-! Genuine Euclidean differential identities behind the tangent-energy dissipation.
The Hessian is built from actual derivatives; its symmetry follows from `C²`
regularity, not from an assumed symmetric-matrix condition. -/

noncomputable section
namespace SharpWasserstein.BochnerIdentity
open WeightedTangent PDEPairings
open scoped InnerProductSpace BigOperators ContDiff
variable {d : ℕ}

/-- Repeated directional derivatives coincide with evaluation of the genuine second Fréchet derivative. -/
theorem directionDeriv_twice_eq_fderiv {f : Point d → ℝ} (hf : ContDiff ℝ 2 f)
    (v w x : Point d) :
    directionDeriv v (directionDeriv w f) x = fderiv ℝ (fderiv ℝ f) x v w := by
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by simp)
  unfold directionDeriv
  rw [fderiv_clm_apply (hd x) (differentiableAt_const w)]
  simp

/-- Schwarz symmetry for the actual coordinate differential operators. -/
theorem directionDeriv_commute {f : Point d → ℝ} (hf : ContDiff ℝ 2 f)
    (v w x : Point d) :
    directionDeriv v (directionDeriv w f) x = directionDeriv w (directionDeriv v f) x := by
  rw [directionDeriv_twice_eq_fderiv hf, directionDeriv_twice_eq_fderiv hf]
  exact hf.contDiffAt.isSymmSndFDerivAt (by simp) v w

/-- The Hessian matrix consists of actual coordinate second derivatives. -/
def hessian (f : Point d → ℝ) (x : Point d) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => directionDeriv (EuclideanSpace.single i 1)
    (directionDeriv (EuclideanSpace.single j 1) f) x

/-- The actual Hessian is symmetric for every twice continuously differentiable potential. -/
theorem hessian_isSymm {f : Point d → ℝ} (hf : ContDiff ℝ 2 f) (x : Point d) :
    (hessian f x).IsSymm := by
  ext i j
  exact directionDeriv_commute hf _ _ _

/-- Product rule for the actual directional derivative. -/
theorem directionDeriv_mul {f g : Point d → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (v x : Point d) :
    directionDeriv v (fun y => f y * g y) x =
      f x * directionDeriv v g x + g x * directionDeriv v f x := by
  simp only [directionDeriv, fderiv_fun_mul (hf x) (hg x), add_apply,
    smul_apply, smul_eq_mul]

/-- Constant multiplication commutes with the actual directional derivative. -/
theorem directionDeriv_const_mul {f : Point d → ℝ} (hf : Differentiable ℝ f)
    (c : ℝ) (v x : Point d) :
    directionDeriv v (fun y => c * f y) x = c * directionDeriv v f x := by
  rw [directionDeriv_mul (differentiable_const c) hf]
  simp [directionDeriv]

/-- The actual directional derivative distributes over a finite sum of differentiable functions. -/
theorem directionDeriv_sum {ι : Type*} (s : Finset ι) (f : ι → Point d → ℝ)
    (hf : ∀ i ∈ s, Differentiable ℝ (f i)) (v x : Point d) :
    directionDeriv v (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, directionDeriv v (f i) x := by
  simp only [directionDeriv, fderiv_fun_sum (fun i hi => hf i hi x), sum_apply]

/-- Squaring a scalar field gives the exact second-directional-derivative formula. -/
theorem directionDeriv_sq_twice {f : Point d → ℝ} (hf : ContDiff ℝ 2 f) (v x : Point d) :
    directionDeriv v (directionDeriv v (fun y => f y ^ 2)) x =
      2 * (directionDeriv v f x) ^ 2 + 2 * f x * directionDeriv v (directionDeriv v f) x := by
  have hfd : Differentiable ℝ f := hf.differentiable (by simp)
  have hvd : Differentiable ℝ (directionDeriv v f) :=
    (contDiff_directionDeriv (m := 1) hf (by norm_num) v).differentiable (by simp)
  have hid : directionDeriv v (fun y => f y ^ 2) =
      fun y => 2 * (f y * directionDeriv v f y) := by
    ext y
    simp only [pow_two, directionDeriv_mul hfd hfd]
    ring
  rw [hid, directionDeriv_const_mul (f := fun y => f y * directionDeriv v f y) (hfd.mul hvd), directionDeriv_mul hfd hvd]
  ring

/-- Second directional derivatives distribute over finite sums with genuine C² hypotheses. -/
theorem directionDeriv_twice_sum {ι : Type*} (s : Finset ι) (f : ι → Point d → ℝ)
    (hf : ∀ i ∈ s, ContDiff ℝ 2 (f i)) (v x : Point d) :
    directionDeriv v (directionDeriv v (fun y => ∑ i ∈ s, f i y)) x =
      ∑ i ∈ s, directionDeriv v (directionDeriv v (f i)) x := by
  have heq : directionDeriv v (fun y => ∑ i ∈ s, f i y) =
      fun y => ∑ i ∈ s, directionDeriv v (f i) y := by
    funext y
    exact directionDeriv_sum s f (fun i hi => (hf i hi).differentiable (by simp)) v y
  rw [heq]
  exact directionDeriv_sum s _ (fun i hi =>
    (contDiff_directionDeriv (m := 1) (hf i hi) (by norm_num) v).differentiable (by simp)) v x

/-- The actual Euclidean Laplacian distributes over finite sums of C² scalar fields. -/
theorem laplacian_sum {ι : Type*} (s : Finset ι) (f : ι → Point d → ℝ)
    (hf : ∀ i ∈ s, ContDiff ℝ 2 (f i)) (x : Point d) :
    laplacian (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, laplacian (f i) x := by
  unfold laplacian
  simp_rw [directionDeriv_twice_sum s f hf]
  exact Finset.sum_comm

/-- Smoothness remains smoothness after taking one genuine directional derivative. -/
theorem smooth_directionDeriv {f : Point d → ℝ} (hf : ContDiff ℝ ∞ f) (v : Point d) :
    ContDiff ℝ ∞ (directionDeriv v f) := contDiff_directionDeriv hf (by simp) v

/-- A smooth function is C², used when applying the genuine Schwarz theorem. -/
theorem contDiff_two_of_smooth {f : Point d → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ 2 f :=
  hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)

/-- First derivatives commute with the actual Euclidean Laplacian for smooth functions. -/
theorem directionDeriv_laplacian {f : Point d → ℝ} (hf : ContDiff ℝ ∞ f)
    (v x : Point d) : directionDeriv v (laplacian f) x = laplacian (directionDeriv v f) x := by
  unfold laplacian
  rw [directionDeriv_sum Finset.univ _ (fun i _ =>
    (smooth_directionDeriv (smooth_directionDeriv hf _) _).differentiable (by simp))]
  apply Finset.sum_congr rfl
  intro i _
  rw [directionDeriv_commute (contDiff_two_of_smooth (smooth_directionDeriv hf _))]
  have heq : directionDeriv v (directionDeriv (EuclideanSpace.single i 1) f) =
      directionDeriv (EuclideanSpace.single i 1) (directionDeriv v f) := by
    funext y
    exact directionDeriv_commute (contDiff_two_of_smooth hf) _ _ _
  rw [heq]

/-- The actual Laplacian of a squared scalar field obeys the exact product rule. -/
theorem laplacian_sq {f : Point d → ℝ} (hf : ContDiff ℝ 2 f) (x : Point d) :
    laplacian (fun y => f y ^ 2) x =
      2 * (∑ i : Fin d, directionDeriv (EuclideanSpace.single i 1) f x ^ 2) +
        2 * f x * laplacian f x := by
  unfold laplacian
  simp_rw [directionDeriv_sq_twice hf]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- The Euclidean Bochner identity, with actual gradients, Laplacians, and Hessian derivatives. -/
theorem laplacian_gradient_norm_sq {f : Point d → ℝ} (hf : ContDiff ℝ ∞ f) (x : Point d) :
    laplacian (fun y => ‖gradient f y‖ ^ 2) x =
      2 * HierarchyAlgebra.frobeniusSq (hessian f x) +
        2 * ⟪gradient f x, gradient (laplacian f) x⟫_ℝ := by
  have hn : (fun y => ‖gradient f y‖ ^ 2) = fun y =>
      ∑ j : Fin d, directionDeriv (EuclideanSpace.single j 1) f y ^ 2 := by
    funext y
    simp only [EuclideanSpace.real_norm_sq_eq, directionDeriv_eq_gradient_component]
  have hc (j : Fin d) : ContDiff ℝ 2 (directionDeriv (EuclideanSpace.single j 1) f) :=
    contDiff_two_of_smooth (smooth_directionDeriv hf _)
  have hh : (∑ j : Fin d, ∑ i : Fin d,
      directionDeriv (EuclideanSpace.single i 1) (directionDeriv (EuclideanSpace.single j 1) f) x ^ 2) =
      HierarchyAlgebra.frobeniusSq (hessian f x) := by
    unfold HierarchyAlgebra.frobeniusSq hessian
    exact Finset.sum_comm
  have hp : (∑ j : Fin d, directionDeriv (EuclideanSpace.single j 1) f x *
      laplacian (directionDeriv (EuclideanSpace.single j 1) f) x) =
      ⟪gradient f x, gradient (laplacian f) x⟫_ℝ := by
    simp_rw [← directionDeriv_laplacian hf, directionDeriv_eq_gradient_component]
    simp only [PiLp.inner_apply, RCLike.inner_apply, RCLike.conj_to_real, mul_comm]
  rw [hn, laplacian_sum Finset.univ _ (fun j _ => (hc j).pow 2)]
  simp_rw [laplacian_sq (hc _)]
  simp only [Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  rw [hh, hp]

/-- The diffusion contribution is pointwise exactly minus twice the squared actual Hessian norm. -/
theorem diffusion_energy_integrand {f : Point d → ℝ} (hf : ContDiff ℝ ∞ f) (x : Point d) :
    2 * ⟪gradient f x, gradient (laplacian f) x⟫_ℝ -
      laplacian (fun y => ‖gradient f y‖ ^ 2) x =
        -2 * HierarchyAlgebra.frobeniusSq (hessian f x) := by
  rw [laplacian_gradient_norm_sq hf]
  ring

/-- The manuscript's lifted Hessian cancellation now follows for the actual Hessian of a C² potential. -/
theorem external_actual_hessian_cancellation {f : Point d → ℝ} (hf : ContDiff ℝ 2 f)
    (x w v : Point d) (α : ℝ) :
    2 * α * ⟪w, HierarchyAlgebra.matrixAction (hessian f x) v⟫_ℝ -
      α * (2 * ⟪v, HierarchyAlgebra.matrixAction (hessian f x) w⟫_ℝ) = 0 :=
  HierarchyAlgebra.external_hessian_cancellation (hessian f x) (hessian_isSymm hf x) w v α

/-- The actual Laplacian of a smooth function is smooth. -/
theorem smooth_laplacian {f : Point d → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (laplacian f) :=
  ContDiff.sum (fun _ _ => smooth_directionDeriv (smooth_directionDeriv hf _) _)

/-- The actual gradient of a smooth function is a smooth Euclidean vector field. -/
theorem smooth_gradient {f : Point d → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (gradient f) :=
  (InnerProductSpace.toDual ℝ (Point d)).symm.toContinuousLinearEquiv.contDiff.comp
    (hf.fderiv_right (by simp))

/-- The squared norm of the actual gradient is smooth. -/
theorem smooth_gradient_norm_sq {f : Point d → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun y => ‖gradient f y‖ ^ 2) := by
  have hn : (fun y => ‖gradient f y‖ ^ 2) = fun y =>
      ∑ j : Fin d, directionDeriv (EuclideanSpace.single j 1) f y ^ 2 := by
    funext y
    simp only [EuclideanSpace.real_norm_sq_eq, directionDeriv_eq_gradient_component]
  rw [hn]
  exact ContDiff.sum (fun j _ => (smooth_directionDeriv hf _).pow 2)

/-- The actual Laplacian of a compact smooth test is again a compact smooth test. -/
def laplacianTest (φ : Test d) : Test d :=
  ⟨laplacian (φ : Point d → ℝ), smooth_laplacian φ.property.1, compact_laplacian φ⟩

/-- The actual squared gradient norm is a compact smooth scalar test. -/
def gradientNormSqTest (φ : Test d) : Test d :=
  ⟨fun y => ‖gradient (φ : Point d → ℝ) y‖ ^ 2, smooth_gradient_norm_sq φ.property.1,
    (compactSupport_test_gradient φ).comp_left (g := fun v : Point d => ‖v‖ ^ 2) (by simp)⟩

open MeasureTheory
variable [MeasurableSpace (Point d)] [BorelSpace (Point d)]
variable (μ : Measure (Point d)) [Measure.IsAddHaarMeasure μ]

/-- The diffusion energy identity for an actual compact smooth potential and C² density.
Both terms on the left are the genuine strong-PDE pairings, and both integrations
by parts are proved from compact support. -/
theorem integral_diffusion_energy (ρ : Point d → ℝ) (hρ : ContDiff ℝ 2 ρ) (φ : Test d) :
    2 * (∫ x, (-divergence (fun y => ρ y • gradient (φ : Point d → ℝ) y) x) *
      laplacian φ x ∂μ) -
      (∫ x, laplacian ρ x * ‖gradient (φ : Point d → ℝ) x‖ ^ 2 ∂μ) =
    -2 * ∫ x, ρ x * HierarchyAlgebra.frobeniusSq (hessian φ x) ∂μ := by
  let F : Point d → Point d := fun x => ρ x • gradient (φ : Point d → ℝ) x
  have hφ1 : ContDiff ℝ 1 (gradient (φ : Point d → ℝ)) :=
    (smooth_gradient φ.property.1).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)
  have hF : ContDiff ℝ 1 F := (hρ.of_le (by norm_num)).smul hφ1
  have hdiv := integral_divergence_mul μ F hF (laplacianTest φ)
  have hlap := integral_laplacian_mul μ ρ hρ (gradientNormSqTest φ)
  have hfirst : (∫ x, (-divergence F x) * laplacian φ x ∂μ) =
      ∫ x, ρ x * ⟪gradient (φ : Point d → ℝ) x, gradient (laplacian φ) x⟫_ℝ ∂μ := by
    simp only [neg_mul, integral_neg]
    change -(∫ x, divergence F x * (laplacianTest φ : Point d → ℝ) x ∂μ) = _
    rw [hdiv, neg_neg]
    apply integral_congr_ae
    filter_upwards [] with x
    exact real_inner_smul_left _ _ _
  have hsecond : (∫ x, laplacian ρ x * ‖gradient (φ : Point d → ℝ) x‖ ^ 2 ∂μ) =
      ∫ x, ρ x * laplacian (fun y => ‖gradient (φ : Point d → ℝ) y‖ ^ 2) x ∂μ := hlap
  change 2 * (∫ x, (-divergence F x) * laplacian φ x ∂μ) - _ = _
  rw [hfirst, hsecond, ← integral_const_mul]
  have hgradlap := continuous_test_gradient (laplacianTest φ)
  have hint1 : Integrable (fun x => 2 * (ρ x *
      ⟪gradient (φ : Point d → ℝ) x, gradient (laplacian φ) x⟫_ℝ)) μ := by
    apply (continuous_const.mul (hρ.continuous.mul
      ((continuous_test_gradient φ).inner hgradlap))).integrable_of_hasCompactSupport
    apply HasCompactSupport.mul_left
    apply HasCompactSupport.mul_left
    apply (compactSupport_test_gradient φ).mono
    intro x hx hz
    exact hx (by simp only [hz, inner_zero_left])
  have hint2 : Integrable (fun x => ρ x *
      laplacian (fun y => ‖gradient (φ : Point d → ℝ) y‖ ^ 2) x) μ :=
    (hρ.continuous.mul (continuous_laplacian
      (contDiff_two_of_smooth (smooth_gradient_norm_sq φ.property.1)))).integrable_of_hasCompactSupport
      (compact_laplacian (gradientNormSqTest φ)).mul_left
  rw [← integral_sub hint1 hint2, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  calc
    _ = ρ x * (2 * ⟪gradient (φ : Point d → ℝ) x, gradient (laplacian φ) x⟫_ℝ -
        laplacian (fun y => ‖gradient (φ : Point d → ℝ) y‖ ^ 2) x) := by ring
    _ = ρ x * (-2 * HierarchyAlgebra.frobeniusSq (hessian φ x)) :=
      congrArg (fun r => ρ x * r) (diffusion_energy_integrand φ.property.1 x)
    _ = _ := by ring

end SharpWasserstein.BochnerIdentity
