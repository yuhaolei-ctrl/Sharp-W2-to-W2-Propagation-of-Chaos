import SharpWasserstein.WeightedTangent
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Genuine integration-by-parts identities for the Euclidean Fokker–Planck
operator, tested against actual compact smooth functions. -/

noncomputable section
namespace SharpWasserstein.PDEPairings

open MeasureTheory Set Filter WeightedTangent
open scoped InnerProductSpace Topology BigOperators ContDiff

variable {d : ℕ}

/-- Directional differentiation is the actual Fréchet derivative applied to a fixed vector. -/
def directionDeriv (v : Point d) (f : Point d → ℝ) : Point d → ℝ :=
  fun x => fderiv ℝ f x v

/-- Smooth compact tests remain compactly supported after directional differentiation. -/
theorem compact_directionDeriv (φ : Test d) (v : Point d) :
    HasCompactSupport (directionDeriv v φ) := φ.property.2.fderiv_apply ℝ v

/-- The actual directional derivative of a compact smooth test is continuous. -/
theorem continuous_directionDeriv (φ : Test d) (v : Point d) :
    Continuous (directionDeriv v φ) :=
  (φ.property.1.continuous_fderiv (by simp)).clm_apply continuous_const

/-- Differentiating a smooth function in a fixed direction loses one derivative. -/
theorem contDiff_directionDeriv {f : Point d → ℝ} {m n : ℕ∞ω}
    (hf : ContDiff ℝ n f) (hmn : m + 1 ≤ n) (v : Point d) :
    ContDiff ℝ m (directionDeriv v f) :=
  (hf.fderiv_right hmn).clm_apply contDiff_const

/-- Directional derivatives are again members of the actual compact smooth test space. -/
def directionTest (φ : Test d) (v : Point d) : Test d :=
  ⟨directionDeriv v φ, contDiff_directionDeriv φ.property.1 (by simp) v,
    compact_directionDeriv φ v⟩

/-- The Euclidean Laplacian is the sum of the actual coordinate second derivatives. -/
def laplacian (f : Point d → ℝ) : Point d → ℝ := fun x =>
  ∑ i : Fin d, directionDeriv (EuclideanSpace.single i 1)
    (directionDeriv (EuclideanSpace.single i 1) f) x

/-- The Euclidean divergence is the sum of the actual component derivatives. -/
def divergence (F : Point d → Point d) : Point d → ℝ := fun x =>
  ∑ i : Fin d, directionDeriv (EuclideanSpace.single i 1) (fun y => F y i) x

/-- Coordinate directional derivatives coincide with coordinates of the genuine Hilbert gradient. -/
theorem directionDeriv_eq_gradient_component (f : Point d → ℝ) (i : Fin d) (x : Point d) :
    directionDeriv (EuclideanSpace.single i 1) f x = gradient f x i := by
  rw [directionDeriv, ← inner_gradient_left]
  simp only [EuclideanSpace.inner_single_right, RCLike.conj_to_real, one_mul]

/-- The Laplacian of a twice continuously differentiable function is continuous. -/
theorem continuous_laplacian {f : Point d → ℝ} (hf : ContDiff ℝ 2 f) : Continuous (laplacian f) := by
  apply continuous_finsetSum
  intro i _
  exact (contDiff_directionDeriv (m := 0)
    (contDiff_directionDeriv (m := 1) hf (by norm_num) _) (by norm_num) _).continuous

/-- A continuously differentiable vector field has continuous divergence. -/
theorem continuous_divergence {F : Point d → Point d} (hF : ContDiff ℝ 1 F) :
    Continuous (divergence F) := by
  apply continuous_finsetSum
  intro i _
  have hc : ContDiff ℝ 1 (fun x => F x i) :=
    (EuclideanSpace.proj i : Point d →L[ℝ] ℝ).contDiff.comp hF
  exact (contDiff_directionDeriv (m := 0) hc (by norm_num) _).continuous

/-- The Laplacian of an actual compact smooth test has compact support. -/
theorem compact_laplacian (φ : Test d) : HasCompactSupport (laplacian (φ : Point d → ℝ)) := by
  convert!
    (HasCompactSupport.finset_sum (s := Finset.univ)
      (f := fun i : Fin d => directionDeriv (EuclideanSpace.single i 1)
        (directionDeriv (EuclideanSpace.single i 1) (φ : Point d → ℝ)))
      (fun i _ => compact_directionDeriv (directionTest φ (EuclideanSpace.single i 1)) _)) using 1
  ext x
  simp only [laplacian, Finset.sum_apply]

variable [MeasurableSpace (Point d)] [BorelSpace (Point d)]
variable (μ : Measure (Point d)) [Measure.IsAddHaarMeasure μ]

/-- Actual integration by parts against a compact smooth test. No boundary terms are assumed away. -/
theorem integral_mul_directionDeriv (f : Point d → ℝ) (hf : ContDiff ℝ 1 f)
    (φ : Test d) (v : Point d) :
    (∫ x, f x * directionDeriv v (φ : Point d → ℝ) x ∂μ) =
      -(∫ x, directionDeriv v f x * (φ : Point d → ℝ) x ∂μ) := by
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact ((hf.continuous_fderiv (by simp)).clm_apply continuous_const |>.mul φ.property.1.continuous).integrable_of_hasCompactSupport
      (φ.property.2.mul_left)
  · exact (hf.continuous.mul (continuous_directionDeriv φ v)).integrable_of_hasCompactSupport
      ((compact_directionDeriv φ v).mul_left)
  · exact (hf.continuous.mul φ.property.1.continuous).integrable_of_hasCompactSupport
      (φ.property.2.mul_left)
  · intro x _
    exact hf.differentiable (by simp) x
  · intro x _
    exact test_differentiable φ x

/-- Moving both directional derivatives is justified by two genuine integrations by parts. -/
theorem integral_directionDeriv_twice (f : Point d → ℝ) (hf : ContDiff ℝ 2 f)
    (φ : Test d) (v : Point d) :
    (∫ x, directionDeriv v (directionDeriv v f) x * (φ : Point d → ℝ) x ∂μ) =
      ∫ x, f x * directionDeriv v (directionDeriv v φ) x ∂μ := by
  have h1 := integral_mul_directionDeriv μ (directionDeriv v f)
    (contDiff_directionDeriv hf (by norm_num) v) φ v
  have h2 := integral_mul_directionDeriv μ f (hf.of_le (by norm_num)) (directionTest φ v) v
  change (∫ x, f x * directionDeriv v (directionDeriv v φ) x ∂μ) =
    -(∫ x, directionDeriv v f x * directionDeriv v φ x ∂μ) at h2
  linarith

/-- The diffusion generator is self-adjoint on compact smooth tests by genuine integration by parts. -/
theorem integral_laplacian_mul (f : Point d → ℝ) (hf : ContDiff ℝ 2 f) (φ : Test d) :
    (∫ x, laplacian f x * (φ : Point d → ℝ) x ∂μ) =
      ∫ x, f x * laplacian φ x ∂μ := by
  simp only [laplacian, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    exact integral_directionDeriv_twice μ f hf φ _
  · intro i _
    exact (hf.continuous.mul
      (continuous_directionDeriv (directionTest φ (EuclideanSpace.single i 1)) _)).integrable_of_hasCompactSupport
      (compact_directionDeriv (directionTest φ (EuclideanSpace.single i 1)) _).mul_left
  · intro i _
    have hc : Continuous (directionDeriv (EuclideanSpace.single i 1)
        (directionDeriv (EuclideanSpace.single i 1) f)) :=
      (contDiff_directionDeriv (m := 0)
        (contDiff_directionDeriv (m := 1) hf (by norm_num) _) (by norm_num) _).continuous
    exact (hc.mul φ.property.1.continuous).integrable_of_hasCompactSupport φ.property.2.mul_left

/-- The actual divergence pairs with a compact test as minus the flux-gradient integral. -/
theorem integral_divergence_mul (F : Point d → Point d) (hF : ContDiff ℝ 1 F) (φ : Test d) :
    (∫ x, divergence F x * (φ : Point d → ℝ) x ∂μ) =
      -(∫ x, ⟪F x, gradient (φ : Point d → ℝ) x⟫_ℝ ∂μ) := by
  have hc (i : Fin d) : ContDiff ℝ 1 (fun x => F x i) :=
    (EuclideanSpace.proj i : Point d →L[ℝ] ℝ).contDiff.comp hF
  have hint (i : Fin d) : Integrable (fun x => F x i *
      directionDeriv (EuclideanSpace.single i 1) φ x) μ :=
    ((hc i).continuous.mul (continuous_directionDeriv φ _)).integrable_of_hasCompactSupport
      (compact_directionDeriv φ _).mul_left
  simp only [divergence, Finset.sum_mul]
  rw [integral_finsetSum]
  · have hp (i : Fin d) :
        (∫ x, directionDeriv (EuclideanSpace.single i 1) (fun y => F y i) x *
          (φ : Point d → ℝ) x ∂μ) =
        -(∫ x, F x i * directionDeriv (EuclideanSpace.single i 1) φ x ∂μ) := by
      have h := integral_mul_directionDeriv μ (fun y => F y i) (hc i) φ (EuclideanSpace.single i 1)
      linarith
    simp_rw [hp]
    rw [Finset.sum_neg_distrib, ← integral_finsetSum Finset.univ (fun i _ => hint i)]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [PiLp.inner_apply, RCLike.inner_apply, directionDeriv_eq_gradient_component,
      RCLike.conj_to_real, mul_comm]
  · intro i _
    exact (((hc i).continuous_fderiv (by simp)).clm_apply continuous_const |>.mul
      φ.property.1.continuous).integrable_of_hasCompactSupport φ.property.2.mul_left

/-- The genuine strong diffusion-minus-divergence expression gives the weak generator pairing. -/
theorem integral_fokkerPlanck_mul (ρ : Point d → ℝ) (hρ : ContDiff ℝ 2 ρ)
    (F : Point d → Point d) (hF : ContDiff ℝ 1 F) (φ : Test d) :
    (∫ x, (laplacian ρ x - divergence F x) * (φ : Point d → ℝ) x ∂μ) =
      ∫ x, ρ x * laplacian φ x + ⟪F x, gradient (φ : Point d → ℝ) x⟫_ℝ ∂μ := by
  have h1 : Integrable (fun x => laplacian ρ x * (φ : Point d → ℝ) x) μ :=
    ((continuous_laplacian hρ).mul φ.property.1.continuous).integrable_of_hasCompactSupport
      φ.property.2.mul_left
  have h2 : Integrable (fun x => divergence F x * (φ : Point d → ℝ) x) μ :=
    ((continuous_divergence hF).mul φ.property.1.continuous).integrable_of_hasCompactSupport
      φ.property.2.mul_left
  have hφ2 : ContDiff ℝ 2 (φ : Point d → ℝ) := φ.property.1.of_le (show (2 : ℕ∞ω) ≤ ∞ from ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have h3 : Integrable (fun x => ρ x * laplacian φ x) μ :=
    (hρ.continuous.mul (continuous_laplacian hφ2)).integrable_of_hasCompactSupport
      (compact_laplacian φ).mul_left
  have h4 : Integrable (fun x => ⟪F x, gradient (φ : Point d → ℝ) x⟫_ℝ) μ :=
    (hF.continuous.inner (continuous_test_gradient φ)).integrable_of_hasCompactSupport
      ((compactSupport_test_gradient φ).mono (by
        intro x hx
        change gradient (φ : Point d → ℝ) x ≠ 0
        intro hz
        exact hx (by simp only [hz, inner_zero_right])))
  simp only [sub_mul]
  rw [integral_sub h1 h2, integral_laplacian_mul μ ρ hρ φ,
    integral_divergence_mul μ F hF φ, sub_neg_eq_add, integral_add h3 h4]

/-- A genuine strong Fokker–Planck time derivative has the actual weak generator pairing. -/
theorem strong_fokkerPlanck_pairing (ρ ρ' : Point d → ℝ) (hρ : ContDiff ℝ 2 ρ)
    (F : Point d → Point d) (hF : ContDiff ℝ 1 F)
    (hPDE : ∀ᵐ x ∂μ, ρ' x = laplacian ρ x - divergence F x) (φ : Test d) :
    (∫ x, ρ' x * (φ : Point d → ℝ) x ∂μ) =
      ∫ x, ρ x * laplacian φ x + ⟪F x, gradient (φ : Point d → ℝ) x⟫_ℝ ∂μ := by
  rw [← integral_fokkerPlanck_mul μ ρ hρ F hF φ]
  apply integral_congr_ae
  filter_upwards [hPDE] with x hx
  rw [hx]

/-- Pointwise density differentiation passes through an actual compact-test integral.
The local bound is imposed only on the compact support of the test. -/
theorem hasDerivAt_density_testPairing
    (ρ ρ' : ℝ → Point d → ℝ) (φ : Test d) {t C : ℝ} {s : Set ℝ}
    (hs : s ∈ 𝓝 t) (hρ : ∀ r ∈ s, Continuous (ρ r))
    (hρ' : Continuous (ρ' t))
    (hderiv : ∀ x, ∀ r ∈ s, HasDerivAt (fun q => ρ q x) (ρ' r x) r)
    (hbound : ∀ x ∈ Function.support (φ : Point d → ℝ), ∀ r ∈ s, |ρ' r x| ≤ C) :
    HasDerivAt (fun r => ∫ x, ρ r x * (φ : Point d → ℝ) x ∂μ)
      (∫ x, ρ' t x * (φ : Point d → ℝ) x ∂μ) t := by
  have ht : t ∈ s := mem_of_mem_nhds hs
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun r x => ρ r x * (φ : Point d → ℝ) x)
    (F' := fun r x => ρ' r x * (φ : Point d → ℝ) x)
    (bound := fun x => C * |(φ : Point d → ℝ) x|) hs ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [hs] with r hr
    exact ((hρ r hr).mul φ.property.1.continuous).aestronglyMeasurable
  · exact ((hρ t ht).mul φ.property.1.continuous).integrable_of_hasCompactSupport
      φ.property.2.mul_left
  · exact (hρ'.mul φ.property.1.continuous).aestronglyMeasurable
  · filter_upwards [] with x r hr
    rw [Real.norm_eq_abs, abs_mul]
    by_cases hx : x ∈ Function.support (φ : Point d → ℝ)
    · exact mul_le_mul_of_nonneg_right (hbound x hx r hr) (abs_nonneg _)
    · have hz : (φ : Point d → ℝ) x = 0 := not_ne_iff.mp hx
      simp only [hz, abs_zero, mul_zero, le_refl]
  · exact (continuous_const.mul φ.property.1.continuous.abs).integrable_of_hasCompactSupport
      φ.property.2.abs.mul_left
  · filter_upwards [] with x r hr
    exact (hderiv x r hr).mul_const _

/-- A classical density satisfying the strong Fokker–Planck equation yields the actual
weak evolution derivative, derived from pointwise differentiation and integration by parts. -/
theorem hasDerivAt_fokkerPlanck_testPairing
    (ρ ρ' : ℝ → Point d → ℝ) (F : Point d → Point d) (φ : Test d)
    {t C : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝 t)
    (hρ : ∀ r ∈ s, Continuous (ρ r)) (hρ' : Continuous (ρ' t))
    (hderiv : ∀ x, ∀ r ∈ s, HasDerivAt (fun q => ρ q x) (ρ' r x) r)
    (hbound : ∀ x ∈ Function.support (φ : Point d → ℝ), ∀ r ∈ s, |ρ' r x| ≤ C)
    (hρ2 : ContDiff ℝ 2 (ρ t)) (hF : ContDiff ℝ 1 F)
    (hPDE : ∀ᵐ x ∂μ, ρ' t x = laplacian (ρ t) x - divergence F x) :
    HasDerivAt (fun r => ∫ x, ρ r x * (φ : Point d → ℝ) x ∂μ)
      (∫ x, ρ t x * laplacian φ x + ⟪F x, gradient (φ : Point d → ℝ) x⟫_ℝ ∂μ) t := by
  rw [← strong_fokkerPlanck_pairing μ (ρ t) (ρ' t) hρ2 F hF hPDE φ]
  exact hasDerivAt_density_testPairing μ ρ ρ' φ hs hρ hρ' hderiv hbound

end SharpWasserstein.PDEPairings
