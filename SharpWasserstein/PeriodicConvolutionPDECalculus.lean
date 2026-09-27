import SharpWasserstein.PeriodicConvolutionWeakBCF
import SharpWasserstein.PeriodicFluxSmooth

/-! Exact coordinate and reflection calculus for the true convolution PDE.
Flattening preserves the unnormalized coordinate Laplacian, and reflection
contributes one minus sign to drift and two cancelling signs to diffusion. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff BigOperators
namespace SharpWasserstein.PeriodicConvolution
open WeightedTangent PeriodicIntegrationByParts PeriodicPositiveKernel

/-- The coordinate flattening, now retaining its continuous linear inverse. -/
def flattenEquiv (d N : ℕ) : Configuration d N ≃L[ℝ] Coordinates (N*d) :=
  (configurationEuclidean d N).trans (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (N*d) => ℝ))

@[simp] theorem flattenEquiv_apply {d N : ℕ} (y : Configuration d N) :
    flattenEquiv d N y = configurationFlatten d N y := configurationFlatten_eq_euclidean y |>.symm

theorem flattenEquiv_coordinateVector {d N : ℕ} (i : Fin N) (a : Fin d) :
    flattenEquiv d N (coordinateVector i a) = Pi.single (finProdFinEquiv (i,a)) 1 := by
  change WithLp.ofLp (configurationEuclidean d N (coordinateVector i a)) = _
  rw [configurationEuclidean_coordinateVector]
  rfl

theorem coordinateDerivative_flatten {d N : ℕ} (f : Coordinates (N*d) → ℝ)
    (i : Fin N) (a : Fin d) (y : Configuration d N) :
    coordinateDerivative (f ∘ flattenEquiv d N) i a y =
      coordinatePartial f (finProdFinEquiv (i,a)) (flattenEquiv d N y) := by
  unfold coordinateDerivative coordinatePartial
  rw [(flattenEquiv d N).comp_right_fderiv]
  change fderiv ℝ f (flattenEquiv d N y) (flattenEquiv d N (coordinateVector i a)) = _
  rw [flattenEquiv_coordinateVector]

theorem laplacian_flatten {d N : ℕ} (f : Coordinates (N*d) → ℝ) (y : Configuration d N) :
    SharpWasserstein.laplacian (f ∘ flattenEquiv d N) y =
      PeriodicIntegrationByParts.laplacian f (flattenEquiv d N y) := by
  have he (i : Fin N) (a : Fin d) : coordinateDerivative (f ∘ flattenEquiv d N) i a =
      coordinatePartial f (finProdFinEquiv (i,a)) ∘ flattenEquiv d N :=
    funext (coordinateDerivative_flatten f i a)
  unfold SharpWasserstein.laplacian PeriodicIntegrationByParts.laplacian
  simp_rw [he,coordinateDerivative_flatten]
  let g := fun k : Fin (N*d) => coordinatePartial (coordinatePartial f k) k (flattenEquiv d N y)
  change (∑ i,∑ a,g (finProdFinEquiv (i,a))) = ∑ k,g k
  calc
    _ = ∑ p : Fin N × Fin d,g (finProdFinEquiv p) := (Fintype.sum_prod_type _).symm
    _ = _ := Fintype.sum_equiv finProdFinEquiv _ _ (fun _ => rfl)

theorem coordinatePartial_reflect {n : ℕ} {f : Coordinates n → ℝ}
    (hf : Differentiable ℝ f) (x : Coordinates n) (i : Fin n) (y : Coordinates n) :
    coordinatePartial (fun z => f (x-z)) i y = -coordinatePartial f i (x-y) := by
  have hd := (hf (x-y)).hasFDerivAt.comp y ((hasFDerivAt_id y).const_sub x)
  unfold coordinatePartial
  simp only [Function.comp_def] at hd
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply,neg_apply,ContinuousLinearMap.id_apply,map_neg]

theorem laplacian_reflect {n : ℕ} {f : Coordinates n → ℝ}
    (hf : ContDiff ℝ ∞ f) (x y : Coordinates n) :
    PeriodicIntegrationByParts.laplacian (fun z => f (x-z)) y =
      PeriodicIntegrationByParts.laplacian f (x-y) := by
  unfold PeriodicIntegrationByParts.laplacian
  apply Finset.sum_congr rfl
  intro i _
  have he : coordinatePartial (fun z => f (x-z)) i = fun z => -coordinatePartial f i (x-z) :=
    funext (coordinatePartial_reflect (hf.differentiable (by simp)) x i)
  rw [he]
  change fderiv ℝ (fun z => -coordinatePartial f i (x-z)) y (Pi.single i 1) = _
  rw [fderiv_fun_neg,neg_apply]
  change -coordinatePartial (fun z => coordinatePartial f i (x-z)) i y = _
  rw [coordinatePartial_reflect
    ((PeriodicFourierTests.smooth_coordinatePartial hf i).differentiable (by simp)),neg_neg]

/-- The reflected kernel generator has exactly the Laplacian and negative
first-derivative drift terms required by the forward density equation. -/
theorem generator_kernelTest {d N : ℕ} (κ : ℝ) (x : Coordinates (N*d))
    (v : Configuration d N → Configuration d N) (y : Configuration d N) :
    generator v (kernelTest κ x) y =
      PeriodicIntegrationByParts.laplacian (kernel κ) (x-configurationFlatten d N y)-
        fderiv ℝ (kernel κ) (x-configurationFlatten d N y) (configurationFlatten d N (v y)) := by
  have he : kernelTest (d := d) (N := N) κ x = (fun z => kernel κ (x-z)) ∘ flattenEquiv d N := by
    funext z
    simp only [kernelTest,Function.comp_apply,flattenEquiv_apply]
  rw [generator_eq_laplacian_add_fderiv,he,laplacian_flatten,laplacian_reflect (kernel_smooth (N*d) κ),
    (flattenEquiv d N).comp_right_fderiv]
  have hd := ((kernel_smooth (N*d) κ).differentiable (by simp) (x-flattenEquiv d N y)).hasFDerivAt.comp
    (flattenEquiv d N y) ((hasFDerivAt_id (flattenEquiv d N y)).const_sub x)
  simp only [Function.comp_def] at hd
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply,neg_apply,ContinuousLinearMap.id_apply,map_neg,
    ContinuousLinearEquiv.coe_coe,flattenEquiv_apply,sub_eq_add_neg]

@[simp] theorem flattenEquiv_symm_apply {d N : ℕ} (x : Coordinates (N*d)) :
    (flattenEquiv d N).symm x = (configurationFlatten d N).symm x := by
  apply (configurationFlatten d N).injective
  rw [← flattenEquiv_apply,ContinuousLinearEquiv.apply_symm_apply,
    (configurationFlatten d N).apply_symm_apply]

/-- The true drift expressed in the same unnormalized flattened coordinates. -/
def flattenedDrift {d N : ℕ} (v : Configuration d N → Configuration d N)
    (x : Coordinates (N*d)) : Coordinates (N*d) :=
  flattenEquiv d N (v ((flattenEquiv d N).symm x))

theorem flattenedDrift_continuous {d N : ℕ} {v : Configuration d N → Configuration d N}
    (hv : Continuous v) : Continuous (flattenedDrift v) :=
  (flattenEquiv d N).continuous.comp (hv.comp (flattenEquiv d N).symm.continuous)

theorem flattenedDrift_at_flatten {d N : ℕ} (v : Configuration d N → Configuration d N)
    (y : Configuration d N) : flattenedDrift v (configurationFlatten d N y) =
      configurationFlatten d N (v y) := by
  unfold flattenedDrift
  rw [flattenEquiv_symm_apply,(configurationFlatten d N).symm_apply_apply,flattenEquiv_apply]

theorem flattenedDrift_contDiff {d N : ℕ} {v : Configuration d N → Configuration d N}
    {r : WithTop ℕ∞} (hv : ContDiff ℝ r v) : ContDiff ℝ r (flattenedDrift v) :=
  (flattenEquiv d N).contDiff.comp (hv.comp (flattenEquiv d N).symm.contDiff)

theorem divergence_sub {n : ℕ} {a b : Coordinates n → Coordinates n}
    (ha : ContDiff ℝ 1 a) (hb : ContDiff ℝ 1 b) (x : Coordinates n) :
    PeriodicDriftEnergy.divergence (fun y => a y-b y) x =
      PeriodicDriftEnergy.divergence a x-PeriodicDriftEnergy.divergence b x := by
  unfold PeriodicDriftEnergy.divergence
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change fderiv ℝ (fun y => a y i-b y i) x (Pi.single i 1) = _
  rw [fderiv_fun_sub (((contDiff_pi.mp ha) i).differentiable (by norm_num) x)
    (((contDiff_pi.mp hb) i).differentiable (by norm_num) x),sub_apply]
  rfl

theorem divergence_commutator {n : ℕ} (κ : ℝ) (μ : Measure (Coordinates n)) [IsProbabilityMeasure μ]
    {b : Coordinates n → Coordinates n} (hb : ContDiff ℝ 1 b) (hbi : Integrable b μ) (x : Coordinates n) :
    PeriodicDriftEnergy.divergence (commutator κ μ b) x =
      PeriodicDriftEnergy.divergence (flux κ μ b) x-
        PeriodicDriftEnergy.divergence (fun y => density κ μ y • b y) x :=
  divergence_sub
    ((flux_smooth_of_integrable κ μ hbi).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1))
    (((density_smooth κ μ).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)).smul hb) x

end SharpWasserstein.PeriodicConvolution
