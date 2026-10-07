module

public import SharpWasserstein.Compat
public import SharpWasserstein.PeriodicConvolutionDensity
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

@[expose] public section

/-! Product periodic convolution preserves genuine prefixCoords marginals. The
fiber density identity is obtained by actual finite-product decomposition,
Fubini, and translation invariance of the normalized periodic kernel. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal ContDiff BigOperators BoundedContinuousFunction
namespace SharpWasserstein.PeriodicConvolution
open PeriodicIntegrationByParts PeriodicPositiveKernel

/-- Split the first `k` coordinates from the remaining `l` coordinates. -/
def splitCoordinates (k l : ℕ) : Coordinates (k+l) ≃ᵐ Coordinates k × Coordinates l :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin k ⊕ Fin l => ℝ) finSumFinEquiv.symm).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin k ⊕ Fin l => ℝ))

def prefixCoords (k l : ℕ) (x : Coordinates (k+l)) : Coordinates k := fun i => x (Fin.castAdd l i)
def suffix (k l : ℕ) (x : Coordinates (k+l)) : Coordinates l := fun i => x (Fin.natAdd k i)

@[simp] theorem splitCoordinates_fst {k l : ℕ} (x : Coordinates (k+l)) :
    (splitCoordinates k l x).1 = prefixCoords k l x := by
  funext i
  simp [splitCoordinates,prefixCoords,MeasurableEquiv.piCongrLeft,Equiv.piCongrLeft,
    MeasurableEquiv.sumPiEquivProdPi,Equiv.piCongrLeft',Equiv.sumPiEquivProdPi]
@[simp] theorem splitCoordinates_snd {k l : ℕ} (x : Coordinates (k+l)) :
    (splitCoordinates k l x).2 = suffix k l x := by
  funext i
  simp [splitCoordinates,suffix,MeasurableEquiv.piCongrLeft,Equiv.piCongrLeft,
    MeasurableEquiv.sumPiEquivProdPi,Equiv.piCongrLeft',Equiv.sumPiEquivProdPi]

theorem prefix_continuous (k l : ℕ) : Continuous (prefixCoords k l) := by unfold prefixCoords; fun_prop
theorem suffix_continuous (k l : ℕ) : Continuous (suffix k l) := by unfold suffix; fun_prop

theorem splitCoordinates_measurePreserving (k l : ℕ) :
    MeasurePreserving (splitCoordinates k l) (cube (k+l)) ((cube k).prod (cube l)) :=
  (measurePreserving_sumPiEquivProdPi (fun _ : Fin k ⊕ Fin l => unitInterval)).comp
    (measurePreserving_piCongrLeft (fun _ : Fin k ⊕ Fin l => unitInterval) finSumFinEquiv.symm)

@[simp] theorem prefix_splitCoordinates_symm {k l : ℕ} (p : Coordinates k × Coordinates l) :
    prefixCoords k l ((splitCoordinates k l).symm p) = p.1 := by
  rw [← splitCoordinates_fst,MeasurableEquiv.apply_symm_apply]
@[simp] theorem suffix_splitCoordinates_symm {k l : ℕ} (p : Coordinates k × Coordinates l) :
    suffix k l ((splitCoordinates k l).symm p) = p.2 := by
  rw [← splitCoordinates_snd,MeasurableEquiv.apply_symm_apply]

@[simp] theorem prefix_sub {k l : ℕ} (x y : Coordinates (k+l)) :
    prefixCoords k l (x-y) = prefixCoords k l x-prefixCoords k l y := rfl
@[simp] theorem suffix_sub {k l : ℕ} (x y : Coordinates (k+l)) :
    suffix k l (x-y) = suffix k l x-suffix k l y := rfl

theorem kernel_split {k l : ℕ} (κ : ℝ) (x : Coordinates (k+l)) :
    kernel κ x = kernel κ (prefixCoords k l x)*kernel κ (suffix k l x) :=
  Fin.prod_univ_add (fun i => scalar κ (x i))

/-- Integrating away the unobserved coordinates of the actual smoothed
density gives precisely the smoothed density of the actual prefixCoords marginal. -/
theorem density_prefix_fiber {k l : ℕ} (κ : ℝ) (μ : Measure (Coordinates (k+l)))
    [IsProbabilityMeasure μ] (x : Coordinates k) :
    (∫ z, density κ μ ((splitCoordinates k l).symm (x,z)) ∂cube l) =
      density κ (μ.map (prefixCoords k l)) x := by
  have hm : Measurable (fun p : Coordinates l × Coordinates (k+l) =>
      (splitCoordinates k l).symm (x,p.1)-p.2) :=
    ((splitCoordinates k l).symm.measurable.comp (measurable_const.prodMk measurable_fst)).sub measurable_snd
  have hi : Integrable (fun p : Coordinates l × Coordinates (k+l) =>
      kernel κ ((splitCoordinates k l).symm (x,p.1)-p.2)) ((cube l).prod μ) := by
    apply Integrable.of_bound ((kernel_smooth (k+l) κ).continuous.measurable.comp hm).aestronglyMeasurable
      ((Real.exp |κ|/normalizer κ)^(k+l))
    exact Eventually.of_forall (fun p => by
      change ‖kernel κ ((splitCoordinates k l).symm (x,p.1)-p.2)‖ ≤ _
      rw [Real.norm_eq_abs,abs_of_pos (kernel_pos κ _)]
      exact (kernel_bounds κ _).2)
  change (∫ z,∫ y,kernel κ ((splitCoordinates k l).symm (x,z)-y) ∂μ ∂cube l) = _
  rw [integral_integral_swap hi]
  unfold density
  rw [integral_map (prefix_continuous k l).measurable.aemeasurable
    (show AEStronglyMeasurable (fun y => kernel κ (x-y)) (μ.map (prefixCoords k l)) from
      ((kernel_smooth k κ).continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  simp_rw [kernel_split,prefix_sub,suffix_sub,prefix_splitCoordinates_symm,suffix_splitCoordinates_symm]
  rw [integral_const_mul,integral_cube_sub (kernel_periodic l κ) (kernel_smooth l κ).continuous,
    kernel_integral,mul_one]

theorem integral_smoothLaw_density {n : ℕ} (κ : ℝ) (μ : Measure (Coordinates n))
    [IsProbabilityMeasure μ] (f : Coordinates n → ℝ) :
    (∫ x, f x ∂smoothLaw κ μ) = ∫ x, density κ μ x*f x ∂cube n := by
  change (∫ x, f x ∂(cube n).withDensity (fun x => ENNReal.ofReal (density κ μ x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (density_smooth κ μ).continuous.measurable.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (density_pos κ μ _).le,smul_eq_mul]

/-- Equality of the genuine prefix marginal measures, not only formal
factorization of a density expression. -/
theorem smoothLaw_prefix {k l : ℕ} (κ : ℝ) (μ : Measure (Coordinates (k+l)))
    [IsProbabilityMeasure μ] :
    (smoothLaw κ μ).map (prefixCoords k l) = smoothLaw κ (μ.map (prefixCoords k l)) := by
  letI : IsProbabilityMeasure (smoothLaw κ μ) := smoothLaw_probability κ μ
  letI : IsProbabilityMeasure (μ.map (prefixCoords k l)) :=
    Measure.isProbabilityMeasure_map (prefix_continuous k l).measurable.aemeasurable
  letI : IsProbabilityMeasure (smoothLaw κ (μ.map (prefixCoords k l))) := smoothLaw_probability κ _
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map (prefix_continuous k l).measurable.aemeasurable f.continuous.aestronglyMeasurable,
    integral_smoothLaw_density,integral_smoothLaw_density]
  let g : Coordinates (k+l) → ℝ := fun y => density κ μ y*f (prefixCoords k l y)
  have hg : Continuous g := (density_smooth κ μ).continuous.mul
    (f.continuous.comp (prefix_continuous k l))
  have hgi := continuous_integrable_cube hg
  have hmp := (splitCoordinates_measurePreserving k l).symm
  have hi : Integrable (fun p => g ((splitCoordinates k l).symm p)) ((cube k).prod (cube l)) :=
    (hmp.integrable_comp hg.aestronglyMeasurable).mpr hgi
  calc
    _ = ∫ p, g ((splitCoordinates k l).symm p) ∂(cube k).prod (cube l) :=
      (hmp.integral_comp' g).symm
    _ = ∫ x, ∫ z, g ((splitCoordinates k l).symm (x,z)) ∂cube l ∂cube k := integral_prod _ hi
    _ = _ := by
      simp only [g,prefix_splitCoordinates_symm]
      simp_rw [integral_mul_const,density_prefix_fiber]

end SharpWasserstein.PeriodicConvolution
