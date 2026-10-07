module

public import SharpWasserstein.Compat
public import SharpWasserstein.WeightedPeriodicFourierClosure
public import SharpWasserstein.WeightedPeriodicFourierScale

@[expose] public section

/-! Physical-period periodic gradients in an unchanged Euclidean carrying law.
The scalar test is evaluated at x/P, while vector values and their weighted
L² norm retain the original physical Euclidean coordinates. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff BigOperators InnerProductSpace ENNReal
namespace SharpWasserstein.WeightedPeriodicFourierPhysical
open PeriodicIntegrationByParts PeriodicFourierTests PeriodicFourierPolynomials
open PeriodicBochner PeriodicConvolution WeightedTangent
open PeriodicSmoothGradient (SmoothPeriodicTest)
open WeightedPeriodicFourierScale (rescale)
variable {n : ℕ}

/-- The actual test in physical Euclidean coordinates. -/
def physicalPotential (P : ℝ) (f : Coordinates n → ℝ) : Point n → ℝ :=
  pullback (rescale P⁻¹ f)

theorem physicalPotential_smooth (P : ℝ) {f : Coordinates n → ℝ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (physicalPotential P f) :=
  (WeightedPeriodicFourierScale.rescale_smooth P⁻¹ hf).comp (coordinateEquiv n).contDiff

/-- The physical vector gradient carries exactly the inverse-period factor. -/
theorem physicalPotential_gradient (P : ℝ) {f : Coordinates n → ℝ}
    (hf : ContDiff ℝ ∞ f) (x : Point n) :
    gradient (physicalPotential P f) x =
      P⁻¹ • euclideanGradient f (P⁻¹ • coordinateEquiv n x) := by
  ext i
  rw [physicalPotential,WeightedPeriodicFourier.pullback_gradient_component,
    WeightedPeriodicFourierScale.coordinatePartial_rescale P⁻¹ (hf.differentiable (by simp))]
  simp only [PiLp.smul_apply,smul_eq_mul,euclideanGradient_apply]

theorem physicalPotential_gradient_bound (P : ℝ) (f : Coordinates n → ℝ)
    (hf : ContDiff ℝ ∞ f) (hp : Periodic f) :
    ∃ C : ℝ, ∀ x, ‖gradient (physicalPotential P f) x‖ ≤ C := by
  obtain ⟨C,_,hC⟩ := PeriodicSmoothBounds.norm_bound
    (euclideanGradient_periodic hp) (euclideanGradient_continuous hf)
  refine ⟨|P⁻¹| *C,fun x => ?_⟩
  rw [physicalPotential_gradient P hf,norm_smul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hC _) (abs_nonneg _)

theorem physicalPotential_value_bound (P : ℝ) (f : Coordinates n → ℝ)
    (hf : ContDiff ℝ ∞ f) (hp : Periodic f) :
    ∃ C : ℝ, ∀ x, |physicalPotential P f x| ≤ C := by
  obtain ⟨C,_,hC⟩ := PeriodicSmoothBounds.norm_bound hp hf.continuous
  exact ⟨C,fun x => hC (P⁻¹ • coordinateEquiv n x)⟩

theorem physicalPotential_gradient_sub_bound (P : ℝ) (f g : Coordinates n → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {ε : ℝ}
    (hε : 0 ≤ ε) (h : ∀ i y, |coordinatePartial f i y-coordinatePartial g i y| ≤ ε)
    (x : Point n) :
    ‖gradient (physicalPotential P f) x-gradient (physicalPotential P g) x‖ ≤
      |P⁻¹| *(ε*Real.sqrt n) := by
  rw [physicalPotential_gradient P hf,physicalPotential_gradient P hg,← smul_sub,norm_smul,
    Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  have hb := HierarchyAlgebra.block_norm_le
    (euclideanGradient f (P⁻¹ • coordinateEquiv n x)-euclideanGradient g (P⁻¹ • coordinateEquiv n x))
    ε hε (fun i => by simp only [PiLp.sub_apply,Real.norm_eq_abs,euclideanGradient_apply]; exact h i _)
  simpa only [Fintype.card_fin] using hb

/-- Normalization and inverse normalization exhaust all smooth physical-period tests. -/
theorem exists_normalized_test {P : ℝ} (hP : 0 < P) (f : Coordinates n → ℝ)
    (hf : ContDiff ℝ ∞ f) (hp : WeightedPeriodicFourierScale.PeriodicOf P f) :
    ∃ g : SmoothPeriodicTest n, physicalPotential P g.val = pullback f := by
  refine ⟨⟨rescale P f,WeightedPeriodicFourierScale.rescale_smooth P hf,
    WeightedPeriodicFourierScale.rescale_periodic hp⟩,?_⟩
  unfold physicalPotential
  rw [WeightedPeriodicFourierScale.rescale_inverse hP.ne']

variable [MeasurableSpace (Point n)] [BorelSpace (Point n)]
variable (P : ℝ) (μ : Measure (Point n)) [IsFiniteMeasure μ]

theorem physical_gradient_memLp (f : Coordinates n → ℝ)
    (hf : ContDiff ℝ ∞ f) (hp : Periodic f) : MemLp (gradient (physicalPotential P f)) 2 μ :=
  bounded_smooth_gradient_memLp μ _ (physicalPotential_smooth P hf)
    (physicalPotential_gradient_bound P f hf hp)

def gradientVector (f : Coordinates n → ℝ) (hf : ContDiff ℝ ∞ f) (hp : Periodic f) :
    gradientClosure μ :=
  ⟨(physical_gradient_memLp P μ f hf hp).toLp (gradient (physicalPotential P f)),
    bounded_smooth_gradient_memClosure μ _ (physicalPotential_smooth P hf)
      (physicalPotential_value_bound P f hf hp) (physicalPotential_gradient_bound P f hf hp)
      (physical_gradient_memLp P μ f hf hp)⟩

theorem gradientVector_ae (f : Coordinates n → ℝ) (hf : ContDiff ℝ ∞ f) (hp : Periodic f) :
    (gradientVector P μ f hf hp : Lp (Point n) 2 μ) =ᵐ[μ] gradient (physicalPotential P f) :=
  (physical_gradient_memLp P μ f hf hp).coeFn_toLp

def periodicGradientMap : SmoothPeriodicTest n →ₗ[ℝ] gradientClosure μ where
  toFun f := gradientVector P μ f.val f.property.1 f.property.2
  map_add' f g := by
    apply Subtype.ext
    change (gradientVector P μ (f+g).val (f+g).property.1 (f+g).property.2).val =
      (gradientVector P μ f.val f.property.1 f.property.2).val +
        (gradientVector P μ g.val g.property.1 g.property.2).val
    apply Lp.ext
    filter_upwards [gradientVector_ae P μ (f+g).val (f+g).property.1 (f+g).property.2,
      gradientVector_ae P μ f.val f.property.1 f.property.2,
      gradientVector_ae P μ g.val g.property.1 g.property.2,
      Lp.coeFn_add (gradientVector P μ f.val f.property.1 f.property.2).val
        (gradientVector P μ g.val g.property.1 g.property.2).val] with x hfg hf hg ha
    rw [hfg,ha]
    simp only [Pi.add_apply,hf,hg]
    unfold gradient
    change (InnerProductSpace.toDual ℝ (Point n)).symm
      (fderiv ℝ (physicalPotential P f.val+physicalPotential P g.val) x) = _
    rw [fderiv_add (f := physicalPotential P f.val) (g := physicalPotential P g.val)
      ((physicalPotential_smooth P f.property.1).differentiable (by simp) x)
      ((physicalPotential_smooth P g.property.1).differentiable (by simp) x),map_add]
  map_smul' c f := by
    apply Subtype.ext
    change (gradientVector P μ (c • f).val (c • f).property.1 (c • f).property.2).val =
      c • (gradientVector P μ f.val f.property.1 f.property.2).val
    apply Lp.ext
    filter_upwards [gradientVector_ae P μ (c • f).val (c • f).property.1 (c • f).property.2,
      gradientVector_ae P μ f.val f.property.1 f.property.2,
      Lp.coeFn_smul c (gradientVector P μ f.val f.property.1 f.property.2).val] with x hcf hf ha
    rw [hcf,ha]
    simp only [Pi.smul_apply,hf]
    unfold gradient
    change (InnerProductSpace.toDual ℝ (Point n)).symm
      (fderiv ℝ (c • physicalPotential P f.val) x) = _
    rw [fderiv_const_smul (f := physicalPotential P f.val)
      ((physicalPotential_smooth P f.property.1).differentiable (by simp) x)]
    simp only [map_smul]

def trialGradient (s : Finset ((Fin n → ℤ) × Bool)) :
    frequencySpace s →ₗ[ℝ] gradientClosure μ :=
  (periodicGradientMap P μ).comp (WeightedPeriodicFourier.frequencyTestInclusion s)

def trialSpace (s : Finset ((Fin n → ℤ) × Bool)) : Submodule ℝ (gradientClosure μ) :=
  (trialGradient P μ s).range

instance trialSpace_finiteDimensional (s : Finset ((Fin n → ℤ) × Bool)) :
    FiniteDimensional ℝ (trialSpace P μ s) := LinearMap.finiteDimensional_range (trialGradient P μ s)

/-- Actual physical-period Fourier closure, with the unmodified physical norm. -/
def periodicSpace : Submodule ℝ (gradientClosure μ) :=
  (⨆ s, trialSpace P μ s).topologicalClosure

instance periodicSpace_complete : CompleteSpace (periodicSpace P μ) := by
  unfold periodicSpace
  infer_instance

theorem trialSpace_le_periodicSpace (s : Finset ((Fin n → ℤ) × Bool)) :
    trialSpace P μ s ≤ periodicSpace P μ :=
  (le_iSup (trialSpace P μ) s).trans (iSup (trialSpace P μ)).le_topologicalClosure

theorem gradientVector_norm_sub_le (f g : Coordinates n → ℝ)
    (hf : ContDiff ℝ ∞ f) (hpf : Periodic f) (hg : ContDiff ℝ ∞ g) (hpg : Periodic g)
    {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ i y, |coordinatePartial f i y-coordinatePartial g i y| ≤ ε) :
    ‖gradientVector P μ f hf hpf-gradientVector P μ g hg hpg‖ ≤
      (measureUnivNNReal μ : ℝ)^((2 : ENNReal).toReal⁻¹)*(|P⁻¹| *(ε*Real.sqrt n)) := by
  change ‖(gradientVector P μ f hf hpf).val-(gradientVector P μ g hg hpg).val‖ ≤ _
  apply Lp.norm_le_of_ae_bound (mul_nonneg (abs_nonneg _) (mul_nonneg hε (Real.sqrt_nonneg _)))
  filter_upwards [Lp.coeFn_sub (gradientVector P μ f hf hpf).val (gradientVector P μ g hg hpg).val,
    gradientVector_ae P μ f hf hpf,gradientVector_ae P μ g hg hpg] with x ha hb hc
  rw [ha]
  simp only [Pi.sub_apply,hb,hc]
  exact physicalPotential_gradient_sub_bound P f g hf hg hε h x

/-- Fourier density at the genuine physical period, including singular μ. -/
theorem gradientVector_mem_periodicSpace (f : Coordinates n → ℝ)
    (hf : ContDiff ℝ ∞ f) (hp : Periodic f) : gradientVector P μ f hf hp ∈ periodicSpace P μ := by
  classical
  rw [periodicSpace,← SetLike.mem_coe,Submodule.topologicalClosure_coe,Metric.mem_closure_iff]
  intro ε hε
  let C : ℝ := (measureUnivNNReal μ : ℝ)^((2 : ENNReal).toReal⁻¹)*|P⁻¹| *Real.sqrt n
  have hC : 0 ≤ C := mul_nonneg
    (mul_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _) (abs_nonneg _)) (Real.sqrt_nonneg _)
  have hη : 0 < ε/(C+1) := div_pos hε (by positivity)
  obtain ⟨s,p,hpS,_,hpa⟩ := WeightedPeriodicFourier.exists_frequencySpace_uniform_C1 f hp hf hη
  have hpp := frequencySpace_properties (frequencySet s) hpS
  refine ⟨gradientVector P μ p hpp.1 hpp.2.1,?_,?_⟩
  · exact le_iSup (trialSpace P μ) (frequencySet s) ⟨⟨p,hpS⟩,rfl⟩
  · rw [dist_eq_norm,norm_sub_rev]
    have hb := gradientVector_norm_sub_le P μ p f hpp.1 hpp.2.1 hf hp hη.le
      (fun i y => (hpa i y).le)
    calc
      _ ≤ C*(ε/(C+1)) := by simpa only [C,mul_assoc,mul_comm,mul_left_comm] using hb
      _ < (C+1)*(ε/(C+1)) := mul_lt_mul_of_pos_right (lt_add_one C) hη
      _ = ε := mul_div_cancel₀ ε (by positivity : C+1 ≠ 0)

theorem periodicSpace_eq_smoothGradientClosure : periodicSpace P μ =
    (periodicGradientMap P μ).range.topologicalClosure := by
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · apply iSup_le
      intro s v hv
      obtain ⟨f,rfl⟩ := hv
      exact (periodicGradientMap P μ).range.le_topologicalClosure
        ⟨WeightedPeriodicFourier.frequencyTestInclusion s f,rfl⟩
    · exact (periodicGradientMap P μ).range.isClosed_topologicalClosure
  · apply Submodule.topologicalClosure_minimal
    · rintro v ⟨f,rfl⟩
      exact gradientVector_mem_periodicSpace P μ f.val f.property.1 f.property.2
    · exact (iSup (trialSpace P μ)).isClosed_topologicalClosure

end SharpWasserstein.WeightedPeriodicFourierPhysical
