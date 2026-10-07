module

public import SharpWasserstein.Compat
public import SharpWasserstein.WeightedPeriodicFourierApproximation
public import SharpWasserstein.PeriodicSmoothGradient
public import SharpWasserstein.HierarchyAlgebra

@[expose] public section

/-! The genuine periodic gradient closure for any finite Borel measure,
including singular measures. Uniform C¹ Fourier recovery proves density in
this weighted space; the larger compact-test gradient closure remains distinct. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff BigOperators InnerProductSpace ENNReal
namespace SharpWasserstein.WeightedPeriodicFourier
open PeriodicIntegrationByParts PeriodicFourierTests PeriodicFourierPolynomials
open PeriodicBochner PeriodicConvolution WeightedTangent
open PeriodicSmoothGradient (SmoothPeriodicTest)
variable {n : ℕ}

theorem pullback_gradient_component (f : Coordinates n → ℝ) (x : Point n) (i : Fin n) :
    gradient (pullback f) x i = coordinatePartial f i (coordinateEquiv n x) := by
  rw [← PDEPairings.directionDeriv_eq_gradient_component,directionDeriv_pullback]

theorem pullback_gradient_bound (f : Coordinates n → ℝ)
    (hf : ContDiff ℝ ∞ f) (hp : Periodic f) :
    ∃ C : ℝ, ∀ x, ‖gradient (pullback f) x‖ ≤ C := by
  obtain ⟨C,_,hC⟩ := PeriodicSmoothBounds.norm_bound
    (euclideanGradient_periodic hp) (euclideanGradient_continuous hf)
  refine ⟨C,fun x => ?_⟩
  simpa only [euclideanGradient,ContinuousLinearEquiv.symm_apply_apply] using hC (coordinateEquiv n x)

theorem pullback_value_bound (f : Coordinates n → ℝ)
    (hf : ContDiff ℝ ∞ f) (hp : Periodic f) :
    ∃ C : ℝ, ∀ x, |pullback f x| ≤ C := by
  obtain ⟨C,_,hC⟩ := PeriodicSmoothBounds.norm_bound hp hf.continuous
  exact ⟨C,fun x => hC (coordinateEquiv n x)⟩

theorem pullback_gradient_sub_bound (f g : Coordinates n → ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) (h : ∀ i y, |coordinatePartial f i y-coordinatePartial g i y| ≤ ε)
    (x : Point n) :
    ‖gradient (pullback f) x-gradient (pullback g) x‖ ≤ ε*Real.sqrt n := by
  have hb := HierarchyAlgebra.block_norm_le
    (gradient (pullback f) x-gradient (pullback g) x) ε hε (fun i => by
      simp only [PiLp.sub_apply,Real.norm_eq_abs,pullback_gradient_component]
      exact h i (coordinateEquiv n x))
  simpa only [Fintype.card_fin] using hb

variable [MeasurableSpace (Point n)] [BorelSpace (Point n)]
variable (μ : Measure (Point n)) [IsFiniteMeasure μ]

theorem periodic_gradient_memLp (f : Coordinates n → ℝ)
    (hf : ContDiff ℝ ∞ f) (hp : Periodic f) : MemLp (gradient (pullback f)) 2 μ :=
  bounded_smooth_gradient_memLp μ (pullback f) (hf.comp (coordinateEquiv n).contDiff)
    (pullback_gradient_bound f hf hp)

/-- Actual periodic gradient, embedded by verified cutoff approximation. -/
def gradientVector (f : Coordinates n → ℝ) (hf : ContDiff ℝ ∞ f) (hp : Periodic f) :
    gradientClosure μ :=
  ⟨(periodic_gradient_memLp μ f hf hp).toLp (gradient (pullback f)),
    bounded_smooth_gradient_memClosure μ (pullback f) (hf.comp (coordinateEquiv n).contDiff)
      (pullback_value_bound f hf hp) (pullback_gradient_bound f hf hp)
      (periodic_gradient_memLp μ f hf hp)⟩

theorem gradientVector_ae (f : Coordinates n → ℝ) (hf : ContDiff ℝ ∞ f) (hp : Periodic f) :
    (gradientVector μ f hf hp : Lp (Point n) 2 μ) =ᵐ[μ] gradient (pullback f) :=
  (periodic_gradient_memLp μ f hf hp).coeFn_toLp

def periodicGradientMap : SmoothPeriodicTest n →ₗ[ℝ] gradientClosure μ where
  toFun f := gradientVector μ f.val f.property.1 f.property.2
  map_add' f g := by
    apply Subtype.ext
    change (gradientVector μ (f+g).val (f+g).property.1 (f+g).property.2).val =
      (gradientVector μ f.val f.property.1 f.property.2).val +
        (gradientVector μ g.val g.property.1 g.property.2).val
    apply Lp.ext
    filter_upwards [gradientVector_ae μ (f+g).val (f+g).property.1 (f+g).property.2,
      gradientVector_ae μ f.val f.property.1 f.property.2,
      gradientVector_ae μ g.val g.property.1 g.property.2,
      Lp.coeFn_add (gradientVector μ f.val f.property.1 f.property.2).val
        (gradientVector μ g.val g.property.1 g.property.2).val] with x hfg hf hg ha
    rw [hfg,ha]
    simp only [Pi.add_apply,hf,hg]
    unfold gradient
    change (InnerProductSpace.toDual ℝ (Point n)).symm
      (fderiv ℝ (pullback f.val+pullback g.val) x) = _
    rw [fderiv_add (f := pullback f.val) (g := pullback g.val) ((f.property.1.comp (coordinateEquiv n).contDiff).differentiable (by simp) x)
      ((g.property.1.comp (coordinateEquiv n).contDiff).differentiable (by simp) x),map_add]
  map_smul' c f := by
    apply Subtype.ext
    change (gradientVector μ (c • f).val (c • f).property.1 (c • f).property.2).val =
      c • (gradientVector μ f.val f.property.1 f.property.2).val
    apply Lp.ext
    filter_upwards [gradientVector_ae μ (c • f).val (c • f).property.1 (c • f).property.2,
      gradientVector_ae μ f.val f.property.1 f.property.2,
      Lp.coeFn_smul c (gradientVector μ f.val f.property.1 f.property.2).val] with x hcf hf ha
    rw [hcf,ha]
    simp only [Pi.smul_apply,hf]
    unfold gradient
    change (InnerProductSpace.toDual ℝ (Point n)).symm
      (fderiv ℝ (c • pullback f.val) x) = _
    rw [fderiv_const_smul (f := pullback f.val) ((f.property.1.comp (coordinateEquiv n).contDiff).differentiable (by simp) x)]
    simp only [map_smul]

def frequencyTestInclusion (s : Finset ((Fin n → ℤ) × Bool)) :
    frequencySpace s →ₗ[ℝ] SmoothPeriodicTest n where
  toFun f := ⟨f.val,(frequencySpace_properties s f.property).1,
    (frequencySpace_properties s f.property).2.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def trialGradient (s : Finset ((Fin n → ℤ) × Bool)) :
    frequencySpace s →ₗ[ℝ] gradientClosure μ :=
  (periodicGradientMap μ).comp (frequencyTestInclusion s)

def trialSpace (s : Finset ((Fin n → ℤ) × Bool)) : Submodule ℝ (gradientClosure μ) :=
  (trialGradient μ s).range

instance trialSpace_finiteDimensional (s : Finset ((Fin n → ℤ) × Bool)) :
    FiniteDimensional ℝ (trialSpace μ s) := LinearMap.finiteDimensional_range (trialGradient μ s)

/-- Closure of genuine finite Fourier gradients in the actual carrying measure. -/
def periodicSpace : Submodule ℝ (gradientClosure μ) :=
  (⨆ s, trialSpace μ s).topologicalClosure

instance periodicSpace_complete : CompleteSpace (periodicSpace μ) := by
  unfold periodicSpace
  infer_instance

theorem trialSpace_le_periodicSpace (s : Finset ((Fin n → ℤ) × Bool)) :
    trialSpace μ s ≤ periodicSpace μ :=
  (le_iSup (trialSpace μ) s).trans (iSup (trialSpace μ)).le_topologicalClosure

theorem gradientVector_norm_sub_le (f g : Coordinates n → ℝ)
    (hf : ContDiff ℝ ∞ f) (hpf : Periodic f) (hg : ContDiff ℝ ∞ g) (hpg : Periodic g)
    {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ i y, |coordinatePartial f i y-coordinatePartial g i y| ≤ ε) :
    ‖gradientVector μ f hf hpf-gradientVector μ g hg hpg‖ ≤
      (measureUnivNNReal μ : ℝ)^((2 : ENNReal).toReal⁻¹)*(ε*Real.sqrt n) := by
  change ‖(gradientVector μ f hf hpf).val-(gradientVector μ g hg hpg).val‖ ≤ _
  apply Lp.norm_le_of_ae_bound (mul_nonneg hε (Real.sqrt_nonneg _))
  filter_upwards [Lp.coeFn_sub (gradientVector μ f hf hpf).val (gradientVector μ g hg hpg).val,
    gradientVector_ae μ f hf hpf,gradientVector_ae μ g hg hpg] with x ha hb hc
  rw [ha]
  simp only [Pi.sub_apply,hb,hc]
  exact pullback_gradient_sub_bound f g hε h x

/-- Uniform C¹ recovery gives weighted Fourier density even for singular μ. -/
theorem gradientVector_mem_periodicSpace (f : Coordinates n → ℝ)
    (hf : ContDiff ℝ ∞ f) (hp : Periodic f) : gradientVector μ f hf hp ∈ periodicSpace μ := by
  classical
  rw [periodicSpace,← SetLike.mem_coe,Submodule.topologicalClosure_coe,Metric.mem_closure_iff]
  intro ε hε
  let C : ℝ := (measureUnivNNReal μ : ℝ)^((2 : ENNReal).toReal⁻¹)*Real.sqrt n
  have hC : 0 ≤ C := mul_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _) (Real.sqrt_nonneg _)
  have hη : 0 < ε/(C+1) := div_pos hε (by positivity)
  obtain ⟨s,p,hpS,_,hpa⟩ := exists_frequencySpace_uniform_C1 f hp hf hη
  have hpp := frequencySpace_properties (frequencySet s) hpS
  refine ⟨gradientVector μ p hpp.1 hpp.2.1,?_,?_⟩
  · exact le_iSup (trialSpace μ) (frequencySet s) ⟨⟨p,hpS⟩,rfl⟩
  · rw [dist_eq_norm,norm_sub_rev]
    have hb := gradientVector_norm_sub_le μ p f hpp.1 hpp.2.1 hf hp hη.le
      (fun i y => (hpa i y).le)
    calc
      _ ≤ C*(ε/(C+1)) := by simpa only [C,mul_assoc,mul_comm,mul_left_comm] using hb
      _ < (C+1)*(ε/(C+1)) := mul_lt_mul_of_pos_right (lt_add_one C) hη
      _ = ε := mul_div_cancel₀ ε (by positivity : C+1 ≠ 0)

/-- The weighted periodic Fourier closure is exactly the closure of genuine
smooth periodic test gradients; it is not asserted to equal all gradients. -/
theorem periodicSpace_eq_smoothGradientClosure : periodicSpace μ =
    (periodicGradientMap μ).range.topologicalClosure := by
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · apply iSup_le
      intro s v hv
      obtain ⟨f,rfl⟩ := hv
      exact (periodicGradientMap μ).range.le_topologicalClosure
        ⟨frequencyTestInclusion s f,rfl⟩
    · exact (periodicGradientMap μ).range.isClosed_topologicalClosure
  · apply Submodule.topologicalClosure_minimal
    · rintro v ⟨f,rfl⟩
      exact gradientVector_mem_periodicSpace μ f.val f.property.1 f.property.2
    · exact (iSup (trialSpace μ)).isClosed_topologicalClosure

end SharpWasserstein.WeightedPeriodicFourier
