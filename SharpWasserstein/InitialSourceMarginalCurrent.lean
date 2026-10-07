module

public import SharpWasserstein.Compat
public import SharpWasserstein.InitialSourceMarginalConfiguration

@[expose] public section

/-! The tested reference-minus-particle current disintegrates to the genuine
conditional marginal drift. Exchangeability is used only in the already proved
particle-current disintegration; no independence of the full law is assumed. -/
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff BigOperators
namespace SharpWasserstein.InitialSourceMarginal
open WeightedTangent InitialSourcePermutation
variable {d m N : ℕ} {b : Position d → Position d → Position d} {B : ℝ}

/-- Bounded scalar products are genuinely integrable under any finite law. -/
theorem integrable_bounded_mul {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {f g : Ω → ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hfb : ∃ C,∀ x,|f x| ≤ C) (hgb : ∃ C,∀ x,|g x| ≤ C) : Integrable (fun x => f x*g x) μ := by
  obtain ⟨C,hC⟩ := hfb
  obtain ⟨D,hD⟩ := hgb
  exact integrable_bounded_scalar μ (hf.mul hg) (fun x =>
    (abs_mul _ _).trans_le (mul_le_mul (hC x) (hD x) (abs_nonneg _) ((abs_nonneg _).trans (hC x))))

/-- Measurability of each actual reference-drift coordinate. -/
theorem reference_coordinate_measurable (q : Measure (Position d)) [IsProbabilityMeasure q]
    (hb : Measurable (Function.uncurry b)) (hbnd : ∀ u w a,|b u w a| ≤ B)
    (i : Fin m) (a : Fin d) : Measurable (fun x : Configuration d m => nonlinearDrift b q (x i) a) := by
  simp_rw [nonlinearDrift_coordinate q hb hbnd]
  have hF : Measurable (Function.uncurry (fun (x : Configuration d m) (y : Position d) => b (x i) y a)) :=
    ((measurable_pi_apply a).comp hb).comp
      (show Measurable (fun p : Configuration d m × Position d => (p.1 i,p.2)) from
        ((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd)
  exact hF.stronglyMeasurable.integral_prod_right.measurable

theorem reference_coordinate_bound (q : Measure (Position d)) [IsProbabilityMeasure q]
    (hb : Measurable (Function.uncurry b)) (hbnd : ∀ u w a,|b u w a| ≤ B)
    (x : Position d) (a : Fin d) : |nonlinearDrift b q x a| ≤ B := by
  rw [nonlinearDrift_coordinate q hb hbnd]
  exact integral_bounded_observable_abs_le
    (((measurable_pi_apply a).comp hb).comp measurable_prodMk_left) (fun y => hbnd x y a)

theorem particle_coordinate_measurable (hb : Measurable (Function.uncurry b))
    (i : Fin N) (a : Fin d) : Measurable (fun x : Configuration d N => particleDrift b x i a) := by
  simp only [particleDrift,Pi.smul_apply,Finset.sum_apply,smul_eq_mul]
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro j _
  exact ((measurable_pi_apply a).comp hb).comp
    (show Measurable (fun x : Configuration d N => (x i,x j)) from
      (measurable_pi_apply i).prodMk (measurable_pi_apply j))

theorem particle_coordinate_bounded (hbnd : ∀ u w a,|b u w a| ≤ B)
    (i : Fin N) (a : Fin d) : ∃ C,∀ x : Configuration d N,|particleDrift b x i a| ≤ C := by
  refine ⟨|(N:ℝ)⁻¹| *((N:ℝ)*B),fun x => ?_⟩
  simp only [particleDrift,Pi.smul_apply,Finset.sum_apply,smul_eq_mul,abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact (Finset.abs_sum_le_sum_abs _ _).trans (by simpa using Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => hbnd (x i) (x j) a))

theorem conditional_coordinate_measurable (hm : m < N)
    (P : Measure (Configuration d N)) [IsProbabilityMeasure P]
    (hb : Measurable (Function.uncurry b)) (i : Fin m) (a : Fin d) :
    Measurable (marginalScalarDrift hm P b i a) := by
  unfold marginalScalarDrift
  apply Measurable.add
  · apply measurable_const.mul
    apply Finset.measurable_sum
    intro j _
    exact ((measurable_pi_apply a).comp hb).comp
      (show Measurable (fun x : Configuration d m => (x i,x j)) from
        (measurable_pi_apply i).prodMk (measurable_pi_apply j))
  · apply measurable_const.mul
    have hF : Measurable (Function.uncurry (fun (x : Configuration d m) (y : Position d) => b (x i) y a)) :=
      ((measurable_pi_apply a).comp hb).comp
        (show Measurable (fun p : Configuration d m × Position d => (p.1 i,p.2)) from
          ((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd)
    exact hF.stronglyMeasurable.integral_kernel_prod_right.measurable

theorem conditional_coordinate_bounded (hm : m < N)
    (P : Measure (Configuration d N)) [IsProbabilityMeasure P]
    (hb : Measurable (Function.uncurry b)) (hbnd : ∀ u w a,|b u w a| ≤ B)
    (i : Fin m) (a : Fin d) : ∃ C,∀ x,|marginalScalarDrift hm P b i a x| ≤ C := by
  refine ⟨|(N:ℝ)⁻¹| *((m:ℝ)*B)+|((N:ℝ)-m)/N| *B,fun x => ?_⟩
  apply (abs_add_le _ _).trans
  apply add_le_add
  · rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    exact (Finset.abs_sum_le_sum_abs _ _).trans (by simpa using Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => hbnd (x i) (x j) a))
  · rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    exact integral_bounded_observable_abs_le
      (((measurable_pi_apply a).comp hb).comp measurable_prodMk_left) (fun y => hbnd (x i) y a)

/-- Actual tested coordinate discrepancy, with the reference-minus-particle
sign preserved under the genuine conditional marginal. -/
theorem integral_current_eq_conditional (hm : m < N)
    (P : Measure (Configuration d N)) [IsProbabilityMeasure P] (hex : Exchangeable P)
    (q : Measure (Position d)) [IsProbabilityMeasure q]
    (hB : 0 ≤ B) (hb : Measurable (Function.uncurry b)) (hbnd : ∀ u w a,|b u w a| ≤ B)
    {g : Configuration d m → ℝ} (hg : Measurable g) (hgb : ∃ C,∀ x,|g x| ≤ C)
    (i : Fin m) (a : Fin d) :
    (∫ z,g (restrictCoordinates hm.le z)*initialCurrent b q z (Fin.castLE hm.le i) a ∂P) =
      ∫ x,g x*(nonlinearDrift b q (x i) a-marginalScalarDrift hm P b i a x) ∂marginal hm.le P := by
  have hgp := hg.comp (measurable_restrictCoordinates hm.le)
  have hgbp : ∃ C,∀ z : Configuration d N,|g (restrictCoordinates hm.le z)| ≤ C :=
    hgb.imp (fun C hC z => hC _)
  have hr := integrable_bounded_mul (marginal hm.le P) hg (reference_coordinate_measurable q hb hbnd i a)
    hgb ⟨B,fun x => reference_coordinate_bound q hb hbnd (x i) a⟩
  have hrp := integrable_bounded_mul P hgp (reference_coordinate_measurable q hb hbnd (Fin.castLE hm.le i) a)
    hgbp ⟨B,fun x => reference_coordinate_bound q hb hbnd (x (Fin.castLE hm.le i)) a⟩
  have hpp := integrable_bounded_mul P hgp (particle_coordinate_measurable hb (Fin.castLE hm.le i) a)
    hgbp (particle_coordinate_bounded hbnd (Fin.castLE hm.le i) a)
  have hcp := integrable_bounded_mul (marginal hm.le P) hg (conditional_coordinate_measurable hm P hb i a)
    hgb (conditional_coordinate_bounded hm P hb hbnd i a)
  dsimp only [Function.comp_apply] at hrp hpp
  simp only [initialCurrent,Pi.sub_apply,mul_sub]
  rw [integral_sub hrp hpp,integral_sub hr hcp]
  congr 1
  · exact (integral_map (measurable_restrictCoordinates hm.le).aemeasurable hr.1).symm
  · obtain ⟨C,hC⟩ := hgb
    exact integral_particleDrift_eq_marginalScalarDrift hm hex hB hb hbnd hg hC i a

/-- Boundedness is stable under the scalar difference needed by the source. -/
theorem bounded_sub {Ω : Type*} {f g : Ω → ℝ}
    (hf : ∃ C,∀ x,|f x| ≤ C) (hg : ∃ C,∀ x,|g x| ≤ C) :
    ∃ C,∀ x,|f x-g x| ≤ C := by
  obtain ⟨C,hC⟩ := hf
  obtain ⟨D,hD⟩ := hg
  exact ⟨C+D,fun x => (abs_sub _ _).trans (add_le_add (hC x) (hD x))⟩

/-- Cylinder pairing of one genuine full source is exactly the sharp
conditional marginal source's generator pairing. -/
theorem configurationMarginalSource_generator
    [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
    [MeasurableSpace (Point (m*d))] [BorelSpace (Point (m*d))]
    (hm : m < N) (P : Measure (Configuration d N)) [IsProbabilityMeasure P]
    (hex : Exchangeable P) (q : Measure (Position d)) [IsProbabilityMeasure q]
    (hB : 0 ≤ B) (hb : Measurable (Function.uncurry b)) (hbnd : ∀ u w a,|b u w a| ≤ B)
    (σ : ConfigurationTest d N →ₗ[ℝ] ℝ)
    (hσ : ∀ φ : ConfigurationTest d N,σ φ = ∫ x,
      generator (fun z i => nonlinearDrift b q (z i)) φ.val x -
        generator (particleDrift b) φ.val x ∂P)
    (φ : ConfigurationTest d m) :
    configurationMarginalSource hm.le P σ φ = ∫ x,
      generator (fun z i => nonlinearDrift b q (z i)) φ.val x -
        generator (fun z i a => marginalScalarDrift hm P b i a z) φ.val x ∂marginal hm.le P := by
  have hv := initialCurrent_memLp (by omega : 0<N) P q hb hbnd
  rw [configurationMarginalSource_apply_current hm.le P q b σ hσ hv]
  have hg (i : Fin m) (a : Fin d) :=
    (CompactGenerator.coordinate_test φ.property i a).1.continuous.measurable
  have hgb (i : Fin m) (a : Fin d) : ∃ C,∀ x,|coordinateDerivative φ.val i a x| ≤ C := by
    obtain ⟨C,hC⟩ := (CompactGenerator.coordinate_test φ.property i a).2.exists_bound_of_continuous
      (CompactGenerator.coordinate_test φ.property i a).1.continuous
    exact ⟨C,fun x => by simpa only [Real.norm_eq_abs] using hC x⟩
  have hfull (i : Fin m) (a : Fin d) : Integrable (fun z =>
      coordinateDerivative φ.val i a (restrictCoordinates hm.le z)*
        initialCurrent b q z (Fin.castLE hm.le i) a) P := by
    apply integrable_bounded_mul P ((hg i a).comp (measurable_restrictCoordinates hm.le))
      ((reference_coordinate_measurable q hb hbnd (Fin.castLE hm.le i) a).sub
        (particle_coordinate_measurable hb (Fin.castLE hm.le i) a))
    · exact (hgb i a).imp (fun C hC z => hC _)
    · exact bounded_sub ⟨B,fun z => reference_coordinate_bound q hb hbnd _ a⟩
        (particle_coordinate_bounded hbnd (Fin.castLE hm.le i) a)
  have hcond (i : Fin m) (a : Fin d) : Integrable (fun x =>
      coordinateDerivative φ.val i a x*(nonlinearDrift b q (x i) a-
        marginalScalarDrift hm P b i a x)) (marginal hm.le P) := by
    apply integrable_bounded_mul _ (hg i a)
      ((reference_coordinate_measurable q hb hbnd i a).sub (conditional_coordinate_measurable hm P hb i a))
      (hgb i a)
    exact bounded_sub ⟨B,fun x => reference_coordinate_bound q hb hbnd _ a⟩
      (conditional_coordinate_bounded hm P hb hbnd i a)
  calc
    _ = ∫ z,∑ i : Fin m,∑ a : Fin d,coordinateDerivative φ.val i a (restrictCoordinates hm.le z)*
        initialCurrent b q z (Fin.castLE hm.le i) a ∂P := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [fderiv_eq_sum_coordinateDerivative]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro a _
      exact mul_comm _ _
    _ = ∑ i : Fin m,∑ a : Fin d,∫ z,coordinateDerivative φ.val i a (restrictCoordinates hm.le z)*
        initialCurrent b q z (Fin.castLE hm.le i) a ∂P := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun a _ => hfull i a))]
      apply Finset.sum_congr rfl
      intro i _
      exact integral_finsetSum _ (fun a _ => hfull i a)
    _ = ∑ i : Fin m,∑ a : Fin d,∫ x,coordinateDerivative φ.val i a x*
        (nonlinearDrift b q (x i) a-marginalScalarDrift hm P b i a x) ∂marginal hm.le P := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro a _
      exact integral_current_eq_conditional hm P hex q hB hb hbnd (hg i a) (hgb i a) i a
    _ = ∫ x,∑ i : Fin m,∑ a : Fin d,coordinateDerivative φ.val i a x*
        (nonlinearDrift b q (x i) a-marginalScalarDrift hm P b i a x) ∂marginal hm.le P := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun a _ => hcond i a))]
      apply Finset.sum_congr rfl
      intro i _
      exact (integral_finsetSum _ (fun a _ => hcond i a)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [generator,mul_sub,Finset.sum_sub_distrib]
      simp_rw [mul_comm (coordinateDerivative φ.val _ _ x)]
      ring

/-- Equality with any sharp marginal witness follows from its actual compact
generator pairing; consistency is a conclusion, never a hypothesis. -/
theorem configurationMarginalSource_eq
    [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
    [MeasurableSpace (Point (m*d))] [BorelSpace (Point (m*d))]
    (hm : m < N) (P : Measure (Configuration d N)) [IsProbabilityMeasure P]
    (hex : Exchangeable P) (q : Measure (Position d)) [IsProbabilityMeasure q]
    (hB : 0 ≤ B) (hb : Measurable (Function.uncurry b)) (hbnd : ∀ u w a,|b u w a| ≤ B)
    (σ : ConfigurationTest d N →ₗ[ℝ] ℝ)
    (hσ : ∀ φ : ConfigurationTest d N,σ φ = ∫ x,
      generator (fun z i => nonlinearDrift b q (z i)) φ.val x -
        generator (particleDrift b) φ.val x ∂P)
    (ζ : ConfigurationTest d m →ₗ[ℝ] ℝ)
    (hζ : ∀ φ : ConfigurationTest d m,ζ φ = ∫ x,
      generator (fun z i => nonlinearDrift b q (z i)) φ.val x -
        generator (fun z i a => marginalScalarDrift hm P b i a z) φ.val x ∂marginal hm.le P) :
    configurationMarginalSource hm.le P σ = ζ := by
  ext φ
  rw [configurationMarginalSource_generator hm P hex q hB hb hbnd σ hσ,hζ]

end SharpWasserstein.InitialSourceMarginal
