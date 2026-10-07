module

public import SharpWasserstein.Compat
public import SharpWasserstein.EntropyObservableVector
public import Mathlib.InformationTheory.KullbackLeibler.ChainRule
public import Mathlib.Probability.Kernel.CompProdEqIff
public import Mathlib.Probability.Kernel.Composition.WithDensity

@[expose] public section

/-!
# Integrated conditional relative entropy

Jointly measurable kernel Radon–Nikodym derivatives give measurability of the
actual conditional KL divergence. Tonelli's theorem then identifies its
integral with the relative entropy of two joint laws with the same first
marginal. Combining this identity with Mathlib's joint-law chain rule yields
the conditional entropy increment. No chain-rule equality is assumed.

`CountableOrCountablyGenerated` is the explicit hypothesis needed for jointly
measurable kernel densities. It holds for the Euclidean state spaces used in
the manuscript.
-/

noncomputable section

open MeasureTheory InformationTheory ProbabilityTheory
open scoped ENNReal

namespace SharpWasserstein

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSpace.CountableOrCountablyGenerated A B]
  {μ ν : Measure A} {κ η : Kernel A B}
  [IsFiniteKernel κ] [IsFiniteKernel η]

/-- The conditional KL of two finite kernels is a measurable extended-real
function. The jointly measurable kernel density avoids choosing unrelated
versions of the Radon–Nikodym derivative in each fiber. -/
theorem measurable_kernel_klDiv : Measurable (fun a ↦ klDiv (κ a) (η a)) := by
  classical
  let G : A → ℝ≥0∞ := fun a ↦
    ∫⁻ b, ENNReal.ofReal (klFun (κ.rnDeriv η a b).toReal) ∂η a
  have hm : Measurable (fun p : A × B ↦
      ENNReal.ofReal (klFun (κ.rnDeriv η p.1 p.2).toReal)) :=
    (measurable_klFun.comp (Kernel.measurable_rnDeriv κ η).ennreal_toReal).ennreal_ofReal
  have hG : Measurable G := hm.lintegral_kernel_prod_right'
  have hformula : (fun a ↦ klDiv (κ a) (η a)) =
      fun a ↦ if κ a ≪ η a then G a else ∞ := by
    funext a
    rw [klDiv_eq_lintegral_klFun]
    split_ifs
    · apply lintegral_congr_ae
      filter_upwards [Kernel.rnDeriv_eq_rnDeriv_measure (κ := κ) (η := η) (a := a)]
        with b hb
      simp only [hb]
    · rfl
  rw [hformula]
  exact Measurable.ite (Kernel.measurableSet_absolutelyContinuous κ η) hG measurable_const

variable [IsFiniteMeasure μ]

/-- The joint density for a fixed first marginal is the jointly measurable
conditional kernel density. -/
theorem rnDeriv_compProd_same_base_eq_kernel
    (hac : μ ⊗ₘ κ ≪ μ ⊗ₘ η) :
    (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) =ᵐ[μ ⊗ₘ η]
      fun p ↦ κ.rnDeriv η p.1 p.2 := by
  have hkernel : κ =ᵐ[μ] η.withDensity (κ.rnDeriv η) := by
    filter_upwards [hac.kernel_of_compProd] with a ha
    exact (Kernel.withDensity_rnDeriv_eq ha).symm
  have hdensity : μ ⊗ₘ κ = (μ ⊗ₘ η).withDensity
      (fun p ↦ κ.rnDeriv η p.1 p.2) := by
    rw [Measure.compProd_congr hkernel,
      Measure.compProd_withDensity (Kernel.measurable_rnDeriv κ η)]
  rw [hdensity]
  exact Measure.rnDeriv_withDensity _ (Kernel.measurable_rnDeriv κ η)

/-- Under absolute continuity of the joint laws, the conditional KL integrates
to their actual extended-real KL divergence, with no finiteness assumption on KL. -/
theorem lintegral_kernel_klDiv_eq_compProd
    (hac : μ ⊗ₘ κ ≪ μ ⊗ₘ η) :
    ∫⁻ a, klDiv (κ a) (η a) ∂μ = klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) := by
  rw [klDiv_eq_lintegral_klFun_of_ac hac]
  calc
    ∫⁻ a, klDiv (κ a) (η a) ∂μ
        = ∫⁻ a, ∫⁻ b, ENNReal.ofReal (klFun (κ.rnDeriv η a b).toReal) ∂η a ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hac.kernel_of_compProd] with a ha
      rw [klDiv_eq_lintegral_klFun_of_ac ha]
      apply lintegral_congr_ae
      filter_upwards [Kernel.rnDeriv_eq_rnDeriv_measure (κ := κ) (η := η) (a := a)]
        with b hb
      simp only [hb]
    _ = ∫⁻ p, ENNReal.ofReal (klFun (κ.rnDeriv η p.1 p.2).toReal) ∂(μ ⊗ₘ η) := by
      rw [Measure.lintegral_compProd]
      exact (measurable_klFun.comp
        (Kernel.measurable_rnDeriv κ η).ennreal_toReal).ennreal_ofReal
    _ = ∫⁻ p, ENNReal.ofReal (klFun ((μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) p).toReal)
        ∂(μ ⊗ₘ η) := by
      apply lintegral_congr_ae
      filter_upwards [rnDeriv_compProd_same_base_eq_kernel hac] with p hp
      simp only [hp]

/-- Finite joint KL implies finite conditional KL almost everywhere. -/
theorem ae_kernel_klDiv_ne_top
    (hfinite : klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) ≠ ∞) :
    ∀ᵐ a ∂μ, klDiv (κ a) (η a) ≠ ∞ := by
  have heq := lintegral_kernel_klDiv_eq_compProd (klDiv_ne_top_iff.mp hfinite).1
  exact (ae_lt_top measurable_kernel_klDiv (heq ▸ hfinite)).mono fun _ h ↦ h.ne

/-- The real conditional entropy is integrable when the joint entropy is finite. -/
theorem integrable_kernel_klDiv_toReal
    (hfinite : klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) ≠ ∞) :
    Integrable (fun a ↦ (klDiv (κ a) (η a)).toReal) μ := by
  apply integrable_toReal_of_lintegral_ne_top measurable_kernel_klDiv.aemeasurable
  rwa [lintegral_kernel_klDiv_eq_compProd (klDiv_ne_top_iff.mp hfinite).1]

/-- The Bochner integral of actual conditional KL equals the real joint KL. -/
theorem integral_kernel_klDiv_toReal_eq_compProd
    (hfinite : klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) ≠ ∞) :
    ∫ a, (klDiv (κ a) (η a)).toReal ∂μ =
      (klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)).toReal := by
  rw [integral_toReal measurable_kernel_klDiv.aemeasurable
    ((ae_kernel_klDiv_ne_top hfinite).mono fun _ h ↦ lt_top_iff_ne_top.mpr h)]
  rw [lintegral_kernel_klDiv_eq_compProd (klDiv_ne_top_iff.mp hfinite).1]

section Markov

variable [IsFiniteMeasure ν] [IsMarkovKernel κ] [IsMarkovKernel η]

omit [MeasurableSpace.CountableOrCountablyGenerated A B] [IsFiniteKernel κ]
  [IsFiniteKernel η] in
/-- Finite entropy of the full pair implies finite entropy for its conditional
comparison with the same first marginal. -/
theorem conditional_joint_klDiv_ne_top
    (hfinite : klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) ≠ ∞) :
    klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) ≠ ∞ := by
  rw [klDiv_compProd_eq_add] at hfinite
  exact (ENNReal.add_ne_top.mp hfinite).2

/-- The integral conditional entropy is exactly the full entropy minus the
entropy of the first marginal. Finiteness of the full joint KL is the only
entropy-finiteness hypothesis. -/
theorem integral_kernel_klDiv_eq_entropy_increment
    (hfinite : klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) ≠ ∞) :
    ∫ a, (klDiv (κ a) (η a)).toReal ∂μ =
      (klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η)).toReal - (klDiv μ ν).toReal := by
  have hchain := klDiv_compProd_eq_add (μ := μ) (ν := ν) (κ := κ) (η := η)
  have hne : klDiv μ ν ≠ ∞ ∧ klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) ≠ ∞ := by
    apply ENNReal.add_ne_top.mp
    rwa [← hchain]
  rw [integral_kernel_klDiv_toReal_eq_compProd hne.2, hchain,
    ENNReal.toReal_add hne.1 hne.2]
  ring

/-- The integrated conditional entropy controls a vector-valued conditional
expectation discrepancy. This derives the integrated conditional Pinsker
bound used for the external source, including its integrability. -/
theorem integrated_kernel_norm_difference_sq_le_entropy_increment
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (hfinite : klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) ≠ ∞)
    {F : A → B → E} {M : ℝ} (hM : 0 ≤ M)
    (hF : StronglyMeasurable (Function.uncurry F))
    (hbound : ∀ᵐ a ∂μ, ∀ᵐ b ∂η a, ‖F a b‖ ≤ M) :
    ∫ a, ‖(∫ b, F a b ∂κ a) - ∫ b, F a b ∂η a‖ ^ 2 ∂μ
      ≤ 2 * M ^ 2 * ((klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η)).toReal - (klDiv μ ν).toReal) := by
  have hcond := conditional_joint_klDiv_ne_top hfinite
  have hboundKL := kernel_norm_integral_difference_sq_le_klDiv hM
    (ae_kernel_klDiv_ne_top hcond)
    (Filter.Eventually.of_forall fun a ↦
      (hF.comp_measurable measurable_prodMk_left).aestronglyMeasurable) hbound
  have hmeas : StronglyMeasurable (fun a ↦
      ‖(∫ b, F a b ∂κ a) - ∫ b, F a b ∂η a‖ ^ 2) :=
    ((hF.integral_kernel_prod_right (κ := κ)).sub
      (hF.integral_kernel_prod_right (κ := η))).norm.pow 2
  have hright := (integrable_kernel_klDiv_toReal hcond).const_mul (2 * M ^ 2)
  have hleft : Integrable (fun a ↦
      ‖(∫ b, F a b ∂κ a) - ∫ b, F a b ∂η a‖ ^ 2) μ :=
    hright.mono_nonneg hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _) hboundKL
  have h := integral_mono_ae hleft hright hboundKL
  rwa [integral_const_mul, integral_kernel_klDiv_eq_entropy_increment hfinite] at h

end Markov

end SharpWasserstein
