module

public import SharpWasserstein.Compat
public import SharpWasserstein.GaussianEntropyCost
public import SharpWasserstein.ExchangeableEntropy
public import Mathlib.Probability.Kernel.Composition.Prod

@[expose] public section

/-!
# Gaussian vector transition entropy

Finite products of real Gaussian laws have the exact sum-of-squares KL cost.
The product measures and measurable state-dependent transition kernels are
constructed explicitly, providing the dimension-independent Euler cost.
-/

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Real
open scoped ENNReal NNReal BigOperators

namespace SharpWasserstein

/-- Independent Gaussian coordinates with prescribed mean and common variance. -/
def gaussianVectorLaw {d : ℕ} (a : Fin d → ℝ) (v : ℝ≥0) : Measure (Fin d → ℝ) :=
  Measure.pi fun i ↦ gaussianReal (a i) v

instance gaussianVectorLaw_isProbability {d : ℕ} (a : Fin d → ℝ) (v : ℝ≥0) :
    IsProbabilityMeasure (gaussianVectorLaw a v) := by unfold gaussianVectorLaw; infer_instance

/-- Split a real vector into its prefix and last coordinate. -/
def splitLastReal (n : ℕ) : (Fin (n + 1) → ℝ) ≃ᵐ (Fin n → ℝ) × ℝ :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) (Fin.last n)).trans
    MeasurableEquiv.prodComm

theorem gaussianVectorLaw_split {n : ℕ} (a : Fin (n + 1) → ℝ) (v : ℝ≥0) :
    (gaussianVectorLaw a v).map (splitLastReal n) =
      (gaussianVectorLaw (fun i ↦ a i.castSucc) v).prod (gaussianReal (a (Fin.last n)) v) := by
  have h := measurePreserving_piFinSuccAbove (fun i : Fin (n + 1) ↦ gaussianReal (a i) v) (Fin.last n)
  have hp := (Measure.measurePreserving_swap.comp h).map_eq
  change (Measure.pi fun i : Fin (n + 1) ↦ gaussianReal (a i) v).map
    (Prod.swap ∘ MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) (Fin.last n)) =
      (Measure.pi fun i : Fin n ↦ gaussianReal (a i.castSucc) v).prod (gaussianReal (a (Fin.last n)) v)
  simpa only [Fin.succAbove_last] using hp

/-- A constant Gaussian Markov kernel is the usual constant kernel. -/
theorem gaussianMeanKernel_const {A : Type*} [MeasurableSpace A] (a : ℝ) (v : ℝ≥0) :
    gaussianMeanKernel (fun _ : A ↦ a) measurable_const v = Kernel.const A (gaussianReal a v) := by
  rfl

/-- Tensoring with an independent scalar Gaussian adds its exact mean-shift cost. -/
theorem klDiv_prod_gaussianReal {A : Type*} [MeasurableSpace A]
    (μ ν : Measure A) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (a b : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    klDiv (μ.prod (gaussianReal a v)) (ν.prod (gaussianReal b v)) =
      klDiv μ ν + ENNReal.ofReal ((a - b) ^ 2 / (2 * v)) := by
  have h := klDiv_gaussianMeanKernel_compProd μ ν (fun _ ↦ a) (fun _ ↦ b)
    measurable_const measurable_const hv
  simpa only [gaussianMeanKernel_const, Measure.compProd_const, lintegral_const,
    measure_univ, mul_one] using h

/-- Exact KL divergence of actual Gaussian product probability laws. -/
theorem klDiv_gaussianVectorLaw {d : ℕ} (a b : Fin d → ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    klDiv (gaussianVectorLaw a v) (gaussianVectorLaw b v) =
      ENNReal.ofReal (∑ i, (a i - b i) ^ 2 / (2 * v)) := by
  induction d with
  | zero =>
    rw [probabilityMeasure_eq_of_subsingleton (gaussianVectorLaw a v) (gaussianVectorLaw b v), klDiv_self]
    simp
  | succ n ih =>
    rw [← klDiv_map_measurableEquiv (splitLastReal n), gaussianVectorLaw_split,
      gaussianVectorLaw_split, klDiv_prod_gaussianReal _ _ _ _ hv, ih]
    rw [← ENNReal.ofReal_add (Finset.sum_nonneg fun _ _ ↦ by positivity) (by positivity)]
    congr 1
    rw [Fin.sum_univ_castSucc]

theorem klDiv_gaussianVectorLaw_ne_top {d : ℕ} (a b : Fin d → ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    klDiv (gaussianVectorLaw a v) (gaussianVectorLaw b v) ≠ ∞ := by
  rw [klDiv_gaussianVectorLaw a b hv]
  exact ENNReal.ofReal_ne_top

theorem toReal_klDiv_gaussianVectorLaw {d : ℕ} (a b : Fin d → ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    (klDiv (gaussianVectorLaw a v) (gaussianVectorLaw b v)).toReal =
      ∑ i, (a i - b i) ^ 2 / (2 * v) := by
  rw [klDiv_gaussianVectorLaw a b hv, ENNReal.toReal_ofReal (Finset.sum_nonneg fun _ _ ↦ by positivity)]

/-- Gaussian product laws depend measurably on their mean vector. -/
theorem measurable_gaussianVectorLaw (d : ℕ) (v : ℝ≥0) :
    Measurable (fun a : Fin d → ℝ ↦ gaussianVectorLaw a v) := by
  induction d with
  | zero =>
    have heq : (fun a : Fin 0 → ℝ ↦ gaussianVectorLaw a v) =
        fun _ ↦ gaussianVectorLaw (fun _ ↦ (0 : ℝ)) v := by
      funext a
      exact probabilityMeasure_eq_of_subsingleton _ _
    rw [heq]
    exact measurable_const
  | succ n ih =>
    let pre : (Fin (n + 1) → ℝ) → Fin n → ℝ := fun a i ↦ a i.castSucc
    have hp : Measurable pre := Measurable.of_eval (fun i ↦ measurable_pi_apply i.castSucc)
    let κ : Kernel (Fin (n + 1) → ℝ) (Fin n → ℝ) := ⟨fun a ↦ gaussianVectorLaw (pre a) v, ih.comp hp⟩
    haveI : IsMarkovKernel κ := ⟨fun a ↦ by change IsProbabilityMeasure (gaussianVectorLaw (pre a) v); infer_instance⟩
    let η := gaussianMeanKernel (fun a : Fin (n + 1) → ℝ ↦ a (Fin.last n)) (measurable_pi_apply _) v
    let K := (κ ×ₖ η).map (splitLastReal n).symm
    have hK (a : Fin (n + 1) → ℝ) : K a = gaussianVectorLaw a v := by
      rw [show K a = ((κ ×ₖ η) a).map (splitLastReal n).symm from
        Kernel.map_apply _ (splitLastReal n).symm.measurable a, Kernel.prod_apply]
      change ((gaussianVectorLaw (fun i ↦ a i.castSucc) v).prod
        (gaussianReal (a (Fin.last n)) v)).map (splitLastReal n).symm = gaussianVectorLaw a v
      rw [← gaussianVectorLaw_split a v, Measure.map_map (splitLastReal n).symm.measurable
        (splitLastReal n).measurable, (splitLastReal n).symm_comp_self, Measure.map_id]
    have heq : (fun a : Fin (n + 1) → ℝ ↦ gaussianVectorLaw a v) = K := by
      funext a
      exact (hK a).symm
    rw [heq]
    exact K.measurable

/-- A genuine measurable Gaussian vector transition kernel. -/
def gaussianVectorKernel {A : Type*} [MeasurableSpace A] {d : ℕ}
    (a : A → Fin d → ℝ) (ha : Measurable a) (v : ℝ≥0) : Kernel A (Fin d → ℝ) where
  toFun x := gaussianVectorLaw (a x) v
  measurable' := (measurable_gaussianVectorLaw d v).comp ha

instance gaussianVectorKernel_isMarkov {A : Type*} [MeasurableSpace A] {d : ℕ}
    (a : A → Fin d → ℝ) (ha : Measurable a) (v : ℝ≥0) : IsMarkovKernel (gaussianVectorKernel a ha v) where
  isProbabilityMeasure x := by change IsProbabilityMeasure (gaussianVectorLaw (a x) v); infer_instance

/-- Actual Gaussian vector transition KL, integrated under the first base law. -/
theorem klDiv_gaussianVectorKernel_same_base {A : Type*} [MeasurableSpace A] {d : ℕ}
    (μ : Measure A) [IsFiniteMeasure μ] (a b : A → Fin d → ℝ)
    (ha : Measurable a) (hb : Measurable b) {v : ℝ≥0} (hv : v ≠ 0) :
    klDiv (μ ⊗ₘ gaussianVectorKernel a ha v) (μ ⊗ₘ gaussianVectorKernel b hb v) =
      ∫⁻ x, ENNReal.ofReal (∑ i, (a x i - b x i) ^ 2 / (2 * v)) ∂μ := by
  have hac : μ ⊗ₘ gaussianVectorKernel a ha v ≪ μ ⊗ₘ gaussianVectorKernel b hb v :=
    Measure.AbsolutelyContinuous.compProd_right
      (Filter.Eventually.of_forall fun x ↦
        (klDiv_ne_top_iff.mp (klDiv_gaussianVectorLaw_ne_top (a x) (b x) hv)).1)
  rw [← lintegral_kernel_klDiv_eq_compProd hac]
  exact lintegral_congr fun x ↦ klDiv_gaussianVectorLaw (a x) (b x) hv

/-- Vector transition chain rule with an actual control-cost integral. -/
theorem klDiv_gaussianVectorKernel_compProd {A : Type*} [MeasurableSpace A] {d : ℕ}
    (μ ν : Measure A) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (a b : A → Fin d → ℝ)
    (ha : Measurable a) (hb : Measurable b) {v : ℝ≥0} (hv : v ≠ 0) :
    klDiv (μ ⊗ₘ gaussianVectorKernel a ha v) (ν ⊗ₘ gaussianVectorKernel b hb v) =
      klDiv μ ν + ∫⁻ x, ENNReal.ofReal (∑ i, (a x i - b x i) ^ 2 / (2 * v)) ∂μ := by
  rw [klDiv_compProd_eq_add, klDiv_gaussianVectorKernel_same_base μ a b ha hb hv]

theorem klDiv_gaussianVectorKernel_compProd_of_integrable {A : Type*} [MeasurableSpace A] {d : ℕ}
    (μ ν : Measure A) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (a b : A → Fin d → ℝ)
    (ha : Measurable a) (hb : Measurable b) {v : ℝ≥0} (hv : v ≠ 0)
    (hcost : Integrable (fun x ↦ ∑ i, (a x i - b x i) ^ 2 / (2 * v)) μ) :
    klDiv (μ ⊗ₘ gaussianVectorKernel a ha v) (ν ⊗ₘ gaussianVectorKernel b hb v) =
      klDiv μ ν + ENNReal.ofReal (∫ x, ∑ i, (a x i - b x i) ^ 2 / (2 * v) ∂μ) := by
  rw [klDiv_gaussianVectorKernel_compProd μ ν a b ha hb hv,
    ofReal_integral_eq_lintegral_ofReal hcost (Filter.Eventually.of_forall fun x ↦
      Finset.sum_nonneg fun _ _ ↦ by positivity)]

/-- Exact Euler-step KL in arbitrary finite dimension. The noise covariance is
2 delta times the identity and the cost coefficient is delta/4, independent
of dimension. Controls are measurable functions of the entire base history. -/
theorem klDiv_vectorEuler_step {A : Type*} [MeasurableSpace A] {d : ℕ}
    (μ ν : Measure A) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (state u w : A → Fin d → ℝ) (hs : Measurable state) (hu : Measurable u) (hw : Measurable w)
    (δ : ℝ≥0) (hδ : δ ≠ 0) (hcost : Integrable (fun x ↦ ∑ i, (u x i - w x i) ^ 2) μ) :
    klDiv (μ ⊗ₘ gaussianVectorKernel (fun x i ↦ state x i + δ * u x i)
        (by fun_prop) (2 * δ))
      (ν ⊗ₘ gaussianVectorKernel (fun x i ↦ state x i + δ * w x i)
        (by fun_prop) (2 * δ)) =
      klDiv μ ν + ENNReal.ofReal ((δ : ℝ) / 4 * ∫ x, ∑ i, (u x i - w x i) ^ 2 ∂μ) := by
  have hδr : (δ : ℝ) ≠ 0 := by exact_mod_cast hδ
  have heq : (fun x ↦ ∑ i, ((state x i + δ * u x i) - (state x i + δ * w x i)) ^ 2 /
      (2 * ((2 * δ : ℝ≥0) : ℝ))) = fun x ↦ (δ : ℝ) / 4 * ∑ i, (u x i - w x i) ^ 2 := by
    funext x
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [NNReal.coe_mul, NNReal.coe_ofNat]
    field_simp
    ring
  have hi : Integrable (fun x ↦ ∑ i,
      ((state x i + δ * u x i) - (state x i + δ * w x i)) ^ 2 /
      (2 * ((2 * δ : ℝ≥0) : ℝ))) μ := by
    rw [heq]
    exact hcost.const_mul _
  rw [klDiv_gaussianVectorKernel_compProd_of_integrable μ ν _ _ _ _
    (mul_ne_zero (by norm_num) hδ) hi, heq, integral_const_mul]

end SharpWasserstein
