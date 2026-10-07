module

public import SharpWasserstein.Compat
public import SharpWasserstein.GaussianVectorEntropy

@[expose] public section

/-!
# Finite Gaussian-history entropy cost

The history law is recursively constructed by adjoining genuine Gaussian
vector transitions. The entropy chain identity is proved by induction over
these actual laws. A measurable observation of the history obeys the resulting
cost bound by data processing. Expectations are under the first history law.
-/

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators

namespace SharpWasserstein

/-- Auxiliary initial labels together with the Gaussian innovations generated
so far. Labels may encode an initial coupling. -/
abbrev GaussianHistory (A : Type*) (d n : ℕ) := A × Configuration d n

/-- Appending one state is a measurable equivalence with a history/state pair. -/
def gaussianHistoryStepEquiv (A : Type*) [MeasurableSpace A] (d n : ℕ) :
    GaussianHistory A d (n + 1) ≃ᵐ GaussianHistory A d n × Position d :=
  ((MeasurableEquiv.refl A).prodCongr (splitLastParticle d n)).trans
    MeasurableEquiv.prodAssoc.symm

/-- The actual iterated transition law; no chain-entropy property enters its
definition. -/
def gaussianHistoryLaw {A : Type*} [MeasurableSpace A] {d : ℕ}
    (μ₀ : Measure (GaussianHistory A d 0))
    (a : (n : ℕ) → GaussianHistory A d n → Position d)
    (ha : ∀ n, Measurable (a n)) (v : ℕ → ℝ≥0) :
    (n : ℕ) → Measure (GaussianHistory A d n)
  | 0 => μ₀
  | n + 1 => ((gaussianHistoryLaw μ₀ a ha v n) ⊗ₘ gaussianVectorKernel (a n) (ha n) (v n)).map
      (gaussianHistoryStepEquiv A d n).symm

instance gaussianHistoryLaw_isProbability {A : Type*} [MeasurableSpace A] {d : ℕ}
    (μ₀ : Measure (GaussianHistory A d 0)) [IsProbabilityMeasure μ₀]
    (a : (n : ℕ) → GaussianHistory A d n → Position d)
    (ha : ∀ n, Measurable (a n)) (v : ℕ → ℝ≥0) (n : ℕ) :
    IsProbabilityMeasure (gaussianHistoryLaw μ₀ a ha v n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure μ₀)
  | succ n ih =>
    letI := ih
    exact Measure.isProbabilityMeasure_map (gaussianHistoryStepEquiv A d n).symm.measurable.aemeasurable

/-- One-step entropy identity for the actual growing history law. -/
theorem klDiv_gaussianHistoryLaw_succ {A : Type*} [MeasurableSpace A] {d : ℕ}
    (μ₀ ν₀ : Measure (GaussianHistory A d 0)) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure ν₀]
    (a b : (n : ℕ) → GaussianHistory A d n → Position d)
    (ha : ∀ n, Measurable (a n)) (hb : ∀ n, Measurable (b n))
    (v : ℕ → ℝ≥0) (hv : ∀ n, v n ≠ 0) (n : ℕ) :
    klDiv (gaussianHistoryLaw μ₀ a ha v (n + 1)) (gaussianHistoryLaw ν₀ b hb v (n + 1)) =
      klDiv (gaussianHistoryLaw μ₀ a ha v n) (gaussianHistoryLaw ν₀ b hb v n) +
        ∫⁻ x, ENNReal.ofReal (∑ i, (a n x i - b n x i) ^ 2 / (2 * v n))
          ∂gaussianHistoryLaw μ₀ a ha v n := by
  simp only [gaussianHistoryLaw]
  rw [klDiv_map_measurableEquiv]
  exact klDiv_gaussianVectorKernel_compProd _ _ _ _ _ _ (hv n)

/-- The full finite-history entropy is the sum of the actual conditional
Gaussian costs, plus initial entropy. This identity includes infinite costs. -/
theorem klDiv_gaussianHistoryLaw {A : Type*} [MeasurableSpace A] {d : ℕ}
    (μ₀ ν₀ : Measure (GaussianHistory A d 0)) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure ν₀]
    (a b : (n : ℕ) → GaussianHistory A d n → Position d)
    (ha : ∀ n, Measurable (a n)) (hb : ∀ n, Measurable (b n))
    (v : ℕ → ℝ≥0) (hv : ∀ n, v n ≠ 0) (n : ℕ) :
    klDiv (gaussianHistoryLaw μ₀ a ha v n) (gaussianHistoryLaw ν₀ b hb v n) =
      klDiv μ₀ ν₀ + ∑ j ∈ Finset.range n,
        ∫⁻ x, ENNReal.ofReal (∑ i, (a j x i - b j x i) ^ 2 / (2 * v j))
          ∂gaussianHistoryLaw μ₀ a ha v j := by
  induction n with
  | zero => simp [gaussianHistoryLaw]
  | succ n ih =>
    rw [klDiv_gaussianHistoryLaw_succ μ₀ ν₀ a b ha hb v hv n, ih, Finset.sum_range_succ, add_assoc]

/-- Finite-cost common-initial-law version of the exact entropy identity. -/
theorem klDiv_gaussianHistoryLaw_same_initial {A : Type*} [MeasurableSpace A] {d : ℕ}
    (μ₀ : Measure (GaussianHistory A d 0)) [IsProbabilityMeasure μ₀]
    (a b : (n : ℕ) → GaussianHistory A d n → Position d)
    (ha : ∀ n, Measurable (a n)) (hb : ∀ n, Measurable (b n))
    (v : ℕ → ℝ≥0) (hv : ∀ n, v n ≠ 0) (n : ℕ)
    (hcost : ∀ j < n, Integrable (fun x ↦ ∑ i, (a j x i - b j x i) ^ 2 / (2 * v j))
      (gaussianHistoryLaw μ₀ a ha v j)) :
    klDiv (gaussianHistoryLaw μ₀ a ha v n) (gaussianHistoryLaw μ₀ b hb v n) =
      ENNReal.ofReal (∑ j ∈ Finset.range n,
        ∫ x, ∑ i, (a j x i - b j x i) ^ 2 / (2 * v j) ∂gaussianHistoryLaw μ₀ a ha v j) := by
  rw [klDiv_gaussianHistoryLaw μ₀ μ₀ a b ha hb v hv n, klDiv_self, zero_add]
  have heq (j : ℕ) (hj : j ∈ Finset.range n) :
      ∫⁻ x, ENNReal.ofReal (∑ i, (a j x i - b j x i) ^ 2 / (2 * v j))
          ∂gaussianHistoryLaw μ₀ a ha v j =
        ENNReal.ofReal (∫ x, ∑ i, (a j x i - b j x i) ^ 2 / (2 * v j)
          ∂gaussianHistoryLaw μ₀ a ha v j) :=
    (ofReal_integral_eq_lintegral_ofReal (hcost j (Finset.mem_range.mp hj))
      (Filter.Eventually.of_forall fun _ ↦ Finset.sum_nonneg fun _ _ ↦ by positivity)).symm
  rw [Finset.sum_congr rfl heq]
  exact (ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ integral_nonneg fun _ ↦
    Finset.sum_nonneg fun _ _ ↦ by positivity)).symm

/-- Data processing yields the endpoint entropy-cost bound from the constructed
Gaussian history laws, with no assumed pathwise entropy estimate. -/
theorem klDiv_gaussianHistory_observation_le_cost {A E : Type*}
    [MeasurableSpace A] [MeasurableSpace E] {d : ℕ}
    (μ₀ : Measure (GaussianHistory A d 0)) [IsProbabilityMeasure μ₀]
    (a b : (n : ℕ) → GaussianHistory A d n → Position d)
    (ha : ∀ n, Measurable (a n)) (hb : ∀ n, Measurable (b n))
    (v : ℕ → ℝ≥0) (hv : ∀ n, v n ≠ 0) (n : ℕ)
    (hcost : ∀ j < n, Integrable (fun x ↦ ∑ i, (a j x i - b j x i) ^ 2 / (2 * v j))
      (gaussianHistoryLaw μ₀ a ha v j))
    (f : GaussianHistory A d n → E) (hf : Measurable f) :
    klDiv ((gaussianHistoryLaw μ₀ a ha v n).map f) ((gaussianHistoryLaw μ₀ b hb v n).map f) ≤
      ENNReal.ofReal (∑ j ∈ Finset.range n,
        ∫ x, ∑ i, (a j x i - b j x i) ^ 2 / (2 * v j) ∂gaussianHistoryLaw μ₀ a ha v j) := by
  calc
    _ ≤ klDiv (gaussianHistoryLaw μ₀ a ha v n) (gaussianHistoryLaw μ₀ b hb v n) := klDiv_map_le hf
    _ = _ := klDiv_gaussianHistoryLaw_same_initial μ₀ a b ha hb v hv n hcost

end SharpWasserstein
