module

public import SharpWasserstein.Compat
public import SharpWasserstein.GaussianEntropyChain

@[expose] public section

/-! Preserved label marginals of genuine recursively generated Gaussian histories. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace SharpWasserstein

@[simp] theorem gaussianHistoryStepEquiv_symm_label {A : Type*} [MeasurableSpace A]
    (d n : ℕ) (z : GaussianHistory A d n × Position d) :
    ((gaussianHistoryStepEquiv A d n).symm z).1 = z.1.1 := rfl

/-- Appending transitions preserves the exact initial label law. -/
theorem gaussianHistoryLaw_map_labels {A : Type*} [MeasurableSpace A] {d : ℕ}
    (μ₀ : Measure (GaussianHistory A d 0)) [IsProbabilityMeasure μ₀]
    (a : (n : ℕ) → GaussianHistory A d n → Position d)
    (ha : ∀ n, Measurable (a n)) (v : ℕ → ℝ≥0) (n : ℕ) :
    (gaussianHistoryLaw μ₀ a ha v n).map Prod.fst = μ₀.map Prod.fst := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [gaussianHistoryLaw, Measure.map_map measurable_fst
      (gaussianHistoryStepEquiv A d n).symm.measurable]
    change ((gaussianHistoryLaw μ₀ a ha v n) ⊗ₘ gaussianVectorKernel (a n) (ha n) (v n)).map
      (Prod.fst ∘ Prod.fst) = _
    rw [← Measure.map_map measurable_fst measurable_fst]
    have he : ((gaussianHistoryLaw μ₀ a ha v n) ⊗ₘ gaussianVectorKernel (a n) (ha n) (v n)).map
        Prod.fst = gaussianHistoryLaw μ₀ a ha v n := Measure.fst_compProd _ _
    rw [he, ih]

/-- Put labels into the zero-length history without adding any randomness. -/
def gaussianInitialHistory {A : Type*} [MeasurableSpace A] (d : ℕ) (π : Measure A) :
    Measure (GaussianHistory A d 0) := π.map (fun z ↦ (z, fun i ↦ Fin.elim0 i))

instance gaussianInitialHistory_isProbability {A : Type*} [MeasurableSpace A]
    (d : ℕ) (π : Measure A) [IsProbabilityMeasure π] :
    IsProbabilityMeasure (gaussianInitialHistory d π) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

@[simp] theorem gaussianInitialHistory_map_labels {A : Type*} [MeasurableSpace A]
    (d : ℕ) (π : Measure A) : (gaussianInitialHistory d π).map Prod.fst = π := by
  rw [gaussianInitialHistory, Measure.map_map measurable_fst (by fun_prop)]
  exact Measure.map_id

/-- The label moment is integrable at every step, and retains its initial
expectation. No moment of the generated trajectory is needed for this fact. -/
theorem gaussianHistory_label_integrable {A : Type*} [MeasurableSpace A] {d : ℕ}
    (π : Measure A) [IsProbabilityMeasure π]
    (a : (n : ℕ) → GaussianHistory A d n → Position d)
    (ha : ∀ n, Measurable (a n)) (v : ℕ → ℝ≥0) (n : ℕ)
    {F : A → ℝ} (hF : Measurable F) (hi : Integrable F π) :
    Integrable (fun x ↦ F x.1) (gaussianHistoryLaw (gaussianInitialHistory d π) a ha v n) := by
  have hm : (gaussianHistoryLaw (gaussianInitialHistory d π) a ha v n).map Prod.fst = π := by
    rw [gaussianHistoryLaw_map_labels, gaussianInitialHistory_map_labels]
  rw [← hm] at hi
  exact (integrable_map_measure hF.aestronglyMeasurable measurable_fst.aemeasurable).mp hi

theorem gaussianHistory_label_integral {A : Type*} [MeasurableSpace A] {d : ℕ}
    (π : Measure A) [IsProbabilityMeasure π]
    (a : (n : ℕ) → GaussianHistory A d n → Position d)
    (ha : ∀ n, Measurable (a n)) (v : ℕ → ℝ≥0) (n : ℕ)
    {F : A → ℝ} (hF : Measurable F) :
    (∫ x, F x.1 ∂gaussianHistoryLaw (gaussianInitialHistory d π) a ha v n) = ∫ x, F x ∂π := by
  rw [← integral_map measurable_fst.aemeasurable hF.aestronglyMeasurable,
    gaussianHistoryLaw_map_labels, gaussianInitialHistory_map_labels]

end SharpWasserstein
