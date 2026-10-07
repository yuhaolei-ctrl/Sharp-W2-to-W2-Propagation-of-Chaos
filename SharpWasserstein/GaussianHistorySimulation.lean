module

public import SharpWasserstein.Compat
public import SharpWasserstein.GaussianEntropyChain

@[expose] public section

/-! Actual Gaussian innovations generate the iterated state-dependent Gaussian
transition measure. This supplies the probabilistic law identity used for Euler
schemes; the transition identity is proved from products and translation. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace SharpWasserstein

theorem gaussianVectorLaw_translate {d : ℕ} (a : Position d) (v : ℝ≥0) :
    (gaussianVectorLaw (0 : Position d) v).map (fun z => a + z) = gaussianVectorLaw a v := by
  unfold gaussianVectorLaw
  change (Measure.pi fun _ : Fin d => gaussianReal 0 v).map (fun z i => a i + z i) = _
  rw [Measure.pi_map_pi (fun i => (by fun_prop : Measurable (fun z : ℝ => a i + z)).aemeasurable)]
  simp only [gaussianReal_map_const_add, zero_add]

/-- Adding a state-dependent mean to an independent centered vector realizes
exactly the corresponding Gaussian transition kernel. -/
theorem gaussianVectorKernel_realization {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] {d : ℕ}
    (a : A → Position d) (ha : Measurable a) (v : ℝ≥0) :
    (μ.prod (gaussianVectorLaw (0 : Position d) v)).map
      (fun p => (p.1, a p.1 + p.2)) = μ ⊗ₘ gaussianVectorKernel a ha v := by
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs, Measure.prod_apply (hs.preimage (by fun_prop)),
    Measure.compProd_apply hs]
  apply lintegral_congr
  intro x
  have h := congrArg (fun ν : Measure (Position d) => ν (Prod.mk x ⁻¹' s))
    (gaussianVectorLaw_translate (a x) v)
  rw [Measure.map_apply (by fun_prop) (hs.preimage measurable_prodMk_left)] at h
  exact h

/-- The genuine product law of a finite collection of centered innovations. -/
def gaussianInnovationLaw (d : ℕ) (v : ℕ → ℝ≥0) (n : ℕ) : Measure (Configuration d n) :=
  Measure.pi fun i : Fin n => gaussianVectorLaw (0 : Position d) (v i)

instance gaussianInnovationLaw_probability (d : ℕ) (v : ℕ → ℝ≥0) (n : ℕ) :
    IsProbabilityMeasure (gaussianInnovationLaw d v n) := by
  unfold gaussianInnovationLaw
  infer_instance

theorem gaussianInnovationLaw_split (d : ℕ) (v : ℕ → ℝ≥0) (n : ℕ) :
    (gaussianInnovationLaw d v (n+1)).map (splitLastParticle d n) =
      (gaussianInnovationLaw d v n).prod (gaussianVectorLaw (0 : Position d) (v n)) := by
  have h := measurePreserving_piFinSuccAbove
    (fun i : Fin (n+1) => gaussianVectorLaw (0 : Position d) (v i)) (Fin.last n)
  have hp := (Measure.measurePreserving_swap.comp h).map_eq
  change (Measure.pi fun i : Fin (n+1) => gaussianVectorLaw (0 : Position d) (v i)).map
    (Prod.swap ∘ MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => Position d) (Fin.last n)) = _
  simpa only [gaussianInnovationLaw, Fin.succAbove_last, Fin.val_castSucc, Fin.val_last] using hp

/-- Deterministically append a state using a prescribed mean and actual noise. -/
def gaussianHistoryAppend {A : Type*} [MeasurableSpace A] {d n : ℕ}
    (a : GaussianHistory A d n → Position d)
    (p : GaussianHistory A d n × Position d) : GaussianHistory A d (n+1) :=
  (gaussianHistoryStepEquiv A d n).symm (p.1, a p.1 + p.2)

theorem gaussianHistoryAppend_measurable {A : Type*} [MeasurableSpace A] {d n : ℕ}
    (a : GaussianHistory A d n → Position d) (ha : Measurable a) :
    Measurable (gaussianHistoryAppend a) := by
  exact (gaussianHistoryStepEquiv A d n).symm.measurable.comp (measurable_fst.prodMk (ha.comp measurable_fst |>.add measurable_snd))

/-- The recursive simulator uses only the initial label and independent innovations. -/
def gaussianHistorySimulator {A : Type*} [MeasurableSpace A] {d : ℕ}
    (a : (n : ℕ) → GaussianHistory A d n → Position d) :
    (n : ℕ) → GaussianHistory A d 0 × Configuration d n → GaussianHistory A d n
  | 0, p => p.1
  | n+1, p => gaussianHistoryAppend (a n)
      (gaussianHistorySimulator a n (p.1, (splitLastParticle d n p.2).1),
        (splitLastParticle d n p.2).2)

theorem gaussianHistorySimulator_measurable {A : Type*} [MeasurableSpace A] {d : ℕ}
    (a : (n : ℕ) → GaussianHistory A d n → Position d) (ha : ∀ n, Measurable (a n))
    (n : ℕ) : Measurable (gaussianHistorySimulator a n) := by
  induction n with
  | zero => exact measurable_fst
  | succ n ih =>
    change Measurable (fun p : GaussianHistory A d 0 × Configuration d (n+1) => gaussianHistoryAppend (a n)
      (gaussianHistorySimulator a n (p.1, (splitLastParticle d n p.2).1),
        (splitLastParticle d n p.2).2))
    exact (gaussianHistoryAppend_measurable (a n) (ha n)).comp
      ((ih.comp (measurable_fst.prodMk ((splitLastParticle d n).measurable.comp measurable_snd |>.fst))).prodMk
        ((splitLastParticle d n).measurable.comp measurable_snd |>.snd))

/-- The simulator's law is the iterated Gaussian transition law, with no
conditional-distribution assumption. -/
theorem gaussianHistorySimulator_hasLaw {A : Type*} [MeasurableSpace A] {d : ℕ}
    (μ₀ : Measure (GaussianHistory A d 0)) [IsProbabilityMeasure μ₀]
    (a : (n : ℕ) → GaussianHistory A d n → Position d) (ha : ∀ n, Measurable (a n))
    (v : ℕ → ℝ≥0) (n : ℕ) :
    HasLaw (gaussianHistorySimulator a n) (gaussianHistoryLaw μ₀ a ha v n)
      (μ₀.prod (gaussianInnovationLaw d v n)) := by
  induction n with
  | zero => exact (measurePreserving_fst (μ := μ₀) (ν := gaussianInnovationLaw d v 0)).hasLaw
  | succ n ih =>
    have hs : MeasurePreserving (splitLastParticle d n) (gaussianInnovationLaw d v (n+1))
        ((gaussianInnovationLaw d v n).prod (gaussianVectorLaw (0 : Position d) (v n))) :=
      ⟨(splitLastParticle d n).measurable, gaussianInnovationLaw_split d v n⟩
    have h₁ := (MeasurePreserving.symm MeasurableEquiv.prodAssoc
      (measurePreserving_prodAssoc μ₀ (gaussianInnovationLaw d v n)
        (gaussianVectorLaw (0 : Position d) (v n)))).comp ((MeasurePreserving.id μ₀).prod hs)
    have h₂ := (ih.measurePreserving (gaussianHistorySimulator_measurable a ha n)).prod
      (MeasurePreserving.id (gaussianVectorLaw (0 : Position d) (v n)))
    have h₃ : MeasurePreserving (gaussianHistoryAppend (a n))
        ((gaussianHistoryLaw μ₀ a ha v n).prod (gaussianVectorLaw (0 : Position d) (v n)))
        (gaussianHistoryLaw μ₀ a ha v (n+1)) := by
      refine ⟨gaussianHistoryAppend_measurable (a n) (ha n), ?_⟩
      change Measure.map ((gaussianHistoryStepEquiv A d n).symm ∘
        (fun p : GaussianHistory A d n × Position d => (p.1, a n p.1 + p.2))) _ = _
      rw [← Measure.map_map (gaussianHistoryStepEquiv A d n).symm.measurable (by fun_prop),
        gaussianVectorKernel_realization]
      rfl
    exact (h₃.comp (h₂.comp h₁)).hasLaw

end SharpWasserstein
