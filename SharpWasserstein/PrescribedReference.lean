import SharpWasserstein.BrownianFlowWeak
import SharpWasserstein.BrownianDecoupledFlow
import SharpWasserstein.NonlinearDriftContinuity
import SharpWasserstein.WeakEvolutionContinuity

/-! Prescribed mean-field reference drifts, using the actual narrow continuity
of a supplied limit weak evolution. The constructed reference evolution is
proved to solve the linear equation with that prescribed drift. Identification
with the supplied tensor curve is a separate uniqueness step. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace SharpWasserstein

namespace WeakEvolution

theorem congr_nonnegDrift {d N : ℕ} {v w : ℝ → Configuration d N → Configuration d N}
    {P : ℝ → Measure (Configuration d N)} (h : WeakEvolution v P)
    (he : ∀ t, 0 ≤ t → v t = w t) : WeakEvolution w P where
  probability := h.probability
  secondMoment := h.secondMoment
  momentBound := h.momentBound
  testContinuous := h.testContinuous
  generatorIntegrable := by
    intro φ hφ t ht
    rw [← he t ht]
    exact h.generatorIntegrable φ hφ t ht
  timeIntegrable := by
    intro φ hφ t ht
    apply (intervalIntegrable_congr (f := fun s => ∫ x, generator (v s) φ x ∂P s) ?_).mp
      (h.timeIntegrable φ hφ t ht)
    intro s hs
    rw [uIoc_of_le ht] at hs
    dsimp only
    rw [he s hs.1.le]
  equation := by
    intro φ hφ t ht
    rw [h.equation φ hφ t ht]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht] at hs
    dsimp only
    rw [he s hs.1]

end WeakEvolution
namespace IsLimitEvolution
variable {d : ℕ} {b : Position d → Position d → Position d}
  {μ : ℝ → Measure (Position d)} (h : IsLimitEvolution b μ)

def probabilityCurve (t : ℝ) : ProbabilityMeasure (Position d) :=
  ⟨μ (max 0 t), h.1 _ (le_max_left _ _)⟩

/-- The supplied nonlinear limit curve is genuinely narrowly continuous,
with its initial law used at negative times. -/
theorem continuous_probabilityCurve : Continuous (probabilityCurve h) := by
  have hc := (ProbabilityMeasure.continuous_map (continuous_apply (0 : Fin 1))).comp
    (WeakEvolution.continuous_probabilityCurve h.2)
  convert hc using 1
  funext t
  apply Subtype.ext
  change μ (max 0 t) = (singletonLaw (μ (max 0 t))).map (fun x => x (0 : Fin 1))
  unfold singletonLaw
  rw [Measure.map_map (measurable_pi_apply (0 : Fin 1)) (by fun_prop)]
  simp only [Function.comp_def,Measure.map_id']

include h in
theorem initial_integrable_positionSq : Integrable positionSq (μ 0) := by
  have hi := (hasSecondMoment_iff_integrable (singletonLaw (μ 0))).mp (h.2.secondMoment 0 le_rfl)
  have hi' := (integrable_map_measure
    (measurable_productCost.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    (by fun_prop : Measurable (fun x : Position d => fun _ : Fin 1 => x)).aemeasurable).mp hi
  simpa only [Function.comp_def,productCost_eq_sum_positionSq,Pi.zero_apply,sub_zero,Fin.sum_univ_one,id_eq] using hi'

end IsLimitEvolution
namespace PrescribedReference

variable {d : ℕ} {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
  (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
  (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁)
  {μ : ℝ → Measure (Position d)} (hμ : IsLimitEvolution b μ)

def singleDrift (t : ℝ) (x : Position d) : Position d := nonlinearDrift b (μ (max 0 t)) x

include hb hbound hL₁ hμ in
theorem singleDrift_continuous : Continuous (Function.uncurry (singleDrift (b := b) (μ := μ))) :=
  nonlinearDrift_continuous_curve hb hbound hL₁ (IsLimitEvolution.continuous_probabilityCurve hμ)

include hbound hμ in
theorem singleDrift_bound : ∀ t x, ‖singleDrift (b := b) (μ := μ) t x‖ ≤ (⟨M,hM⟩ : ℝ≥0) := by
  intro t x
  letI := hμ.1 (max 0 t) (le_max_left _ _)
  exact nonlinearDrift_bound hbound (μ (max 0 t)) x

include hb hbound hμ in
theorem singleDrift_lipschitz : ∀ t, LipschitzWith (⟨L₁,hL₁⟩ : ℝ≥0) (singleDrift (b := b) (μ := μ) t) := by
  intro t
  letI := hμ.1 (max 0 t) (le_max_left _ _)
  exact nonlinearDrift_lipschitz hb hbound hL₁ (μ (max 0 t))

/-- A concrete linear reference evolution starting from any correlated P₂ law. -/
def law (N : ℕ) (P : Measure (Configuration d N)) : ℝ → Measure (Configuration d N) :=
  BrownianFlow.globalLaw
    (DecoupledFlow.liftDrift_continuous N (singleDrift_continuous hb hbound hL₁ hμ))
    (DecoupledFlow.liftDrift_bound N (singleDrift_bound hbound hM hμ))
    (DecoupledFlow.liftDrift_lipschitz N (singleDrift_lipschitz hb hbound hL₁ hμ)) P

theorem law_initial (N : ℕ) (P : Measure (Configuration d N)) [IsProbabilityMeasure P] :
    law hb hbound hM hL₁ hμ N P 0 = P := BrownianFlow.globalLaw_initial _ _ _ P

/-- The drift in the conclusion uses the original supplied μ_t at every
nonnegative time, without an extra continuity hypothesis on μ. -/
theorem law_weakEvolution (N : ℕ) (P : Measure (Configuration d N)) [IsProbabilityMeasure P]
    (hP : HasSecondMoment P) :
    WeakEvolution (fun t x i => nonlinearDrift b (μ t) (x i)) (law hb hbound hM hL₁ hμ N P) := by
  have h := BrownianFlow.globalLaw_weakEvolution
    (DecoupledFlow.liftDrift_continuous N (singleDrift_continuous hb hbound hL₁ hμ))
    (DecoupledFlow.liftDrift_bound N (singleDrift_bound hbound hM hμ))
    (DecoupledFlow.liftDrift_lipschitz N (singleDrift_lipschitz hb hbound hL₁ hμ)) P hP
  apply h.congr_nonnegDrift
  intro t ht
  funext x i
  change nonlinearDrift b (μ (max 0 t)) (x i) = nonlinearDrift b (μ t) (x i)
  rw [max_eq_right ht]

/-- The product initial reference produces a proved linear weak evolution. -/
theorem tensor_initial_weakEvolution (N : ℕ) :
    WeakEvolution (fun t x i => nonlinearDrift b (μ t) (x i))
      (law hb hbound hM hL₁ hμ N (tensorLaw (μ 0) N)) := by
  letI := hμ.1 0 le_rfl
  exact law_weakEvolution hb hbound hM hL₁ hμ N _
    (hasSecondMoment_tensorLaw (μ 0) (IsLimitEvolution.initial_integrable_positionSq hμ) N)


/-- The constructed reference is exactly the independent coordinate flow used
by the entropy-cost regularization, at each positive time. -/
theorem law_eq_decoupled (N : ℕ) (P : Measure (Configuration d N)) [IsProbabilityMeasure P]
    {t : ℝ} (ht : 0 < t) :
    law hb hbound hM hL₁ hμ N P t =
      DecoupledFlow.law (singleDrift_continuous hb hbound hL₁ hμ)
        (singleDrift_bound hbound hM hμ) (singleDrift_lipschitz hb hbound hL₁ hμ)
        ht.le P (BrownianNoise.positionLaw d t) t := by
  unfold law
  rw [BrownianFlow.globalLaw_eq _ _ _ ht.le P ⟨ht.le,le_rfl⟩]
  exact DecoupledFlow.brownian_flowLaw_eq _ _ _ ht P

/-- Product initial data remain the exact tensor of the constructed
one-particle reference law, not merely a law with matching marginals. -/
theorem law_tensor (N : ℕ) {t : ℝ} (ht : 0 < t) :
    law hb hbound hM hL₁ hμ N (tensorLaw (μ 0) N) t =
      tensorLaw (Measure.map
        (fun p : Position d × C(Icc 0 t, Position d) => BoundedFlow.flow
          (singleDrift_continuous hb hbound hL₁ hμ) (singleDrift_bound hbound hM hμ)
          (singleDrift_lipschitz hb hbound hL₁ hμ) ht.le p.1 p.2 t)
        ((μ 0).prod (BrownianNoise.positionLaw d t))) N := by
  letI := hμ.1 0 le_rfl
  rw [law_eq_decoupled hb hbound hM hL₁ hμ N _ ht]
  exact DecoupledFlow.law_tensor _ _ _ ht.le (μ 0) _ ⟨ht.le,le_rfl⟩

end PrescribedReference
end SharpWasserstein
