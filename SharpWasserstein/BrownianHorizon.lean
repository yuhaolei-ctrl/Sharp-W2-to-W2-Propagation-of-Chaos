import SharpWasserstein.ConfigurationBrownian
import SharpWasserstein.FlowCausality
import SharpWasserstein.BrownianParticle

/-! Restriction consistency of the actual Brownian laws and particle flows.
The selected finite-horizon solutions therefore define a single evolution. -/

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace SharpWasserstein

theorem BoundedFlow.restrictPath_measurable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {S T : ℝ} (hST : S ≤ T) :
    Measurable (restrictPath (E := E) hST) := by
  apply (ContinuousMap.measurable_iff_eval _).mpr
  intro t
  exact (by fun_prop : Continuous (fun w : C(Icc 0 T,E) =>
    w ⟨t,t.property.1,t.property.2.trans hST⟩)).measurable

namespace BrownianNoise

theorem scalarLaw_restrict {S T : ℝ} (hST : S ≤ T) :
    MeasurePreserving (BoundedFlow.restrictPath (E := ℝ) hST) (scalarLaw T) (scalarLaw S) := by
  refine ⟨BoundedFlow.restrictPath_measurable hST, ?_⟩
  rw [scalarLaw,Measure.map_map (BoundedFlow.restrictPath_measurable hST) scalarPath_measurable]
  rfl

theorem coordinateLaw_restrict (d : ℕ) {S T : ℝ} (hST : S ≤ T) :
    MeasurePreserving (fun w : Fin d → C(Icc 0 T,ℝ) =>
      fun a => BoundedFlow.restrictPath hST (w a)) (coordinateLaw d T) (coordinateLaw d S) :=
  measurePreserving_pi (fun _ => scalarLaw T) (fun _ => scalarLaw S)
    (fun _ => scalarLaw_restrict hST)

theorem pathLabels_restrict (d N : ℕ) {S T : ℝ} (hST : S ≤ T) :
    MeasurePreserving (fun w : Fin N → Fin d → C(Icc 0 T,ℝ) =>
      fun i a => BoundedFlow.restrictPath hST (w i a)) (pathLabels d N T) (pathLabels d N S) :=
  measurePreserving_pi (fun _ => coordinateLaw d T) (fun _ => coordinateLaw d S)
    (fun _ => coordinateLaw_restrict d hST)

theorem configurationLaw_restrict (d N : ℕ) {S T : ℝ} (hST : S ≤ T) :
    MeasurePreserving (BoundedFlow.restrictPath (E := Configuration d N) hST)
      (configurationLaw d N T) (configurationLaw d N S) := by
  refine ⟨BoundedFlow.restrictPath_measurable hST, ?_⟩
  rw [configurationLaw,Measure.map_map (BoundedFlow.restrictPath_measurable hST)
    configurationPath_measurable]
  have he : BoundedFlow.restrictPath (E := Configuration d N) hST ∘ configurationPath =
      configurationPath ∘ (fun w : Fin N → Fin d → C(Icc 0 T,ℝ) =>
        fun i a => BoundedFlow.restrictPath hST (w i a)) := rfl
  rw [he,← Measure.map_map configurationPath_measurable (pathLabels_restrict d N hST).measurable,
    (pathLabels_restrict d N hST).map_eq]
  rfl

end BrownianNoise

namespace BrownianParticle

variable {d N : ℕ} {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
  (hN : 0 < N) (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
  (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)

theorem solution_restrict {S T : ℝ} (hS : 0 ≤ S) (hST : S ≤ T)
    (x : Configuration d N) (w : C(Icc 0 T, Configuration d N))
    {t : ℝ} (ht : t ∈ Icc 0 S) :
    ParticleFlow.solution hN hb hbound hM hL₁ hL₂ hS x (BoundedFlow.restrictPath hST w) t =
      ParticleFlow.solution hN hb hbound hM hL₁ hL₂ (hS.trans hST) x w t :=
  BoundedFlow.flow_restrict _ _ _ hS hST x w ht

theorem law_restrict {S T : ℝ} (hS : 0 ≤ S) (hST : S ≤ T)
    (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    {t : ℝ} (ht : t ∈ Icc 0 S) :
    law hN hb hbound hM hL₁ hL₂ hS μ t =
      law hN hb hbound hM hL₁ hL₂ (hS.trans hST) μ t := by
  let R := Prod.map (id : Configuration d N → Configuration d N)
    (BoundedFlow.restrictPath (E := Configuration d N) hST)
  have hR : MeasurePreserving R
      (μ.prod (BrownianNoise.configurationLaw d N T))
      (μ.prod (BrownianNoise.configurationLaw d N S)) :=
    (MeasurePreserving.id μ).prod (BrownianNoise.configurationLaw_restrict d N hST)
  unfold law ParticleFlow.law randomMapLaw
  rw [← hR.map_eq,Measure.map_map
    (ParticleFlow.solution_measurable hN hb hbound hM hL₁ hL₂ hS ht) hR.measurable]
  congr 1
  funext p
  exact solution_restrict hN hb hbound hM hL₁ hL₂ hS hST p.1 p.2 ht

theorem law_horizon_independent {S T : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T)
    (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    {t : ℝ} (htS : t ∈ Icc 0 S) (htT : t ∈ Icc 0 T) :
    law hN hb hbound hM hL₁ hL₂ hS μ t = law hN hb hbound hM hL₁ hL₂ hT μ t := by
  rcases le_total S T with hST | hTS
  · exact law_restrict hN hb hbound hM hL₁ hL₂ hS hST μ htS
  · exact (law_restrict hN hb hbound hM hL₁ hL₂ hT hTS μ htT).symm

/-- One law at every nonnegative time, constructed without a consistency axiom. -/
def globalLaw (μ : Measure (Configuration d N)) (t : ℝ) : Measure (Configuration d N) :=
  law hN hb hbound hM hL₁ hL₂ (le_max_right t 0) μ t

theorem globalLaw_eq {T t : ℝ} (hT : 0 ≤ T)
    (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ] (ht : t ∈ Icc 0 T) :
    globalLaw hN hb hbound hM hL₁ hL₂ μ t = law hN hb hbound hM hL₁ hL₂ hT μ t :=
  law_horizon_independent hN hb hbound hM hL₁ hL₂ (le_max_right t 0) hT μ
    ⟨ht.1,le_max_left t 0⟩ ht

theorem globalLaw_initial (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ] :
    globalLaw hN hb hbound hM hL₁ hL₂ μ 0 = μ :=
  law_initial hN hb hbound hM hL₁ hL₂ (le_max_right 0 0) μ

theorem globalLaw_probability (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    {t : ℝ} (ht : 0 ≤ t) : IsProbabilityMeasure (globalLaw hN hb hbound hM hL₁ hL₂ μ t) :=
  law_probability hN hb hbound hM hL₁ hL₂ (le_max_right t 0) μ ⟨ht,le_max_left t 0⟩

theorem globalLaw_secondMoment (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    (hμ : HasSecondMoment μ) {t : ℝ} (ht : 0 ≤ t) :
    HasSecondMoment (globalLaw hN hb hbound hM hL₁ hL₂ μ t) :=
  law_secondMoment hN hb hbound hM hL₁ hL₂ (le_max_right t 0) μ hμ ⟨ht,le_max_left t 0⟩

theorem globalLaw_exchangeable (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    (hμ : Exchangeable μ) {t : ℝ} (ht : 0 ≤ t) :
    Exchangeable (globalLaw hN hb hbound hM hL₁ hL₂ μ t) :=
  law_exchangeable hN hb hbound hM hL₁ hL₂ (le_max_right t 0) μ hμ ⟨ht,le_max_left t 0⟩

end BrownianParticle
end SharpWasserstein
