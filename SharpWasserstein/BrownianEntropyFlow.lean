module

public import SharpWasserstein.Compat
public import SharpWasserstein.EulerBrownianLaw
public import SharpWasserstein.GaussianBridgeLimit

@[expose] public section

/-! Actual bounded continuous-drift Brownian endpoint laws and Euler limits.
These definitions use the constructed Brownian source and integral-equation
flow, not assumed transition semigroups or entropy bounds. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace SharpWasserstein.BrownianEntropy

variable {d N : ℕ} {T : ℝ} {v : ℝ → Configuration d N → Configuration d N} {M K : ℝ≥0}

def inputLaw {A : Type*} [MeasurableSpace A] (γ : Measure A) [IsProbabilityMeasure γ] :
    ProbabilityMeasure (A × C(Icc 0 T, Configuration d N)) :=
  ⟨γ.prod (BrownianNoise.configurationLaw d N T), inferInstance⟩

def labelEulerLaw {A : Type*} [MeasurableSpace A]
    (γ : Measure A) [IsProbabilityMeasure γ] (initial : A → Configuration d N) (hi : Measurable initial)
    (v : ℝ → Configuration d N → Configuration d N) (hv : ∀ t, Measurable (v t))
    (hT : 0 ≤ T) (n : ℕ) : ProbabilityMeasure (Configuration d N) :=
  (inputLaw (d := d) (N := N) (T := T) γ).map
    (Euler.endpointMap hT v n ∘ fun a => ((initial ∘ Prod.fst) a, a.2))

def labelFlowLaw {A : Type*} [MeasurableSpace A]
    (γ : Measure A) [IsProbabilityMeasure γ] (initial : A → Configuration d N) (hi : Measurable initial)
    (hv : Continuous (Function.uncurry v)) (hb : ∀ t x, ‖v t x‖ ≤ M)
    (hl : ∀ t, LipschitzWith K (v t)) (hT : 0 ≤ T) : ProbabilityMeasure (Configuration d N) :=
  (inputLaw (d := d) (N := N) (T := T) γ).map
    ((fun p : Configuration d N × C(Icc 0 T, Configuration d N) => BoundedFlow.flow hv hb hl hT p.1 p.2 T) ∘
      fun a => ((initial ∘ Prod.fst) a, a.2))

/-- Independent initial law and actual `sqrt(2)` Brownian source pushed through
the constructed continuous additive flow at the terminal time. -/
def flowLaw (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    (hv : Continuous (Function.uncurry v)) (hb : ∀ t x, ‖v t x‖ ≤ M)
    (hl : ∀ t, LipschitzWith K (v t)) (hT : 0 ≤ T) : ProbabilityMeasure (Configuration d N) :=
  labelFlowLaw μ id measurable_id hv hb hl hT

/-- Pointwise Euler convergence gives actual narrow endpoint convergence for
any independent initial labels, without a uniform bound on the labels. -/
theorem labelEulerLaw_tendsto {A : Type*} [MeasurableSpace A]
    (γ : Measure A) [IsProbabilityMeasure γ] (initial : A → Configuration d N) (hi : Measurable initial)
    (hv : Continuous (Function.uncurry v)) (hb : ∀ t x, ‖v t x‖ ≤ M)
    (hl : ∀ t, LipschitzWith K (v t)) (hT : 0 < T) :
    Tendsto (fun n ↦ labelEulerLaw γ initial hi v (fun t ↦ (hl t).continuous.measurable) hT.le n)
      atTop (𝓝 (labelFlowLaw γ initial hi hv hb hl hT.le)) := by
  apply probabilityMeasure_map_tendsto (inputLaw (d := d) (N := N) (T := T) γ)
    (fun n ↦ (Euler.endpointMap_measurable hT.le (fun t ↦ (hl t).continuous.measurable) n).comp
      ((hi.comp measurable_fst).prodMk measurable_snd))
    ((BoundedFlow.flow_continuous hv hb hl hT.le ⟨hT.le, le_rfl⟩).measurable.comp
      ((hi.comp measurable_fst).prodMk measurable_snd))
  exact Filter.Eventually.of_forall fun p : A × C(Icc 0 T, Configuration d N) ↦ Euler.trajectory_endpoint_tendsto
    (BoundedFlow.flow_trajectory hv hb hl hT.le (initial p.1) p.2) hl hT

/-- The endpoint distribution depends on the actual initial marginal only. -/
theorem labelFlowLaw_eq_flowLaw_map {A : Type*} [MeasurableSpace A]
    (γ : Measure A) [IsProbabilityMeasure γ] (initial : A → Configuration d N) (hi : Measurable initial)
    (hv : Continuous (Function.uncurry v)) (hb : ∀ t x, ‖v t x‖ ≤ M)
    (hl : ∀ t, LipschitzWith K (v t)) (hT : 0 ≤ T) :
    labelFlowLaw γ initial hi hv hb hl hT =
      @flowLaw d N T v M K (γ.map initial) (Measure.isProbabilityMeasure_map hi.aemeasurable) hv hb hl hT := by
  apply Subtype.ext
  change ((γ.prod (BrownianNoise.configurationLaw d N T)).map
    (fun p ↦ BoundedFlow.flow hv hb hl hT (initial p.1) p.2 T)) =
    (((γ.map initial).prod (BrownianNoise.configurationLaw d N T)).map
    (fun p ↦ BoundedFlow.flow hv hb hl hT p.1 p.2 T))
  have hp : (γ.prod (BrownianNoise.configurationLaw d N T)).map (Prod.map initial id) =
      (γ.map initial).prod (BrownianNoise.configurationLaw d N T) := by
    simpa using (Measure.map_prod_map γ (BrownianNoise.configurationLaw d N T) hi measurable_id).symm
  rw [← hp, Measure.map_map (BoundedFlow.flow_continuous hv hb hl hT ⟨hT, le_rfl⟩).measurable
    (hi.prodMap measurable_id)]
  rfl

end SharpWasserstein.BrownianEntropy
