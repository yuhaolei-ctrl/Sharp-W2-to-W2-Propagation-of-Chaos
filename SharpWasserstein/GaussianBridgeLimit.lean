module

public import SharpWasserstein.Compat
public import SharpWasserstein.GaussianBridgeCoupling
public import SharpWasserstein.GaussianBridgeRate
public import SharpWasserstein.EntropyNarrow

@[expose] public section

/-! Passage from the proved finite Gaussian bridge bound to limits of the
actual observed history laws. Convergence hypotheses are explicit; Brownian
Euler identification and diffusion convergence are supplied by other modules. -/
noncomputable section
open MeasureTheory InformationTheory Filter
open scoped ENNReal NNReal Topology
namespace SharpWasserstein

/-- A converging sequence of actual entropy costs passes through simultaneous
narrow limits of both laws. -/
theorem klDiv_le_of_narrow_converging_cost {E : Type*} [MeasurableSpace E]
    [TopologicalSpace E] [BorelSpace E] [NormalSpace E]
    {ι : Type*} {F : Filter ι} [NeBot F]
    (μs νs : ι → ProbabilityMeasure E) (μ ν : ProbabilityMeasure E)
    [((μ : Measure E) + (ν : Measure E)).WeaklyRegular]
    (hμ : Tendsto μs F (𝓝 μ)) (hν : Tendsto νs F (𝓝 ν))
    {cost : ι → ℝ} {C : ℝ} (hcost : Tendsto cost F (𝓝 C))
    (hbound : ∀ᶠ n in F, klDiv (μs n : Measure E) (νs n : Measure E) ≤ ENNReal.ofReal (cost n)) :
    klDiv (μ : Measure E) (ν : Measure E) ≤ ENNReal.ofReal C := by
  calc
    _ ≤ liminf (fun n ↦ klDiv (μs n : Measure E) (νs n : Measure E)) F :=
      klDiv_le_liminf_of_narrow μs νs μ ν hμ hν
    _ ≤ liminf (fun n ↦ ENNReal.ofReal (cost n)) F := liminf_le_liminf hbound
    _ = _ := (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hcost).liminf_eq

namespace GaussianBridge

/-- Equal positive time mesh as an actual nonnegative Gaussian variance parameter. -/
def gridStep (T : ℝ) (hT : 0 < T) (n : ℕ) : ℝ≥0 := ⟨T/(n+1), by positivity⟩

theorem gridStep_ne_zero {T : ℝ} (hT : 0 < T) (n : ℕ) : gridStep T hT n ≠ 0 := by
  apply ne_of_gt
  change 0 < T/(n+1)
  positivity

theorem gridStep_terminal {T : ℝ} (hT : 0 < T) (n : ℕ) :
    ((n+1 : ℕ) : ℝ) * gridStep T hT n = T := by
  change ((n+1 : ℕ) : ℝ) * (T/(n+1)) = T
  push_cast
  field_simp

/-- Observed ordinary history as a probability law. -/
def ordinaryObservation {E : Type*} [MeasurableSpace E] {d : ℕ}
    (γ : Measure (Labels d)) [IsProbabilityMeasure γ]
    (v : ℝ → Position d → Position d) (hv : ∀ t, Measurable (v t))
    (δ : ℝ≥0) (n : ℕ) (f : History d n → E) (hf : Measurable f) : ProbabilityMeasure E :=
  ⟨(ordinaryLaw γ v hv δ n).map f, by
    haveI : IsProbabilityMeasure (ordinaryLaw γ v hv δ n) := inferInstanceAs
      (IsProbabilityMeasure (gaussianHistoryLaw _ _ _ _ _))
    exact Measure.isProbabilityMeasure_map hf.aemeasurable⟩

def shiftedObservation {E : Type*} [MeasurableSpace E] {d : ℕ}
    (γ : Measure (Labels d)) [IsProbabilityMeasure γ]
    (v : ℝ → Position d → Position d) (hv : ∀ t, Measurable (v t))
    (T : ℝ) (δ : ℝ≥0) (n : ℕ) (f : History d n → E) (hf : Measurable f) : ProbabilityMeasure E :=
  ⟨(shiftedLaw γ v hv T δ n).map f, by
    haveI : IsProbabilityMeasure (shiftedLaw γ v hv T δ n) := inferInstanceAs
      (IsProbabilityMeasure (gaussianHistoryLaw _ _ _ _ _))
    exact Measure.isProbabilityMeasure_map hf.aemeasurable⟩

/-- Limit entropy-cost bound from actual finite Gaussian history observations.
The only remaining analytic input is their narrow convergence to the named
endpoint laws; no entropy conclusion is among the premises. -/
theorem limit_observation_entropy_le {E : Type*} [MeasurableSpace E]
    [TopologicalSpace E] [BorelSpace E] [NormalSpace E] {d : ℕ}
    (γ : Measure (Labels d)) [IsProbabilityMeasure γ]
    {v : ℝ → Position d → Position d} (hv : ∀ t, Measurable (v t))
    {T : ℝ} (hT : 0 < T) {K : ℝ≥0}
    (hl : ∀ t, LipschitzWith K (euclideanDrift v t)) (hi : Integrable displacementSq γ)
    (f : (n : ℕ) → History d (n+1) → E) (hf : ∀ n, Measurable (f n))
    (μ ν : ProbabilityMeasure E) [((μ : Measure E) + (ν : Measure E)).WeaklyRegular]
    (hμ : Tendsto (fun n ↦ ordinaryObservation γ v hv (gridStep T hT n) (n+1) (f n) (hf n))
      atTop (𝓝 μ))
    (hν : Tendsto (fun n ↦ shiftedObservation γ v hv T (gridStep T hT n) (n+1) (f n) (hf n))
      atTop (𝓝 ν)) :
    klDiv (μ : Measure E) (ν : Measure E) ≤
      ENNReal.ofReal (RegularizationRates.bridgeCost K T * ∫ z, displacementSq z ∂γ) := by
  apply klDiv_le_of_narrow_converging_cost _ _ μ ν hμ hν
    ((gridCost_tendsto K hT.ne').mul_const (∫ z, displacementSq z ∂γ))
  refine Filter.Eventually.of_forall fun n ↦ ?_
  have hb := observation_entropy_le γ hv (gridStep_ne_zero hT n) hl hT hi (n+1)
    (gridStep_terminal hT n).le (f n) (hf n)
  exact hb

end GaussianBridge
end SharpWasserstein
