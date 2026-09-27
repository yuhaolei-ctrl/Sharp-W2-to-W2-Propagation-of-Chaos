import SharpWasserstein.BrownianEntropyFlow
import SharpWasserstein.GaussianBridgeBrownian

/-! # Entropy cost for the actually constructed Brownian flow
The finite Gaussian identity, deterministic meeting bridge, actual Brownian
Euler law identification, Euler convergence and KL lower semicontinuity are
composed here. No Girsanov or entropy-cost hypothesis is introduced.
-/
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped ENNReal NNReal Topology
namespace SharpWasserstein.BrownianEntropy
open GaussianBridge

variable {d N : ℕ} {T : ℝ} {v : ℝ → Configuration d N → Configuration d N} {M K L : ℝ≥0}

/-- First Gaussian observation is exactly the independently initialized actual
Brownian Euler endpoint law from the first coupling label. -/
theorem ordinaryObservation_eq_labelEulerLaw (γ : Measure (Labels (N*d))) [IsProbabilityMeasure γ]
    (hv : ∀ t, Measurable (v t)) (hT : 0 < T) (n : ℕ) :
    ordinaryObservation γ (flattenedDrift v) (flattenedDrift_measurable v hv)
      (gridStep T hT n) (n+1) (endpointObservation (d := d) (N := N) (n+1))
      (endpointObservation_measurable _) =
        labelEulerLaw γ initialX (measurable_initialX d N) v hv hT.le n := by
  apply Subtype.ext
  exact ordinaryLaw_endpoint_eq hT.le γ v hv n

/-- The shifted Gaussian comparison has exactly the uncontrolled Brownian
Euler endpoint law from the second label, by terminal conjugacy. -/
theorem shiftedObservation_eq_labelEulerLaw (γ : Measure (Labels (N*d))) [IsProbabilityMeasure γ]
    (hv : ∀ t, Measurable (v t)) (hT : 0 < T) (n : ℕ) :
    shiftedObservation γ (flattenedDrift v) (flattenedDrift_measurable v hv) T
      (gridStep T hT n) (n+1) (endpointObservation (d := d) (N := N) (n+1))
      (endpointObservation_measurable _) =
        labelEulerLaw γ initialY (measurable_initialY d N) v hv hT.le n := by
  apply Subtype.ext
  exact shiftedLaw_endpoint_eq hT γ v hv n

/-- The entropy cost for arbitrary retained initial labels, with expectation
under their original joint law and the exact dimension-free coefficient. -/
theorem label_flow_entropy_le (γ : Measure (Labels (N*d))) [IsProbabilityMeasure γ]
    (hv : Continuous (Function.uncurry v)) (hb : ∀ t x, ‖v t x‖ ≤ M)
    (hl : ∀ t, LipschitzWith K (v t))
    (he : ∀ t, LipschitzWith L (euclideanDrift (flattenedDrift v) t))
    (hT : 0 < T) (hi : Integrable displacementSq γ) :
    klDiv (labelFlowLaw γ initialX (measurable_initialX d N) hv hb hl hT.le : Measure (Configuration d N))
      (labelFlowLaw γ initialY (measurable_initialY d N) hv hb hl hT.le : Measure (Configuration d N)) ≤
      ENNReal.ofReal (RegularizationRates.bridgeCost L T * ∫ z, displacementSq z ∂γ) := by
  let hm : ∀ t, Measurable (v t) := fun t ↦ (hl t).continuous.measurable
  apply limit_observation_entropy_le γ (flattenedDrift_measurable v hm) hT he hi
    (fun n ↦ endpointObservation (d := d) (N := N) (n+1)) (fun _ ↦ endpointObservation_measurable _)
  · have h := labelEulerLaw_tendsto γ initialX (measurable_initialX d N) hv hb hl hT
    exact h.congr' (Filter.Eventually.of_forall fun n ↦
      (ordinaryObservation_eq_labelEulerLaw (d := d) (N := N) γ hm hT n).symm)
  · have h := labelEulerLaw_tendsto γ initialY (measurable_initialY d N) hv hb hl hT
    exact h.congr' (Filter.Eventually.of_forall fun n ↦
      (shiftedObservation_eq_labelEulerLaw (d := d) (N := N) γ hm hT n).symm)

/-- Flattened labels retain precisely the first original marginal. -/
theorem flattenedCoupling_map_initialX {μ ν : Measure (Configuration d N)}
    {γ : Measure (Configuration d N × Configuration d N)} (hγ : IsCoupling μ ν γ) :
    (flattenedCoupling γ).map (initialX (d := d) (N := N)) = μ := by
  rw [flattenedCoupling, Measure.map_map (measurable_initialX d N)
    ((configurationFlatten d N).prodCongr (configurationFlatten d N)).measurable]
  have heq : initialX ∘ ((configurationFlatten d N).prodCongr (configurationFlatten d N)) =
      (Prod.fst : Configuration d N × Configuration d N → Configuration d N) := by
    funext z
    exact (configurationFlatten d N).symm_apply_apply z.1
  rw [heq]
  exact hγ.2.1

theorem flattenedCoupling_map_initialY {μ ν : Measure (Configuration d N)}
    {γ : Measure (Configuration d N × Configuration d N)} (hγ : IsCoupling μ ν γ) :
    (flattenedCoupling γ).map (initialY (d := d) (N := N)) = ν := by
  rw [flattenedCoupling, Measure.map_map (measurable_initialY d N)
    ((configurationFlatten d N).prodCongr (configurationFlatten d N)).measurable]
  have heq : initialY ∘ ((configurationFlatten d N).prodCongr (configurationFlatten d N)) =
      (Prod.snd : Configuration d N × Configuration d N → Configuration d N) := by
    funext z
    exact (configurationFlatten d N).symm_apply_apply z.2
  rw [heq]
  exact hγ.2.2

/-- Actual continuous-time Brownian flow entropy-cost bound for every P₂
coupling. The coefficient uses the Euclidean Lipschitz constant, independent
of particle number. The sup-norm Lipschitz condition is solely a flow-existence
input and does not appear in the entropy-cost coefficient. -/
theorem flow_entropy_le_coupling (μ ν : Measure (Configuration d N))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {γ : Measure (Configuration d N × Configuration d N)} (hγ : IsCoupling μ ν γ)
    (hμ : HasSecondMoment μ) (hν : HasSecondMoment ν)
    (hv : Continuous (Function.uncurry v)) (hb : ∀ t x, ‖v t x‖ ≤ M)
    (hl : ∀ t, LipschitzWith K (v t))
    (he : ∀ t, LipschitzWith L (euclideanDrift (flattenedDrift v) t)) (hT : 0 < T) :
    klDiv (flowLaw μ hv hb hl hT.le : Measure (Configuration d N))
      (flowLaw ν hv hb hl hT.le : Measure (Configuration d N)) ≤
      ENNReal.ofReal (RegularizationRates.bridgeCost L T * ∫ z, productCost z.1 z.2 ∂γ) := by
  letI := hγ.1
  have h := label_flow_entropy_le (flattenedCoupling γ) hv hb hl he hT
    (flattenedCoupling_displacement_integrable hγ hμ hν)
  have hx : (labelFlowLaw (flattenedCoupling γ) initialX (measurable_initialX d N) hv hb hl hT.le :
      Measure (Configuration d N)) = flowLaw μ hv hb hl hT.le := by
    rw [labelFlowLaw_eq_flowLaw_map]
    change (((flattenedCoupling γ).map initialX).prod (BrownianNoise.configurationLaw d N T)).map
      (fun p ↦ BoundedFlow.flow hv hb hl hT.le p.1 p.2 T) = _
    rw [flattenedCoupling_map_initialX hγ]
    rfl
  have hy : (labelFlowLaw (flattenedCoupling γ) initialY (measurable_initialY d N) hv hb hl hT.le :
      Measure (Configuration d N)) = flowLaw ν hv hb hl hT.le := by
    rw [labelFlowLaw_eq_flowLaw_map]
    change (((flattenedCoupling γ).map initialY).prod (BrownianNoise.configurationLaw d N T)).map
      (fun p ↦ BoundedFlow.flow hv hb hl hT.le p.1 p.2 T) = _
    rw [flattenedCoupling_map_initialY hγ]
    rfl
  rw [hx, hy, flattenedCoupling_displacement_integral] at h
  exact h

end SharpWasserstein.BrownianEntropy
