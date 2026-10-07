module

public import SharpWasserstein.Compat
public import SharpWasserstein.PropagatedSourceEquationDistribution

@[expose] public section

/-! Exact identification of the measure carrying the propagated source with
the already constructed Brownian flow law in Euclidean coordinates. -/
noncomputable section
open Set MeasureTheory
open scoped NNReal
namespace SharpWasserstein.PropagatedSourceEquation.Brownian
open WeightedTangent
variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  {b : Configuration d N → Configuration d N} {M K M' K' : ℝ≥0}
  (hv : Continuous (Function.uncurry (fun _ : ℝ => b)))
  (hb : ∀ _ : ℝ, ∀ x, ‖b x‖ ≤ M) (hl : ∀ _ : ℝ, LipschitzWith K b)
  (hv' : Continuous (Function.uncurry (fun _ : ℝ => equivDrift (configurationEuclidean d N) b)))
  (hb' : ∀ _ : ℝ, ∀ y, ‖equivDrift (configurationEuclidean d N) b y‖ ≤ M')
  (hl' : ∀ _ : ℝ, LipschitzWith K' (equivDrift (configurationEuclidean d N) b))
  {T : ℝ} (hT : 0 ≤ T)

/-- The genuine random map carrying the source is precisely the previously
constructed Brownian flow, after the fixed Euclidean coordinate map. -/
theorem lawAt_eq_map_flowLaw (μ : Measure (Configuration d N)) [IsFiniteMeasure μ]
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) t =
      (BrownianFlow.law hv hb hl hT μ t).map (configurationEuclidean d N) := by
  let L := configurationEuclidean d N
  have hL : Measurable L := L.continuous.measurable
  have hP := (equivPath_continuous (T := T) L).measurable
  simp only [lawAt,projIcc_of_mem _ ht,euclideanBrownianPathLaw]
  rw [Measure.map_prod_map μ _ hL hP,
    Measure.map_map (PropagatedFlux.Flow.endpoint_measurable hv' hb' hl' hT ht) (hL.prodMap hP)]
  rw [BrownianFlow.law,Measure.map_map hL (BoundedFlow.flow_continuous hv hb hl hT ht).measurable]
  congr 1
  funext p
  exact flow_equiv L hv hb hl hv' hb' hl' hT p.1 p.2 ht

/-- Horizon-consistent actual Brownian law identification. -/
theorem lawAt_eq_map_globalLaw (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) t =
      (BrownianFlow.globalLaw hv hb hl μ t).map (configurationEuclidean d N) := by
  rw [BrownianFlow.globalLaw_eq hv hb hl hT μ ht]
  exact lawAt_eq_map_flowLaw hv hb hl hv' hb' hl' hT μ ht

end SharpWasserstein.PropagatedSourceEquation.Brownian
