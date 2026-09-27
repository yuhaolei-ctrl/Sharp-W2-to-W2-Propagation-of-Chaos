import SharpWasserstein.RoughCommonLabelLift
import SharpWasserstein.RoughEulerianTransportTimeEndpoint

/-! Direct endpoint adapters from the actual common-label curve data to the
exact time-averaged and space-time-regularized laws used by the rough
continuity-equation construction. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory
namespace SharpWasserstein.RoughEulerianTransport.CommonLabelLift
open WeightedTangent RoughEulerianTime RoughEulerianSmoothing
variable {d k : ℕ} [MeasurableSpace (Point (k*d))] [BorelSpace (Point (k*d))]
  {μ : ℝ → ProbabilityMeasure (Point (k*d))}

/-- The actual time-averaged kernel converges in the true quadratic transport
cost to each endpoint, from a supplied genuine label realization. -/
theorem averagedKernel_wassersteinSq_tendsto (h : CommonLabelLift d k μ) (hμ : Continuous μ)
    {J : Type*} {l : Filter J} {a b t₀ : ℝ} {τ t : J → ℝ}
    (hτ : ∀ j,0 < τ j) (ha : ∀ j,a+τ j ≤ t j) (hb : ∀ j,t j+τ j ≤ b)
    (hτlim : Tendsto τ l (𝓝 0)) (htlim : Tendsto t l (𝓝 t₀)) :
    Tendsto (fun j => wassersteinSq
      ((averagedKernel (τ j) (hτ j) ((volume.restrict (Icc a b)) ⊗ₘ probabilityCurveKernel μ hμ)
        (t j)).map (configurationEuclidean d k).symm)
      ((μ t₀ : Measure _).map (configurationEuclidean d k).symm)) l (𝓝 0) := by
  rw [h.law t₀]
  exact averagedKernel_wassersteinSq_tendsto_commonLabel hτ ha hb hτlim htlim
    (probabilityCurveKernel μ hμ) h.P h.F h.measurable (fun ω => h.F (t₀,ω))
    (h.measurable.comp (measurable_const.prodMk measurable_id))
    (fun s _ => h.law_euclidean s) ((h.modulus t₀).mono_left nhdsWithin_le_nhds)

/-- All three smoothing scales vanish independently for the literal
space-time law; a fixed spatial support supplies the moment domination. -/
theorem spaceTimeRegularizedLaw_wassersteinSq_tendsto
    (h : CommonLabelLift d k μ) (hμ : Continuous μ)
    {J : Type*} {l : Filter J} {a b t₀ R : ℝ} {τ ε δ t : J → ℝ}
    (hτ : ∀ j,0 < τ j) (hε : ∀ j,0 < ε j) (hδ : ∀ j,0 ≤ δ j) (hδ₁ : ∀ j,δ j ≤ 1)
    (ha : ∀ j,a+τ j ≤ t j) (hb : ∀ j,t j+τ j ≤ b)
    (hτlim : Tendsto τ l (𝓝 0)) (hεlim : Tendsto ε l (𝓝 0))
    (hδlim : Tendsto δ l (𝓝 0)) (htlim : Tendsto t l (𝓝 t₀))
    (hρ : ∀ᵐ z ∂((volume.restrict (Icc a b)) ⊗ₘ probabilityCurveKernel μ hμ),‖z.2‖ ≤ R) :
    Tendsto (fun j => wassersteinSq
      ((spaceTimeRegularizedLaw (τ j) (hτ j) (ε j) (hε j) (δ j)
        ((volume.restrict (Icc a b)) ⊗ₘ probabilityCurveKernel μ hμ) (t j)).map
        (configurationEuclidean d k).symm)
      ((μ t₀ : Measure _).map (configurationEuclidean d k).symm)) l (𝓝 0) := by
  rw [h.law t₀]
  exact spaceTimeRegularizedLaw_wassersteinSq_tendsto_commonLabel hτ hε hδ hδ₁ ha hb
    hτlim hεlim hδlim htlim (probabilityCurveKernel μ hμ) hρ h.P h.F h.measurable
    (fun ω => h.F (t₀,ω)) (h.measurable.comp (measurable_const.prodMk measurable_id))
    (fun s _ => h.law_euclidean s) ((h.modulus t₀).mono_left nhdsWithin_le_nhds)

end SharpWasserstein.RoughEulerianTransport.CommonLabelLift
