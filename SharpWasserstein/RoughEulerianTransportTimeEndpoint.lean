import SharpWasserstein.RoughEulerianTransportTimeMixture
import SharpWasserstein.RoughEulerianSmoothingEndpoint
import SharpWasserstein.RoughEulerianTimeActionMoments
import SharpWasserstein.TransportTriangle

/-! Endpoint removal for genuine space-time regularizations of common-label
curves. Time, spatial-convolution, and Gaussian-floor scales can vanish
independently; the only uniform moment bound is derived from fixed carrying
support when this is applied after the actual spatial compression. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory
namespace SharpWasserstein.RoughEulerianTransport
open WeightedTangent RoughEulerianTime RoughEulerianSmoothing

/-- The proved transport triangle passes two actual zero-cost limits through
an intermediate measure; no moment or probability premise is hidden here. -/
theorem wassersteinSq_tendsto_zero_triangle {d N : ℕ} {J : Type*} {l : Filter J}
    {μ ν : J → Measure (Configuration d N)} {ρ : Measure (Configuration d N)}
    (hμν : Tendsto (fun j => wassersteinSq (μ j) (ν j)) l (𝓝 0))
    (hνρ : Tendsto (fun j => wassersteinSq (ν j) ρ) l (𝓝 0)) :
    Tendsto (fun j => wassersteinSq (μ j) ρ) l (𝓝 0) := by
  have hupper := ((hμν.ennrpow_const (1/2)).add (hνρ.ennrpow_const (1/2))).ennrpow_const 2
  norm_num only [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1/2),zero_add,
    ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)] at hupper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper (fun _ => zero_le)
  intro j
  have hh := ENNReal.rpow_le_rpow (wassersteinSq_root_triangle (μ j) (ν j) ρ)
    (by norm_num : (0 : ℝ) ≤ 2)
  simpa only [← ENNReal.rpow_mul,show (1/2:ℝ)*2=1 by norm_num,ENNReal.rpow_one] using hh

variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]

/-- Actual spatial regularization can be removed along moving laws with a
uniform second-moment bound. All three laws are the literal transport marginals. -/
theorem regularizedLaw_moving_wassersteinSq_tendsto {J : Type*} {l : Filter J}
    (μ : J → Measure (Point (N*d))) (hprob : ∀ j,IsProbabilityMeasure (μ j))
    (hμ : ∀ j,Integrable (fun x => ‖x‖^2) (μ j)) {B : ℝ}
    (hB : ∀ j,(∫ x,‖x‖^2 ∂μ j) ≤ B)
    {ε δ : J → ℝ} (hε : ∀ j,0 < ε j) (hδ : ∀ j,0 ≤ δ j) (hδ₁ : ∀ j,δ j ≤ 1)
    (hεlim : Tendsto ε l (𝓝 0)) (hδlim : Tendsto δ l (𝓝 0))
    {ρ : Measure (Configuration d N)}
    (hlim : Tendsto (fun j => wassersteinSq ((μ j).map (configurationEuclidean d N).symm) ρ) l (𝓝 0)) :
    Tendsto (fun j => wassersteinSq
      ((regularizedLaw (ε j) (hε j) (δ j) (μ j)).map (configurationEuclidean d N).symm) ρ) l (𝓝 0) := by
  apply wassersteinSq_tendsto_zero_triangle (ν := fun j => (μ j).map (configurationEuclidean d N).symm) _ hlim
  have hu := ENNReal.tendsto_ofReal ((hεlim.pow 2).add
    (hδlim.mul_const (2*(∫ x : Point (N*d),‖x‖^2 ∂gaussianFloorLaw)+2*B)))
  simp only [zero_pow (by norm_num : 2 ≠ 0),zero_mul,add_zero,ENNReal.ofReal_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu (fun _ => zero_le)
  intro j
  letI := hprob j
  apply (regularizedLaw_wassersteinSq_le (hε j) (hδ j) (hδ₁ j) (μ j) (hμ j)).trans
  apply ENNReal.ofReal_le_ofReal
  gcongr
  · exact hδ j
  · exact hB j

/-- Simultaneous time/space/floor endpoint convergence for the actual law
used in the smoothed continuity equation, with fixed compressed support. -/
theorem spaceTimeRegularizedLaw_wassersteinSq_tendsto_commonLabel
    {Ω : Type*} [MeasurableSpace Ω] {J : Type*} {l : Filter J}
    {a b t₀ R : ℝ} {τ ε δ t : J → ℝ}
    (hτ : ∀ j,0 < τ j) (hε : ∀ j,0 < ε j) (hδ : ∀ j,0 ≤ δ j) (hδ₁ : ∀ j,δ j ≤ 1)
    (ha : ∀ j,a+τ j ≤ t j) (hb : ∀ j,t j+τ j ≤ b)
    (hτlim : Tendsto τ l (𝓝 0)) (hεlim : Tendsto ε l (𝓝 0))
    (hδlim : Tendsto δ l (𝓝 0)) (htlim : Tendsto t l (𝓝 t₀))
    (κ : Kernel ℝ (Point (N*d))) [IsMarkovKernel κ]
    (hρ : ∀ᵐ z ∂((volume.restrict (Icc a b)) ⊗ₘ κ),‖z.2‖ ≤ R)
    (P : Measure Ω) [IsProbabilityMeasure P] (F : ℝ × Ω → Configuration d N) (hF : Measurable F)
    (G : Ω → Configuration d N) (hG : Measurable G)
    (hκ : ∀ s ∈ Icc a b,κ s = P.map (fun ω => configurationEuclidean d N (F (s,ω))))
    (hcost : Tendsto (fun s => ∫⁻ ω,ENNReal.ofReal (productCost (F (s,ω)) (G ω)) ∂P)
      (𝓝[Icc a b] t₀) (𝓝 0)) :
    Tendsto (fun j => wassersteinSq
      ((spaceTimeRegularizedLaw (τ j) (hτ j) (ε j) (hε j) (δ j)
        ((volume.restrict (Icc a b)) ⊗ₘ κ) (t j)).map (configurationEuclidean d N).symm)
      (P.map G)) l (𝓝 0) := by
  let μ (j : J) := averagedKernel (τ j) (hτ j) ((volume.restrict (Icc a b)) ⊗ₘ κ) (t j)
  have hp (j : J) : IsProbabilityMeasure (μ j) := averagedKernel_probability (hτ j) κ (ha j) (hb j)
  have hn (j : J) : ∀ᵐ x ∂μ j,‖x‖^2 ≤ R^2 := by
    filter_upwards [averagedKernel_norm_le (hτ j) ((volume.restrict (Icc a b)) ⊗ₘ κ) hρ (t j)] with x hx
    exact pow_le_pow_left₀ (norm_nonneg _) hx 2
  have hi (j : J) : Integrable (fun x => ‖x‖^2) (μ j) := by
    letI := hp j
    have hmeas : AEStronglyMeasurable (fun x : Point (N*d) => ‖x‖^2) (μ j) :=
      (continuous_norm.pow 2).aestronglyMeasurable
    apply Integrable.of_bound hmeas (R^2)
    filter_upwards [hn j] with x hx
    simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖x‖)] using hx
  have hm (j : J) : (∫ x,‖x‖^2 ∂μ j) ≤ R^2 := by
    letI := hp j
    exact (integral_mono_ae (hi j) (integrable_const _) (hn j)).trans_eq (by simp)
  exact regularizedLaw_moving_wassersteinSq_tendsto μ hp hi hm hε hδ hδ₁ hεlim hδlim
    (averagedKernel_wassersteinSq_tendsto_commonLabel hτ ha hb hτlim htlim κ P F hF G hG hκ hcost)

end SharpWasserstein.RoughEulerianTransport
