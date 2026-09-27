import SharpWasserstein.RoughEulerianSmoothingMixture
import SharpWasserstein.ConfigurationEuclidean
import SharpWasserstein.TransportConvergence

/-! Actual Wasserstein convergence of the compact-convolution/Gaussian-floor
regularization. The coupling is pushed through the exact Euclidean coordinate
equivalence, preserving the manuscript's full sum-of-squares transport cost. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff NNReal
namespace SharpWasserstein.RoughEulerianSmoothing
open WeightedTangent

theorem coupling_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ ν : Measure X} {γ : Measure (X × X)} (hγ : IsCoupling μ ν γ)
    {f : X → Y} (hf : Measurable f) :
    IsCoupling (μ.map f) (ν.map f) (γ.map (fun z => (f z.1,f z.2))) := by
  letI : IsProbabilityMeasure γ := hγ.1
  have hm : Measurable (fun z : X × X => (f z.1,f z.2)) :=
    (hf.comp measurable_fst).prodMk (hf.comp measurable_snd)
  refine ⟨Measure.isProbabilityMeasure_map hm.aemeasurable, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst hm]
    change γ.map (f ∘ Prod.fst) = μ.map f
    rw [← Measure.map_map hf measurable_fst, hγ.2.1]
  · rw [Measure.map_map measurable_snd hm]
    change γ.map (f ∘ Prod.snd) = ν.map f
    rw [← Measure.map_map hf measurable_snd, hγ.2.2]

variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]

theorem wassersteinSq_euclidean_coupling_le
    {μ ν : Measure (Point (N*d))} {γ : Measure (Point (N*d) × Point (N*d))}
    (hγ : IsCoupling μ ν γ) (hi : Integrable (fun z => ‖z.1-z.2‖^2) γ) :
    wassersteinSq (μ.map (configurationEuclidean d N).symm)
      (ν.map (configurationEuclidean d N).symm) ≤ ENNReal.ofReal (∫ z, ‖z.1-z.2‖^2 ∂γ) := by
  have hm : Measurable (fun z : Point (N*d) × Point (N*d) =>
      ((configurationEuclidean d N).symm z.1,(configurationEuclidean d N).symm z.2)) :=
    ((configurationEuclidean d N).symm.continuous.measurable.comp measurable_fst).prodMk
      ((configurationEuclidean d N).symm.continuous.measurable.comp measurable_snd)
  have hc := wassersteinSq_le_cost (coupling_map hγ (configurationEuclidean d N).symm.continuous.measurable)
  rw [transportCost, lintegral_map measurable_productCost.ennreal_ofReal hm] at hc
  have he (z : Point (N*d) × Point (N*d)) :
      productCost ((configurationEuclidean d N).symm z.1) ((configurationEuclidean d N).symm z.2) =
        ‖z.1-z.2‖^2 := by
    rw [productCost_eq_configurationEuclidean_dist_sq]
    simp only [ContinuousLinearEquiv.apply_symm_apply]
  simp only [he] at hc
  exact hc.trans_eq (ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun z => sq_nonneg ‖z.1-z.2‖)).symm

theorem regularizedLaw_wassersteinSq_le {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1)
    (μ : Measure (Point (N*d))) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x => ‖x‖^2) μ) :
    wassersteinSq ((regularizedLaw ε hε δ μ).map (configurationEuclidean d N).symm)
      (μ.map (configurationEuclidean d N).symm) ≤
      ENNReal.ofReal (ε^2 + δ*(2*(∫ x : Point (N*d), ‖x‖^2 ∂gaussianFloorLaw)+2*(∫ y, ‖y‖^2 ∂μ))) :=
  (wassersteinSq_euclidean_coupling_le (regularizationCoupling_isCoupling hε hδ hδ₁ μ)
    (regularizationCoupling_cost_integrable hε δ μ hμ)).trans
      (ENNReal.ofReal_le_ofReal (regularizationCoupling_cost_le hε hδ hδ₁ μ hμ))

/-- Both smoothing parameters can vanish independently. The result is the
actual unnormalized quadratic transport distance, not merely weak convergence. -/
theorem regularizedLaw_wassersteinSq_tendsto
    (μ : Measure (Point (N*d))) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x => ‖x‖^2) μ) {ε δ : ℕ → ℝ}
    (hε : ∀ n, 0 < ε n) (hδ : ∀ n, 0 ≤ δ n) (hδ₁ : ∀ n, δ n ≤ 1)
    (hεlim : Tendsto ε atTop (𝓝 0)) (hδlim : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n => wassersteinSq ((regularizedLaw (ε n) (hε n) (δ n) μ).map
      (configurationEuclidean d N).symm) (μ.map (configurationEuclidean d N).symm)) atTop (𝓝 0) := by
  have hu := ENNReal.tendsto_ofReal ((hεlim.pow 2).add
    (hδlim.mul_const (2*(∫ x : Point (N*d), ‖x‖^2 ∂gaussianFloorLaw)+2*(∫ y, ‖y‖^2 ∂μ))))
  simp only [zero_pow (by norm_num : 2 ≠ 0), zero_mul, add_zero, ENNReal.ofReal_zero] at hu
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu (fun _ => zero_le)
    (fun n => regularizedLaw_wassersteinSq_le (hε n) (hδ n) (hδ₁ n) μ hμ)

end SharpWasserstein.RoughEulerianSmoothing
