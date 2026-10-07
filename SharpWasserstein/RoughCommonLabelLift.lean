module

public import SharpWasserstein.Compat
public import SharpWasserstein.RoughEulerianTransportTimeMixture
public import SharpWasserstein.RoughEulerianCompressionEndpoint
public import SharpWasserstein.RoughEulerianCompressionEquation

@[expose] public section

/-! A genuine common-label realization and its actual quadratic continuity.
This is independent curve data, not a transport conclusion or a choice of
optimal couplings. Translation and the constructed spatial compressions
preserve the data by explicit maps of the same labels. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace SharpWasserstein.RoughEulerianTransport
open WeightedTangent RoughEulerianCompression
variable {d k : ℕ} [MeasurableSpace (Point (k*d))] [BorelSpace (Point (k*d))]

/-- Common labels realizing every law, with an actual mean-square modulus
at every time. The probability and all maps are part of the supplied data. -/
structure CommonLabelLift (d k : ℕ) [MeasurableSpace (Point (k*d))]
    (μ : ℝ → ProbabilityMeasure (Point (k*d))) : Type 1 where
  Ω : Type
  [measurableSpace : MeasurableSpace Ω]
  P : Measure Ω
  [probability : IsProbabilityMeasure P]
  F : ℝ × Ω → Configuration d k
  measurable : Measurable F
  law : ∀ t,(μ t : Measure _).map (configurationEuclidean d k).symm =
    P.map (fun ω => F (t,ω))
  modulus : ∀ s,Tendsto (fun t => ∫⁻ ω,ENNReal.ofReal (productCost (F (t,ω)) (F (s,ω))) ∂P)
    (𝓝 s) (𝓝 0)

attribute [instance] CommonLabelLift.measurableSpace CommonLabelLift.probability

namespace CommonLabelLift
variable {μ : ℝ → ProbabilityMeasure (Point (k*d))}

/-- Translation keeps the same actual probability labels. -/
def translate (h : CommonLabelLift d k μ) (a : ℝ) :
    CommonLabelLift d k (fun t => μ (a+t)) where
  Ω := h.Ω
  measurableSpace := h.measurableSpace
  P := h.P
  probability := h.probability
  F := fun p => h.F (a+p.1,p.2)
  measurable := h.measurable.comp ((measurable_const.add measurable_fst).prodMk measurable_snd)
  law := fun t => h.law (a+t)
  modulus := fun s => (h.modulus (a+s)).comp ((continuous_const.add continuous_id).tendsto s)

/-- The scalar law identity is equivalent to the literal Euclidean
pushforward of the actual labels. -/
theorem law_euclidean (h : CommonLabelLift d k μ) (t : ℝ) :
    (μ t : Measure _) = h.P.map (fun ω => configurationEuclidean d k (h.F (t,ω))) := by
  calc
    _ = ((μ t : Measure _).map (configurationEuclidean d k).symm).map
        (configurationEuclidean d k) := by
      rw [Measure.map_map (configurationEuclidean d k).continuous.measurable
        (configurationEuclidean d k).symm.continuous.measurable]
      simp only [ContinuousLinearEquiv.apply_symm_apply,Function.comp_def]
      exact Measure.map_id.symm
    _ = _ := by
      rw [h.law t,Measure.map_map (f := fun ω => h.F (t,ω)) (configurationEuclidean d k).continuous.measurable
        (h.measurable.comp (measurable_const.prodMk measurable_id))]
      rfl

omit [MeasurableSpace (Point (k*d))] [BorelSpace (Point (k*d))] in
/-- The actual Euclidean compression contracts the full configuration cost. -/
theorem configurationCompression_pair_cost_le {R : ℝ} (hR : R ≠ 0)
    (x y : Configuration d k) :
    productCost (configurationCompression R x) (configurationCompression R y) ≤ productCost x y := by
  simp only [productCost_eq_configurationEuclidean_dist_sq,configurationCompression,
    ContinuousLinearEquiv.apply_symm_apply]
  have hh := (compression_lipschitz hR).norm_sub_le
    (configurationEuclidean d k x) (configurationEuclidean d k y)
  simp only [NNReal.coe_one,one_mul] at hh
  exact pow_le_pow_left₀ (norm_nonneg _) hh 2

/-- Spatial compression transforms the same labels and preserves their
actual mean-square continuity by the exact Euclidean cost contraction. -/
def compress (h : CommonLabelLift d k μ) {R : ℝ} (hR : R ≠ 0) :
    CommonLabelLift d k (compressedCurve R μ) where
  Ω := h.Ω
  measurableSpace := h.measurableSpace
  P := h.P
  probability := h.probability
  F := fun p => configurationCompression R (h.F p)
  measurable := (configurationCompression_continuous R).measurable.comp h.measurable
  law := by
    intro t
    change ((μ t : Measure _).map (compression R)).map (configurationEuclidean d k).symm = _
    calc
      _ = ((μ t : Measure _).map (configurationEuclidean d k).symm).map
          (configurationCompression R) := by
        rw [Measure.map_map (configurationEuclidean d k).symm.continuous.measurable
          (compression_contDiff R).continuous.measurable,
          Measure.map_map (configurationCompression_continuous R).measurable
            (configurationEuclidean d k).symm.continuous.measurable]
        congr 1
        funext x
        simp only [Function.comp_def,configurationCompression,ContinuousLinearEquiv.apply_symm_apply]
      _ = _ := by
        rw [h.law t,Measure.map_map (f := fun ω => h.F (t,ω)) (configurationCompression_continuous R).measurable
          (h.measurable.comp (measurable_const.prodMk measurable_id))]
        rfl
  modulus := by
    intro s
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h.modulus s) (fun _ => zero_le)
    intro t
    apply lintegral_mono
    intro ω
    exact ENNReal.ofReal_le_ofReal (configurationCompression_pair_cost_le hR (h.F (t,ω)) (h.F (s,ω)))

end CommonLabelLift
end SharpWasserstein.RoughEulerianTransport
