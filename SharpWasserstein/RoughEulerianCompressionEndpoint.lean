import SharpWasserstein.RoughEulerianCompressionGeometry
import SharpWasserstein.ConfigurationEuclidean
import SharpWasserstein.TransportConvergence
import SharpWasserstein.MarginalMoments
import SharpWasserstein.EulerLaw

/-! Actual endpoint transport convergence of the smooth compressions. A graph
coupling has exactly the Euclidean compression displacement cost. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff
namespace SharpWasserstein.RoughEulerianCompression
open WeightedTangent
variable {d N : ℕ}

def configurationCompression (R : ℝ) (x : Configuration d N) : Configuration d N :=
  (configurationEuclidean d N).symm (compression R (configurationEuclidean d N x))

theorem configurationCompression_continuous (R : ℝ) :
    Continuous (configurationCompression (d := d) (N := N) R) :=
  (configurationEuclidean d N).symm.continuous.comp
    ((compression_contDiff R).continuous.comp (configurationEuclidean d N).continuous)

theorem configurationCompression_cost (R : ℝ) (x : Configuration d N) :
    productCost (configurationCompression R x) x =
      ‖compression R (configurationEuclidean d N x)-configurationEuclidean d N x‖^2 := by
  rw [productCost_eq_configurationEuclidean_dist_sq]
  simp only [configurationCompression,ContinuousLinearEquiv.apply_symm_apply]

theorem configurationCompression_cost_bound {R : ℝ} (hR : R ≠ 0) (x : Configuration d N) :
    productCost (configurationCompression R x) x ≤ 4*productCost x 0 := by
  rw [configurationCompression_cost,productCost_eq_configurationEuclidean_dist_sq,map_zero,sub_zero]
  exact compression_displacement_bound hR _

/-- The actual graph-coupling displacement is integrable under precisely P₂. -/
theorem configurationCompression_cost_integrable (μ : Measure (Configuration d N))
    (hμ : HasSecondMoment μ) {R : ℝ} (hR : R ≠ 0) :
    Integrable (fun x => productCost (configurationCompression R x) x) μ := by
  apply ((hasSecondMoment_iff_integrable μ).mp hμ).const_mul 4 |>.mono'
    ((measurable_productCost.comp ((configurationCompression_continuous R).measurable.prodMk
      measurable_id)).aestronglyMeasurable)
  exact Eventually.of_forall fun x => by
    simp only [Function.comp_apply,id_eq,Real.norm_eq_abs]
    rw [abs_of_nonneg (productCost_nonneg _ _)]
    exact configurationCompression_cost_bound hR x

/-- The exact Euclidean graph-coupling costs vanish. -/
theorem configurationCompression_cost_tendsto (μ : Measure (Configuration d N))
    (hμ : HasSecondMoment μ) :
    Tendsto (fun k : ℕ => ∫ x,productCost (configurationCompression ((k:ℝ)+1) x) x ∂μ)
      atTop (𝓝 0) := by
  have ht := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun k x => productCost (configurationCompression ((k:ℝ)+1) x) x)
    (f := fun _ => (0:ℝ)) (fun x => 4*productCost x 0) ?_
    (((hasSecondMoment_iff_integrable μ).mp hμ).const_mul 4) ?_ ?_
  · simpa only [integral_zero] using ht
  · intro k
    exact (measurable_productCost.comp ((configurationCompression_continuous _).measurable.prodMk
      measurable_id)).aestronglyMeasurable
  · intro k
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (productCost_nonneg _ _)]
      exact configurationCompression_cost_bound (by positivity) x
  · filter_upwards [] with x
    simp only [configurationCompression_cost]
    simpa only [sub_self,norm_zero,zero_pow (by decide : 2 ≠ 0)] using
      (((compression_tendsto (configurationEuclidean d N x)).sub_const
        (configurationEuclidean d N x)).norm.pow 2)

/-- Actual Wasserstein convergence, using the graph coupling with no dimension loss. -/
theorem configurationCompression_wassersteinSq_tendsto (μ : Measure (Configuration d N))
    [IsProbabilityMeasure μ] (hμ : HasSecondMoment μ) :
    Tendsto (fun k : ℕ => wassersteinSq (μ.map (configurationCompression ((k:ℝ)+1))) μ)
      atTop (𝓝 0) := by
  have hu := ENNReal.tendsto_ofReal (configurationCompression_cost_tendsto μ hμ)
  rw [ENNReal.ofReal_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu (fun _ => zero_le)
  intro k
  have hc := wassersteinSq_commonLabel_le μ (configurationCompression_continuous ((k:ℝ)+1)).measurable
    measurable_id
  rw [Measure.map_id] at hc
  apply hc.trans_eq
  exact (ofReal_integral_eq_lintegral_ofReal
    (configurationCompression_cost_integrable μ hμ (by positivity))
    (Eventually.of_forall fun x => productCost_nonneg _ _)).symm

/-- Narrow convergence needs no moment assumption. -/
theorem compression_probability_tendsto {m : ℕ} [MeasurableSpace (Point m)] [BorelSpace (Point m)]
    (μ : ProbabilityMeasure (Point m)) :
    Tendsto (fun k : ℕ => μ.map (compression_contDiff ((k:ℝ)+1)).continuous.measurable.aemeasurable)
      atTop (𝓝 μ) := by
  have he : μ.map (measurable_id.aemeasurable) = μ := by
    apply Subtype.ext
    exact Measure.map_id
  have ht := probabilityMeasure_map_tendsto μ
    (fun k => (compression_contDiff ((k:ℝ)+1)).continuous.measurable) measurable_id
    (Eventually.of_forall compression_tendsto)
  simpa only [he] using ht

end SharpWasserstein.RoughEulerianCompression
