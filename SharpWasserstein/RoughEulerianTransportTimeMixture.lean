import SharpWasserstein.RoughEulerianTimeActionLaw
import SharpWasserstein.TransportConvergence
import SharpWasserstein.ConfigurationEuclidean

/-! Actual time-mixture transport through a supplied common-label realization.
The coupling is constructed on the product of the normalized time kernel and
the original label law. There is no selection of optimal transport plans. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory
namespace SharpWasserstein.RoughEulerianTransport
open WeightedTangent RoughEulerianTime

/-- The genuine probability time-sampling measure at an interior center. -/
def timeSampling (ε : ℝ) (hε : 0 < ε) (a b t : ℝ) : Measure ℝ :=
  (volume.restrict (Icc a b)).withDensity (fun s => ENNReal.ofReal (timeKernel ε hε (t-s)))

theorem timeSampling_probability {ε a b t : ℝ} (hε : 0 < ε)
    (ha : a+ε ≤ t) (hb : t+ε ≤ b) : IsProbabilityMeasure (timeSampling ε hε a b t) := by
  apply isProbabilityMeasure_iff.mpr
  rw [timeSampling,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  have hi : Integrable (fun s => timeKernel ε hε (t-s)) (volume.restrict (Icc a b)) :=
    ((timeKernel_smooth hε).continuous.comp (continuous_const.sub continuous_id)).continuousOn.integrableOn_Icc
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun s => timeKernel_nonneg hε (t-s)),
    timeKernel_window_normalization hε ha hb,ENNReal.ofReal_one]

theorem timeSampling_support {ε a b t : ℝ} (hε : 0 < ε) :
    ∀ᵐ s ∂timeSampling ε hε a b t,s ∈ Icc a b ∧ |t-s| < ε := by
  have hw : Measurable (fun s : ℝ => ENNReal.ofReal (timeKernel ε hε (t-s))) :=
    ((timeKernel_smooth hε).continuous.measurable.comp (measurable_const.sub measurable_id)).ennreal_ofReal
  apply (ae_withDensity_iff hw).mpr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs hw
  refine ⟨hs,lt_of_not_ge fun hn => hw ?_⟩
  rw [timeKernel_eq_zero hε hn,ENNReal.ofReal_zero]

/-- The normalized shrinking time sampling preserves any nonnegative
endpoint limit, using only its proved support and probability normalization. -/
theorem timeSampling_lintegral_tendsto_zero {J : Type*} {l : Filter J} {a b t₀ : ℝ}
    {ε t : J → ℝ} (hε : ∀ j,0 < ε j) (ha : ∀ j,a+ε j ≤ t j) (hb : ∀ j,t j+ε j ≤ b)
    (hεlim : Tendsto ε l (𝓝 0)) (htlim : Tendsto t l (𝓝 t₀))
    {C : ℝ → ℝ≥0∞} (hC : Tendsto C (𝓝[Icc a b] t₀) (𝓝 0)) :
    Tendsto (fun j => ∫⁻ s,C s ∂timeSampling (ε j) (hε j) a b (t j)) l (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro η hη
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhdsWithin_iff.mp
    (ENNReal.tendsto_nhds_zero.mp hC η hη)
  filter_upwards [hεlim.eventually_lt_const (by linarith : 0 < r/2),
    Metric.tendsto_nhds.mp htlim (r/2) (by positivity)] with j hjε hjt
  letI := timeSampling_probability (hε j) (ha j) (hb j)
  have hc : ∀ᵐ s ∂timeSampling (ε j) (hε j) a b (t j),C s ≤ η := by
    filter_upwards [timeSampling_support (a := a) (b := b) (t := t j) (hε j)] with s hs
    apply hball
    refine ⟨?_,hs.1⟩
    have hst : dist s (t j) < ε j := by simpa only [Real.dist_eq,abs_sub_comm] using hs.2
    exact (dist_triangle s (t j) t₀).trans_lt (by linarith)
  calc
    _ ≤ ∫⁻ _s,η ∂timeSampling (ε j) (hε j) a b (t j) := lintegral_mono_ae hc
    _ = η := by simp

variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} [MeasurableSpace (Point n)]

/-- Exact identification of the already constructed averaged kernel with
sampling time and the same original label independently. -/
theorem averagedKernel_eq_commonLabel {ε a b t : ℝ} (hε : 0 < ε)
    (κ : Kernel ℝ (Point n)) [IsMarkovKernel κ]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : ℝ × Ω → Point n) (hF : Measurable F)
    (hκ : ∀ s ∈ Icc a b,κ s = P.map (fun ω => F (s,ω))) :
    averagedKernel ε hε ((volume.restrict (Icc a b)) ⊗ₘ κ) t =
      ((timeSampling ε hε a b t).prod P).map F := by
  apply Measure.ext_of_lintegral
  intro g hg
  have hw : Measurable (fun s : ℝ => ENNReal.ofReal (timeKernel ε hε (t-s))) :=
    ((timeKernel_smooth hε).continuous.measurable.comp (measurable_const.sub measurable_id)).ennreal_ofReal
  have hwt : Measurable (timeWeight (d := n) ε hε t) :=
    (timeWeight_measurable hε).comp (measurable_const.prodMk measurable_id)
  have hgs : Measurable (fun z : ℝ × Point n => g z.2) := hg.comp measurable_snd
  have hwΩ : Measurable (fun z : ℝ × Ω => ENNReal.ofReal (timeKernel ε hε (t-z.1))) :=
    hw.comp measurable_fst
  have hgF : Measurable (fun z : ℝ × Ω => g (F z)) := hg.comp hF
  rw [averagedKernel_apply,lintegral_map hg measurable_snd,
    lintegral_withDensity_eq_lintegral_mul _ hwt hgs,
    Measure.lintegral_compProd (by exact (hw.comp measurable_fst).mul (hg.comp measurable_snd)),
    lintegral_map hg hF,timeSampling,prod_withDensity_left hw,
    lintegral_withDensity_eq_lintegral_mul _ hwΩ hgF,
    lintegral_prod _ ((hwΩ.mul hgF).aemeasurable)]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  rw [hκ s hs]
  change (∫⁻ x, ENNReal.ofReal (timeKernel ε hε (t-s))*g x ∂P.map (fun ω => F (s,ω))) = _
  exact lintegral_map (measurable_const.mul hg) (hF.comp (measurable_const.prodMk measurable_id))

section Configuration
variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]

theorem averagedKernel_configuration_eq_commonLabel {ε a b t : ℝ} (hε : 0 < ε)
    (κ : Kernel ℝ (Point (N*d))) [IsMarkovKernel κ]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : ℝ × Ω → Configuration d N) (hF : Measurable F)
    (hκ : ∀ s ∈ Icc a b,κ s = P.map (fun ω => configurationEuclidean d N (F (s,ω)))) :
    (averagedKernel ε hε ((volume.restrict (Icc a b)) ⊗ₘ κ) t).map
      (configurationEuclidean d N).symm = ((timeSampling ε hε a b t).prod P).map F := by
  rw [averagedKernel_eq_commonLabel hε κ P
    (fun z => configurationEuclidean d N (F z))
    ((configurationEuclidean d N).continuous.measurable.comp hF) hκ,
    Measure.map_map (f := fun z => configurationEuclidean d N (F z))
      (g := (configurationEuclidean d N).symm)
      (configurationEuclidean d N).symm.continuous.measurable
      ((configurationEuclidean d N).continuous.measurable.comp hF)]
  congr 1
  funext z
  exact (configurationEuclidean d N).symm_apply_apply _

/-- A literal coupling bound for the existing time-averaged kernel. -/
theorem averagedKernel_wassersteinSq_le_commonLabel {ε a b t : ℝ} (hε : 0 < ε)
    (ha : a+ε ≤ t) (hb : t+ε ≤ b)
    (κ : Kernel ℝ (Point (N*d))) [IsMarkovKernel κ]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : ℝ × Ω → Configuration d N) (hF : Measurable F)
    (G : Ω → Configuration d N) (hG : Measurable G)
    (hκ : ∀ s ∈ Icc a b,κ s = P.map (fun ω => configurationEuclidean d N (F (s,ω)))) :
    wassersteinSq ((averagedKernel ε hε ((volume.restrict (Icc a b)) ⊗ₘ κ) t).map
      (configurationEuclidean d N).symm) (P.map G) ≤
      ∫⁻ s,∫⁻ ω,ENNReal.ofReal (productCost (F (s,ω)) (G ω)) ∂P ∂timeSampling ε hε a b t := by
  letI := timeSampling_probability hε ha hb
  rw [averagedKernel_configuration_eq_commonLabel hε κ P F hF hκ]
  have he : ((timeSampling ε hε a b t).prod P).map (fun z => G z.2) = P.map G := by
    rw [show (fun z : ℝ × Ω => G z.2) = G ∘ Prod.snd from rfl,
      ← Measure.map_map hG measurable_snd,Measure.map_snd_prod,measure_univ,one_smul]
  have hc := wassersteinSq_commonLabel_le ((timeSampling ε hε a b t).prod P)
    hF (hG.comp measurable_snd)
  change ((timeSampling ε hε a b t).prod P).map (G ∘ Prod.snd) = P.map G at he
  rw [he] at hc
  refine hc.trans_eq ?_
  exact lintegral_prod _ ((measurable_productCost.ennreal_ofReal.comp
    (hF.prodMk (hG.comp measurable_snd))).aemeasurable)
/-- Endpoint convergence for the actual time-averaged law, from a genuine
common-label L² endpoint limit. This is not a claim about arbitrary narrow
curves or measurable choices of optimal couplings. -/
theorem averagedKernel_wassersteinSq_tendsto_commonLabel {J : Type*} {l : Filter J}
    {a b t₀ : ℝ} {ε t : J → ℝ} (hε : ∀ j,0 < ε j)
    (ha : ∀ j,a+ε j ≤ t j) (hb : ∀ j,t j+ε j ≤ b)
    (hεlim : Tendsto ε l (𝓝 0)) (htlim : Tendsto t l (𝓝 t₀))
    (κ : Kernel ℝ (Point (N*d))) [IsMarkovKernel κ]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : ℝ × Ω → Configuration d N) (hF : Measurable F)
    (G : Ω → Configuration d N) (hG : Measurable G)
    (hκ : ∀ s ∈ Icc a b,κ s = P.map (fun ω => configurationEuclidean d N (F (s,ω))))
    (hcost : Tendsto (fun s => ∫⁻ ω,ENNReal.ofReal (productCost (F (s,ω)) (G ω)) ∂P)
      (𝓝[Icc a b] t₀) (𝓝 0)) :
    Tendsto (fun j => wassersteinSq
      ((averagedKernel (ε j) (hε j) ((volume.restrict (Icc a b)) ⊗ₘ κ) (t j)).map
        (configurationEuclidean d N).symm) (P.map G)) l (𝓝 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (timeSampling_lintegral_tendsto_zero hε ha hb hεlim htlim hcost)
    (fun _ => zero_le) (fun j => averagedKernel_wassersteinSq_le_commonLabel
      (hε j) (ha j) (hb j) κ P F hF G hG hκ)

end Configuration

end SharpWasserstein.RoughEulerianTransport
