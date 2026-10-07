module

public import SharpWasserstein.Compat
public import SharpWasserstein.EulerTimeWeakLimit
public import SharpWasserstein.BrownianHorizon
public import SharpWasserstein.ParticleMomentBounds

@[expose] public section

/-! Actual global laws of bounded, jointly continuous, uniformly spatially
Lipschitz time-dependent drifts driven by independent sqrt-two Brownian paths.
The construction, horizon consistency and moment estimates are explicit. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Interval
namespace SharpWasserstein.BrownianFlow

variable {d N : ℕ} {v : ℝ → Configuration d N → Configuration d N} {M K : ℝ≥0}
  (hv : Continuous (Function.uncurry v)) (hb : ∀ t x, ‖v t x‖ ≤ M)
  (hl : ∀ t, LipschitzWith K (v t))

def law {T : ℝ} (hT : 0 ≤ T) (μ : Measure (Configuration d N)) (t : ℝ) :
    Measure (Configuration d N) :=
  (μ.prod (BrownianNoise.configurationLaw d N T)).map
    (fun p => BoundedFlow.flow hv hb hl hT p.1 p.2 t)

theorem law_probability {T : ℝ} (hT : 0 ≤ T) (μ : Measure (Configuration d N))
    [IsProbabilityMeasure μ] {t : ℝ} (ht : t ∈ Icc 0 T) :
    IsProbabilityMeasure (law hv hb hl hT μ t) :=
  Measure.isProbabilityMeasure_map (BoundedFlow.flow_continuous hv hb hl hT ht).measurable.aemeasurable

theorem law_initial {T : ℝ} (hT : 0 ≤ T) (μ : Measure (Configuration d N))
    [IsProbabilityMeasure μ] : law hv hb hl hT μ 0 = μ := by
  have hw := (measurePreserving_snd (μ := μ)
    (ν := BrownianNoise.configurationLaw d N T)).quasiMeasurePreserving.ae
      (BrownianNoise.configurationLaw_zero_ae hT)
  have heq : (fun p : Configuration d N × C(Icc 0 T, Configuration d N) =>
      BoundedFlow.flow hv hb hl hT p.1 p.2 0) =ᵐ[
        μ.prod (BrownianNoise.configurationLaw d N T)] Prod.fst := by
    filter_upwards [hw] with p hp
    apply (BoundedFlow.flow_trajectory hv hb hl hT p.1 p.2).initial hT
    simpa only [BoundedFlow.noiseExtension,
      projIcc_of_mem _ (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩)] using hp
  unfold law
  rw [Measure.map_congr heq]
  exact (measurePreserving_fst (μ := μ) (ν := BrownianNoise.configurationLaw d N T)).map_eq

theorem law_secondMoment {T : ℝ} (hT : 0 ≤ T) (μ : Measure (Configuration d N))
    [IsProbabilityMeasure μ] (hμ : HasSecondMoment μ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasSecondMoment (law hv hb hl hT μ t) := by
  let ξ := BrownianNoise.configurationLaw d N T
  have hx : MemLp (fun p : Configuration d N × C(Icc 0 T, Configuration d N) => p.1)
      2 (μ.prod ξ) := by
    apply memLp_of_hasSecondMoment_map measurable_fst
    rwa [(measurePreserving_fst (μ := μ) (ν := ξ)).map_eq]
  have hw : MemLp (fun p : Configuration d N × C(Icc 0 T, Configuration d N) =>
      BoundedFlow.noiseExtension hT p.2 t) 2 (μ.prod ξ) := by
    simpa only [Function.comp_def,BoundedFlow.noiseExtension,projIcc_of_mem _ ht] using
      (BrownianNoise.configurationLaw_memLp (d := d) (N := N) ⟨t,ht⟩ 2 (by norm_num)).comp_measurePreserving
        (measurePreserving_snd (μ := μ) (ν := ξ))
  apply hasSecondMoment_map_of_memLp (BoundedFlow.flow_continuous hv hb hl hT ht).measurable
  exact finiteTrajectory_memLp (fun p : Configuration d N × C(Icc 0 T, Configuration d N) => BoundedFlow.flow_trajectory hv hb hl hT p.1 p.2)
    (fun s _ x => hb s x) ht hx hw (BoundedFlow.flow_continuous hv hb hl hT ht).measurable.aestronglyMeasurable

theorem law_restrict {S T : ℝ} (hS : 0 ≤ S) (hST : S ≤ T)
    (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    {t : ℝ} (ht : t ∈ Icc 0 S) :
    law hv hb hl hS μ t = law hv hb hl (hS.trans hST) μ t := by
  let R := Prod.map (id : Configuration d N → Configuration d N)
    (BoundedFlow.restrictPath (E := Configuration d N) hST)
  have hR : MeasurePreserving R
      (μ.prod (BrownianNoise.configurationLaw d N T))
      (μ.prod (BrownianNoise.configurationLaw d N S)) :=
    (MeasurePreserving.id μ).prod (BrownianNoise.configurationLaw_restrict d N hST)
  unfold law
  rw [← hR.map_eq,Measure.map_map
    (BoundedFlow.flow_continuous hv hb hl hS ht).measurable hR.measurable]
  congr 1
  funext p
  exact BoundedFlow.flow_restrict hv hb hl hS hST p.1 p.2 ht

theorem law_horizon_independent {S T : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T)
    (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    {t : ℝ} (htS : t ∈ Icc 0 S) (htT : t ∈ Icc 0 T) :
    law hv hb hl hS μ t = law hv hb hl hT μ t := by
  rcases le_total S T with hST | hTS
  · exact law_restrict hv hb hl hS hST μ htS
  · exact (law_restrict hv hb hl hT hTS μ htT).symm

def globalLaw (μ : Measure (Configuration d N)) (t : ℝ) : Measure (Configuration d N) :=
  law hv hb hl (le_max_right t 0) μ t

theorem globalLaw_eq {T t : ℝ} (hT : 0 ≤ T)
    (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ] (ht : t ∈ Icc 0 T) :
    globalLaw hv hb hl μ t = law hv hb hl hT μ t :=
  law_horizon_independent hv hb hl (le_max_right t 0) hT μ ⟨ht.1,le_max_left t 0⟩ ht

theorem globalLaw_initial (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ] :
    globalLaw hv hb hl μ 0 = μ := law_initial hv hb hl (le_max_right 0 0) μ

theorem globalLaw_probability (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    {t : ℝ} (ht : 0 ≤ t) : IsProbabilityMeasure (globalLaw hv hb hl μ t) :=
  law_probability hv hb hl (le_max_right t 0) μ ⟨ht,le_max_left t 0⟩

theorem globalLaw_secondMoment (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    (hμ : HasSecondMoment μ) {t : ℝ} (ht : 0 ≤ t) : HasSecondMoment (globalLaw hv hb hl μ t) :=
  law_secondMoment hv hb hl (le_max_right t 0) μ hμ ⟨ht,le_max_left t 0⟩

theorem law_momentIntegral_le {T : ℝ} (hT : 0 ≤ T)
    (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    (hμ : HasSecondMoment μ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    (∫ x, productCost x 0 ∂law hv hb hl hT μ t) ≤
      4*(∫ x, productCost x 0 ∂μ) + 4*((N : ℝ)*d*((M : ℝ)*t)^2) + 2*((N : ℝ)*d*(2*t)) := by
  apply BrownianParticle.randomMap_momentIntegral_le μ hμ ht
    (fun p => BoundedFlow.flow hv hb hl hT p.1 p.2 t)
    (BoundedFlow.flow_continuous hv hb hl hT ht).measurable
    (law_secondMoment hv hb hl hT μ hμ ht)
  intro p
  have hp := (BoundedFlow.flow_trajectory hv hb hl hT p.1 p.2).productCost_bound
    M.coe_nonneg (fun s _ x => hb s x) ht
  simpa only [BoundedFlow.noiseExtension,projIcc_of_mem _ ht] using hp

theorem globalLaw_momentBound (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    (hμ : HasSecondMoment μ) {T : ℝ} (hT : 0 ≤ T) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ t ∈ Icc 0 T,
      (∫⁻ x, ENNReal.ofReal (productCost x 0) ∂globalLaw hv hb hl μ t) ≤ C := by
  refine ⟨ENNReal.ofReal (4*(∫ x, productCost x 0 ∂μ) +
    4*((N : ℝ)*d*((M : ℝ)*T)^2) + 2*((N : ℝ)*d*(2*T))), ENNReal.ofReal_lt_top, ?_⟩
  intro t ht
  rw [globalLaw_eq hv hb hl hT μ ht,← ofReal_integral_eq_lintegral_ofReal
    (law_secondMoment hv hb hl hT μ hμ ht).integrable_cost
    (Eventually.of_forall (fun x => productCost_nonneg x 0))]
  apply ENNReal.ofReal_le_ofReal
  refine (law_momentIntegral_le hv hb hl hT μ hμ ht).trans ?_
  have hsq : ((M : ℝ)*t)^2 ≤ ((M : ℝ)*T)^2 := by
    apply (sq_le_sq₀ (mul_nonneg M.coe_nonneg ht.1) (mul_nonneg M.coe_nonneg hT)).mpr
    exact mul_le_mul_of_nonneg_left ht.2 M.coe_nonneg
  have ha : (N : ℝ)*d*((M : ℝ)*t)^2 ≤ (N : ℝ)*d*((M : ℝ)*T)^2 :=
    mul_le_mul_of_nonneg_left hsq (by positivity)
  have hb' : (N : ℝ)*d*(2*t) ≤ (N : ℝ)*d*(2*T) :=
    mul_le_mul_of_nonneg_left (by linarith [ht.2]) (by positivity)
  linarith

theorem law_integral_eq {T : ℝ} (hT : 0 ≤ T)
    (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    {f : Configuration d N → ℝ} (hf : Continuous f) {t : ℝ} (ht : t ∈ Icc 0 T) :
    (∫ x, f x ∂law hv hb hl hT μ t) =
      ∫ p : Configuration d N × C(Icc 0 T, Configuration d N),
        f (BoundedFlow.flow hv hb hl hT p.1 p.2 t) ∂μ.prod (BrownianNoise.configurationLaw d N T) :=
  integral_map (BoundedFlow.flow_continuous hv hb hl hT ht).measurable.aemeasurable hf.aestronglyMeasurable

end SharpWasserstein.BrownianFlow
