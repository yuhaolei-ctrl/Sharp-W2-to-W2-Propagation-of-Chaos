import SharpWasserstein.TransportTriangle
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Transport length of a common-label L² trajectory

Each L² random configuration is pushed forward to its actual probability law.
The joint law of two representatives supplies a coupling, so the Wasserstein
distance is bounded by their L² displacement. A Bochner integral equation, or
the fundamental theorem of calculus for an L²-valued curve, then gives the
integrated-speed bound.

These are Lagrangian statements. Constructing this curve from a weak Eulerian
continuity equation is a separate analytic step, not an assumption disguised
as a transport-length estimate here.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SharpWasserstein

/-- The Euclidean coordinates underlying the unnormalized product cost. -/
def configurationOfEuclidean {d N : ℕ}
    (x : EuclideanSpace ℝ (Fin N × Fin d)) : Configuration d N :=
  fun i j => x (i, j)

theorem continuous_configurationOfEuclidean {d N : ℕ} :
    Continuous (configurationOfEuclidean (d := d) (N := N)) := by
  unfold configurationOfEuclidean
  fun_prop

theorem displacement_configurationOfEuclidean {d N : ℕ}
    (x y : EuclideanSpace ℝ (Fin N × Fin d)) :
    transportDisplacement (configurationOfEuclidean x, configurationOfEuclidean y) = x - y := by
  ext i
  rfl

/-- Flatten a configuration into the Euclidean space carrying its actual cost. -/
def configurationToEuclidean {d N : ℕ} (x : Configuration d N) :
    EuclideanSpace ℝ (Fin N × Fin d) := transportDisplacement (x, 0)

theorem continuous_configurationToEuclidean {d N : ℕ} :
    Continuous (configurationToEuclidean (d := d) (N := N)) :=
  continuous_transportDisplacement.comp (continuous_id.prodMk continuous_const)

theorem configurationOfEuclidean_toEuclidean {d N : ℕ} (x : Configuration d N) :
    configurationOfEuclidean (configurationToEuclidean x) = x := by
  ext i j
  simp [configurationOfEuclidean, configurationToEuclidean, transportDisplacement]

theorem productCost_configurationOfEuclidean_zero {d N : ℕ}
    (x : EuclideanSpace ℝ (Fin N × Fin d)) :
    productCost (configurationOfEuclidean x) 0 = ‖x‖ ^ 2 := by
  change productCost (configurationOfEuclidean x) (configurationOfEuclidean 0) = _
  rw [productCost_eq_displacement_norm_sq, displacement_configurationOfEuclidean, sub_zero]

/-- L² random configurations with their Euclidean, rather than sup, norm. -/
abbrev ConfigurationL2 {Ω : Type*} [MeasurableSpace Ω] (d N : ℕ) (P : Measure Ω) :=
  Lp (EuclideanSpace ℝ (Fin N × Fin d)) 2 P

/-- The speed norm is the actual square-integrated Euclidean velocity. -/
theorem configurationL2_norm_sq {Ω : Type*} [MeasurableSpace Ω] {d N : ℕ}
    {P : Measure Ω} (V : ConfigurationL2 d N P) :
    ‖V‖ ^ 2 = ∫ ω, ‖V ω‖ ^ 2 ∂P := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

def configurationRepresentative {Ω : Type*} [MeasurableSpace Ω] {d N : ℕ}
    {P : Measure Ω} (Z : ConfigurationL2 d N P) : Ω → Configuration d N :=
  fun ω => configurationOfEuclidean (Z ω)

theorem measurable_configurationRepresentative {Ω : Type*} [MeasurableSpace Ω] {d N : ℕ}
    {P : Measure Ω} (Z : ConfigurationL2 d N P) :
    Measurable (configurationRepresentative Z) :=
  (continuous_configurationOfEuclidean.comp_stronglyMeasurable (Lp.stronglyMeasurable Z)).measurable

/-- The actual law of an L² random configuration. -/
def l2ConfigurationLaw {Ω : Type*} [MeasurableSpace Ω] {d N : ℕ}
    (P : Measure Ω) (Z : ConfigurationL2 d N P) : Measure (Configuration d N) :=
  Measure.map (configurationRepresentative Z) P

theorem l2ConfigurationLaw_probability {Ω : Type*} [MeasurableSpace Ω] {d N : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ConfigurationL2 d N P) :
    IsProbabilityMeasure (l2ConfigurationLaw P Z) :=
  Measure.isProbabilityMeasure_map (measurable_configurationRepresentative Z).aemeasurable

/-- The law has a genuine finite Euclidean second moment. -/
theorem l2ConfigurationLaw_secondMoment {Ω : Type*} [MeasurableSpace Ω] {d N : ℕ}
    (P : Measure Ω) (Z : ConfigurationL2 d N P) :
    HasSecondMoment (l2ConfigurationLaw P Z) := by
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable Z)).mp (Lp.memLp Z)
  have hm : Measurable (fun x : Configuration d N => ENNReal.ofReal (productCost x 0)) := by
    unfold productCost
    fun_prop
  rw [HasSecondMoment, l2ConfigurationLaw,
    lintegral_map hm (measurable_configurationRepresentative Z)]
  simp only [configurationRepresentative, productCost_configurationOfEuclidean_zero]
  exact (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun _ => sq_nonneg _)).mp hi.2

/-- Lift a given random configuration without changing its law. -/
def l2LiftConfiguration {Ω : Type*} [MeasurableSpace Ω] {d N : ℕ}
    {P : Measure Ω} (X : Ω → Configuration d N)
    (hX : MemLp (fun ω => configurationToEuclidean (X ω)) 2 P) : ConfigurationL2 d N P :=
  hX.toLp (fun ω => configurationToEuclidean (X ω))

/-- Passing to the L² equivalence class preserves the original pushforward law. -/
theorem law_l2LiftConfiguration {Ω : Type*} [MeasurableSpace Ω] {d N : ℕ}
    {P : Measure Ω} (X : Ω → Configuration d N)
    (hX : MemLp (fun ω => configurationToEuclidean (X ω)) 2 P) :
    l2ConfigurationLaw P (l2LiftConfiguration X hX) = Measure.map X P := by
  apply Measure.map_congr
  filter_upwards [hX.coeFn_toLp] with ω hω
  change configurationOfEuclidean ((hX.toLp _) ω) = X ω
  rw [hω, configurationOfEuclidean_toEuclidean]

/-- The common-label joint law is constructed explicitly and has the required marginals. -/
theorem l2_commonLabel_isCoupling {Ω : Type*} [MeasurableSpace Ω] {d N : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (Z W : ConfigurationL2 d N P) :
    IsCoupling (l2ConfigurationLaw P Z) (l2ConfigurationLaw P W)
      (Measure.map (fun ω => (configurationRepresentative Z ω, configurationRepresentative W ω)) P) := by
  have hm := (measurable_configurationRepresentative Z).prodMk
    (measurable_configurationRepresentative W)
  refine ⟨Measure.isProbabilityMeasure_map hm.aemeasurable, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst hm]
    rfl
  · rw [Measure.map_map measurable_snd hm]
    rfl

/-- The common-label coupling has precisely the L² displacement cost. -/
theorem l2_commonLabel_cost_root {Ω : Type*} [MeasurableSpace Ω] {d N : ℕ}
    (P : Measure Ω) (Z W : ConfigurationL2 d N P) :
    transportCost (Measure.map (fun ω =>
      (configurationRepresentative Z ω, configurationRepresentative W ω)) P) ^ (1 / 2 : ℝ) =
      ‖Z - W‖ₑ := by
  rw [transportCost_map_root_eq_eLpNorm P _ _
    (measurable_configurationRepresentative Z) (measurable_configurationRepresentative W)]
  simp only [configurationRepresentative, displacement_configurationOfEuclidean]
  rw [Lp.enorm_def]
  exact (eLpNorm_congr_ae (Lp.coeFn_sub Z W)).symm

/-- Genuine quadratic transport is bounded by a common-label L² displacement. -/
theorem wassersteinSq_root_l2Law_le {Ω : Type*} [MeasurableSpace Ω] {d N : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (Z W : ConfigurationL2 d N P) :
    wassersteinSq (l2ConfigurationLaw P Z) (l2ConfigurationLaw P W) ^ (1 / 2 : ℝ) ≤
      ‖Z - W‖ₑ := by
  exact (ENNReal.rpow_le_rpow (wassersteinSq_le_cost (l2_commonLabel_isCoupling P Z W))
    (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans_eq (l2_commonLabel_cost_root P Z W)

theorem wassersteinSq_sqrt_l2Law_le {Ω : Type*} [MeasurableSpace Ω] {d N : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (Z W : ConfigurationL2 d N P) :
    Real.sqrt (wassersteinSq (l2ConfigurationLaw P Z) (l2ConfigurationLaw P W)).toReal ≤
      ‖Z - W‖ := by
  have ht := ENNReal.toReal_mono enorm_ne_top (wassersteinSq_root_l2Law_le P Z W)
  simpa only [← ENNReal.toReal_rpow, ← Real.sqrt_eq_rpow, toReal_enorm] using ht

/-- A genuine L² integral equation yields a Wasserstein length bound.
The Bochner-integrability assumption ensures that the supplied velocity is an
actual integrable velocity, rather than a value assigned by the total integral. -/
theorem wasserstein_length_of_l2_integral {Ω : Type*} [MeasurableSpace Ω] {d N : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ConfigurationL2 d N P) (V : ℝ → ConfigurationL2 d N P)
    {a b : ℝ} (hab : a ≤ b) (hV : IntervalIntegrable V volume a b)
    (heq : Z b - Z a = ∫ t in a..b, V t) :
    Real.sqrt (wassersteinSq (l2ConfigurationLaw P (Z a))
      (l2ConfigurationLaw P (Z b))).toReal ≤ ∫ t in a..b, ‖V t‖ := by
  have hd := wassersteinSq_sqrt_l2Law_le P (Z a) (Z b)
  rw [norm_sub_rev, heq] at hd
  exact hd.trans (intervalIntegral.norm_integral_le_of_norm_le hab
    (Filter.Eventually.of_forall fun _ _ => le_rfl) hV.norm)

/-- Squaring the length bound controls the extended-valued transport cost itself;
finiteness follows from the actual L² laws rather than a `toReal` convention. -/
theorem wassersteinSq_of_l2_integral {Ω : Type*} [MeasurableSpace Ω] {d N : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ConfigurationL2 d N P) (V : ℝ → ConfigurationL2 d N P)
    {a b : ℝ} (hab : a ≤ b) (hV : IntervalIntegrable V volume a b)
    (heq : Z b - Z a = ∫ t in a..b, V t) :
    wassersteinSq (l2ConfigurationLaw P (Z a)) (l2ConfigurationLaw P (Z b)) ≤
      ENNReal.ofReal ((∫ t in a..b, ‖V t‖) ^ 2) := by
  letI := l2ConfigurationLaw_probability P (Z a)
  letI := l2ConfigurationLaw_probability P (Z b)
  have hfinite := wassersteinSq_lt_top _ _
    (l2ConfigurationLaw_secondMoment P (Z a)) (l2ConfigurationLaw_secondMoment P (Z b))
  have hlength := wasserstein_length_of_l2_integral P Z V hab hV heq
  have hn : 0 ≤ ∫ t in a..b, ‖V t‖ :=
    intervalIntegral.integral_nonneg hab (fun _ _ => norm_nonneg _)
  have hs := (sq_le_sq₀ (Real.sqrt_nonneg _) hn).mpr hlength
  rw [Real.sq_sqrt ENNReal.toReal_nonneg] at hs
  rw [← ENNReal.ofReal_toReal hfinite.ne]
  exact ENNReal.ofReal_le_ofReal hs

/-- Differentiability and an integrable L² velocity imply the actual transport
length bound by the Banach-space fundamental theorem of calculus. -/
theorem wasserstein_length_of_l2_derivative {Ω : Type*} [MeasurableSpace Ω] {d N : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ConfigurationL2 d N P) (V : ℝ → ConfigurationL2 d N P)
    {a b : ℝ} (hab : a ≤ b) (hZ : ContinuousOn Z (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt Z (V t) t)
    (hV : IntervalIntegrable V volume a b) :
    Real.sqrt (wassersteinSq (l2ConfigurationLaw P (Z a))
      (l2ConfigurationLaw P (Z b))).toReal ≤ ∫ t in a..b, ‖V t‖ := by
  apply wasserstein_length_of_l2_integral P Z V hab hV
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hZ hderiv hV).symm

/-- The same estimate for the original given random trajectory `Z(t,ω)`.
The differentiability hypothesis is in the Euclidean L² space; no transport
speed, length inequality, or existence of a coupling is assumed. -/
theorem wasserstein_length_of_random_trajectory {Ω : Type*} [MeasurableSpace Ω] {d N : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ℝ → Ω → Configuration d N)
    (h₂ : ∀ t, MemLp (fun ω => configurationToEuclidean (Z t ω)) 2 P)
    (V : ℝ → ConfigurationL2 d N P) {a b : ℝ} (hab : a ≤ b)
    (hZ : ContinuousOn (fun t => l2LiftConfiguration (Z t) (h₂ t)) (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b,
      HasDerivAt (fun s => l2LiftConfiguration (Z s) (h₂ s)) (V t) t)
    (hV : IntervalIntegrable V volume a b) :
    Real.sqrt (wassersteinSq (Measure.map (Z a) P) (Measure.map (Z b) P)).toReal ≤
      ∫ t in a..b, ‖V t‖ := by
  have h := wasserstein_length_of_l2_derivative P
    (fun t => l2LiftConfiguration (Z t) (h₂ t)) V hab hZ hderiv hV
  simpa only [law_l2LiftConfiguration] using h

end SharpWasserstein
