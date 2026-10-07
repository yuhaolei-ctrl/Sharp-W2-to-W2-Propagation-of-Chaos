module

public import SharpWasserstein.Compat
public import SharpWasserstein.EulerianTransportCompact
public import SharpWasserstein.WeightedIntegralSquare

@[expose] public section

/-! Exact finite-action transport for genuine regular Eulerian curves.
The time factor follows from an actual Cauchy--Schwarz estimate, retaining
coefficient one and the unnormalized Euclidean product cost. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal ENNReal Topology ContDiff Interval
namespace SharpWasserstein.RoughEulerianTransport
open NoiseAverage

/-- Cauchy--Schwarz for the actual square-root action integral. -/
theorem integral_sqrt_sq_le_time_mul {Q E : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hQ : Continuous Q) (hQ₀ : ∀ t,0 ≤ Q t)
    (hE : IntervalIntegrable E volume a b)
    (hQE : ∀ᵐ t ∂volume.restrict (Icc a b),Q t ≤ E t) :
    (∫ t in a..b,Real.sqrt (Q t))^2 ≤ (b-a)*(∫ t in a..b,E t) := by
  rcases eq_or_lt_of_le hab with heq | hlt
  · subst b
    simp
  have hmass : (∫ t in Icc a b,(1:ℝ)) = b-a := by
    rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hab]
    simp
  have hroot := (Real.continuous_sqrt.comp hQ).integrableOn_Icc (μ := volume) (a := a) (b := b)
  have hsquare : IntegrableOn (fun t => (Real.sqrt (Q t))^2) (Icc a b) := by
    simpa only [Real.sq_sqrt (hQ₀ _)] using hQ.integrableOn_Icc (μ := volume) (a := a) (b := b)
  have hh := WeightedIntegralSquare.weighted_scalar_sq_le (μ := volume.restrict (Icc a b))
    (w := fun _ => (1:ℝ)) (r := fun t => Real.sqrt (Q t)) (integrable_const 1)
    (by simpa only [one_mul,IntegrableOn,Function.comp_def] using hroot) (by simpa only [one_mul,IntegrableOn] using hsquare)
    (Eventually.of_forall fun _ => zero_le_one) (by rw [hmass]; linarith)
  simp only [one_mul,hmass,Real.sq_sqrt (hQ₀ _)] at hh
  have hc := (div_le_iff₀ (sub_pos.mpr hlt)).mp hh
  have hi : (∫ t in Icc a b,Real.sqrt (Q t)) = ∫ t in a..b,Real.sqrt (Q t) := by
    rw [integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le hab]
  have hiQ : (∫ t in Icc a b,Q t) = ∫ t in a..b,Q t := by
    rw [integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le hab]
  rw [hi,hiQ] at hc
  have hmono := intervalIntegral.integral_mono_ae_restrict hab (hQ.intervalIntegrable a b) hE hQE
  exact hc.trans (by nlinarith [mul_le_mul_of_nonneg_left hmono (sub_nonneg.mpr hab)])

/-- The genuine regular compact weak equation gives the coefficient-one
finite-action bound; a law/characteristic representation is not assumed. -/
theorem regular_wassersteinSq_le_finiteAction {d N : ℕ}
    {v : ℝ → Configuration d N → Configuration d N}
    {μ : ℝ → ProbabilityMeasure (Configuration d N)} {T : ℝ}
    (h : EulerianTransport.CompactWeakContinuity v μ T) {M K K₁ : ℝ≥0}
    (hv : Continuous (Function.uncurry v)) (hb : ∀ t x,‖v t x‖ ≤ M)
    (hl : ∀ t,LipschitzWith K (v t)) (hT : 0 ≤ T)
    (hvs : ∀ t,ContDiff ℝ ∞ (v t)) (hvB : ∀ t,AllDerivativesBounded (v t))
    (hv₁ : ∀ t,LipschitzWith K₁ (fderiv ℝ (v t)))
    (hP : HasSecondMoment (μ 0 : Measure (Configuration d N)))
    {a b : ℝ} (ha : a ∈ Icc 0 T) (hbT : b ∈ Icc 0 T) (hab : a ≤ b)
    {E : ℝ → ℝ} (hE : IntervalIntegrable E volume a b)
    (hbound : ∀ᵐ t ∂volume.restrict (Icc a b),
      (∫ x,productCost (v t x) 0 ∂(μ t : Measure _)) ≤ E t) :
    wassersteinSq (μ a : Measure (Configuration d N)) (μ b : Measure (Configuration d N)) ≤
      ENNReal.ofReal ((b-a)*(∫ t in a..b,E t)) := by
  let Q := fun t => ∫ x,productCost (v t x) 0 ∂(μ t : Measure (Configuration d N))
  have hqc : Continuous (fun p : ℝ × Configuration d N => productCost (v p.1 p.2) 0) := by
    unfold productCost
    fun_prop
  have hqb (p : ℝ × Configuration d N) :
      ‖productCost (v p.1 p.2) 0‖ ≤ (N:ℝ)*d*(M:ℝ)^2 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (productCost_nonneg _ _)]
    exact (productCost_le_dimension_norm _ _).trans (by
      simp only [sub_zero]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hb p.1 p.2) 2) (by positivity))
  have hQ : Continuous Q := continuous_integral_parameter_probability μ h.continuous _ hqc hqb
  have hQ₀ (t : ℝ) : 0 ≤ Q t := integral_nonneg (fun x => productCost_nonneg _ _)
  exact (h.wassersteinSq_le_action hv hb hl hT hvs hvB hv₁ hP ha hbT hab).trans
    (ENNReal.ofReal_le_ofReal (integral_sqrt_sq_le_time_mul hab hQ hQ₀ hE hbound))

end SharpWasserstein.RoughEulerianTransport
