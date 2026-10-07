module

public import SharpWasserstein.Compat
public import SharpWasserstein.VolterraFourierRecovery
public import SharpWasserstein.VolterraEnergyLimit

@[expose] public section

/-! Actual physical Fourier recovery turns finite trial differential bounds
into Volterra inequalities. Only finite energies are differentiated; the total
energy's scalar measurability and integrability are derived. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology Interval
namespace SharpWasserstein.VolterraFourier
open WeightedTangent
variable {n : ℕ} [MeasurableSpace (Point n)] [BorelSpace (Point n)]
  (P : ℝ) (μ : ℝ → Measure (Point n)) [∀ t,IsFiniteMeasure (μ t)]
  (U : (t : ℝ) → gradientClosure (μ t)) {a t : ℝ}

/-- Continuous finite energies yield measurable total energy on the interval
by actual Fourier recovery; a coarse integrable bound then yields genuine
interval integrability. -/
theorem totalEnergy_intervalIntegrable (hat : a ≤ t)
    (hU : ∀ r ∈ Icc a t,U r ∈ WeightedPeriodicFourierPhysical.periodicSpace P (μ r))
    (hc : ∀ j,ContinuousOn (finiteEnergy P μ U j) (Icc a t))
    {B : ℝ → ℝ} (hB : IntervalIntegrable B volume a t)
    (hbound : ∀ r ∈ Icc a t,totalEnergy μ U r ≤ B r) :
    IntervalIntegrable (totalEnergy μ U) volume a t := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hat]
  apply totalEnergy_integrable P μ U (volume.restrict (Icc a t))
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact hU r hr
  · intro j
    exact ((intervalIntegrable_iff_integrableOn_Icc_of_le hat).mp
      ((hc j).intervalIntegrable_of_Icc hat)).aestronglyMeasurable
  · exact (intervalIntegrable_iff_integrableOn_Icc_of_le hat).mp hB
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact hbound r hr

/-- Literal interval L¹ convergence of the actual finite trial gaps. -/
theorem intervalIntegral_norm_mul_gap_tendsto (hat : a ≤ t) (K : ℝ)
    (hU : ∀ r ∈ Icc a t,U r ∈ WeightedPeriodicFourierPhysical.periodicSpace P (μ r))
    (hc : ∀ j,ContinuousOn (finiteEnergy P μ U j) (Icc a t))
    {B : ℝ → ℝ} (hB : IntervalIntegrable B volume a t)
    (hbound : ∀ r ∈ Icc a t,totalEnergy μ U r ≤ B r) :
    Tendsto (fun j => ∫ r in a..t,‖K*gap P μ U j r‖) atTop (𝓝 0) := by
  have hh := integral_norm_mul_gap_tendsto P μ U (volume.restrict (Icc a t)) K
    (show ∀ᵐ r ∂volume.restrict (Icc a t),U r ∈ WeightedPeriodicFourierPhysical.periodicSpace P (μ r) by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      exact hU r hr)
    (fun j => ((intervalIntegrable_iff_integrableOn_Icc_of_le hat).mp
      ((hc j).intervalIntegrable_of_Icc hat)).aestronglyMeasurable)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hat).mp hB)
    (show ∀ᵐ r ∂volume.restrict (Icc a t),totalEnergy μ U r ≤ B r by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      exact hbound r hr)
  simpa only [intervalIntegral.integral_of_le hat,integral_Icc_eq_integral_Ioc] using hh

/-- A finite trial inequality with a fixed multiple of its actual energy gap
implies the limiting positive-kernel inequality. The finite derivative bound
is the explicit interface; no desired limit inequality is assumed. -/
theorem volterra_bound_of_finite_derivative
    (hat : a ≤ t) {α K : ℝ} {g B : ℝ → ℝ} {f' : ℕ → ℝ → ℝ}
    (hU : ∀ r ∈ Icc a t,U r ∈ WeightedPeriodicFourierPhysical.periodicSpace P (μ r))
    (hc : ∀ j,ContinuousOn (finiteEnergy P μ U j) (Icc a t))
    (hd : ∀ j r,r ∈ Ioo a t → HasDerivAt (finiteEnergy P μ U j) (f' j r) r)
    (hg : IntervalIntegrable g volume a t)
    (hB : IntervalIntegrable B volume a t)
    (hbound : ∀ r ∈ Icc a t,totalEnergy μ U r ≤ B r)
    (hfinite : ∀ j r,r ∈ Ioo a t →
      f' j r ≤ α*finiteEnergy P μ U j r+g r+K*gap P μ U j r) :
    totalEnergy μ U t ≤ Real.exp (α*(t-a))*totalEnergy μ U a+
      (∫ r in a..t,Real.exp (α*(t-r))*g r) := by
  have hEi := totalEnergy_intervalIntegrable P μ U hat hU hc hB hbound
  apply VolterraEnergyLimit.limit_integrating_factor_bound hat hc hd hg
    (fun j => (hEi.sub ((hc j).intervalIntegrable_of_Icc hat)).const_mul K) hfinite
  · exact finiteEnergy_tendsto P μ U a (hU a ⟨le_rfl,hat⟩)
  · exact finiteEnergy_tendsto P μ U t (hU t ⟨hat,le_rfl⟩)
  · exact intervalIntegral_norm_mul_gap_tendsto P μ U hat K hU hc hB hbound

end SharpWasserstein.VolterraFourier
