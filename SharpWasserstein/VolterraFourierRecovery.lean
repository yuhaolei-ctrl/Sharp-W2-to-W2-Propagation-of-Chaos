import SharpWasserstein.RegularizedTrialConvergencePhysicalTime

/-! Scalar measurability, integrability, and L¹ gaps for the actual physical
Fourier ridge energies. The weighted tangent vector may live in a different
Hilbert space at each time; no measurable choice of vector representatives is
assumed. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace SharpWasserstein.VolterraFourier
open WeightedTangent RegularizedTrialConvergence
variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
  [MeasurableSpace (Point n)] [BorelSpace (Point n)]
  (P : ℝ) (μ : Ω → Measure (Point n)) [∀ t,IsFiniteMeasure (μ t)]
  (U : (t : Ω) → gradientClosure (μ t))

/-- Literal finite gradient trial energy at physical period P, using the
proved frequency exhaustion and penalty 1/(j+1). -/
def finiteEnergy (j : ℕ) (t : Ω) : ℝ :=
  RegularizedTrialEnergy.energy
    (RegularizedTrialConvergencePhysical.trial P (μ t) (exhaustion ((Fin n → ℤ) × Bool) j))
    (penalty j) (U t).val

/-- Scalar squared norm of the actual weighted tangent. -/
def totalEnergy (t : Ω) : ℝ := ‖U t‖^2

/-- Actual nonnegative finite trial energy loss. -/
def gap (j : ℕ) (t : Ω) : ℝ := totalEnergy μ U t-finiteEnergy P μ U j t

omit [MeasurableSpace Ω] in
theorem finiteEnergy_nonneg (j : ℕ) (t : Ω) : 0 ≤ finiteEnergy P μ U j t :=
  RegularizedTrialEnergy.energy_nonneg _ _ (penalty_pos j) _

omit [MeasurableSpace Ω] in
theorem finiteEnergy_le (j : ℕ) (t : Ω) : finiteEnergy P μ U j t ≤ totalEnergy μ U t :=
  RegularizedTrialEnergy.energy_le _ _ (penalty_pos j) _

omit [MeasurableSpace Ω] in
theorem gap_bounds (j : ℕ) (t : Ω) : 0 ≤ gap P μ U j t ∧ gap P μ U j t ≤ totalEnergy μ U t :=
  ⟨sub_nonneg.mpr (finiteEnergy_le P μ U j t),sub_le_self _ (finiteEnergy_nonneg P μ U j t)⟩

omit [MeasurableSpace Ω] in
/-- Pointwise recovery is proved for the actual physical Fourier trials. -/
theorem finiteEnergy_tendsto (t : Ω)
    (hU : U t ∈ WeightedPeriodicFourierPhysical.periodicSpace P (μ t)) :
    Tendsto (fun j => finiteEnergy P μ U j t) atTop (𝓝 (totalEnergy μ U t)) :=
  RegularizedTrialConvergencePhysical.energy_tendsto P (μ t) _ _
    (eventually_mem_exhaustion _) penalty_pos penalty_tendsto (U t) hU

/-- Measurability of total energy follows from finite scalar energies and
actual Fourier recovery, not from an assumed measurable vector field. -/
theorem totalEnergy_aestronglyMeasurable (ν : Measure Ω)
    (hU : ∀ᵐ t ∂ν,U t ∈ WeightedPeriodicFourierPhysical.periodicSpace P (μ t))
    (he : ∀ j,AEStronglyMeasurable (finiteEnergy P μ U j) ν) :
    AEStronglyMeasurable (totalEnergy μ U) ν := by
  apply aestronglyMeasurable_of_tendsto_ae atTop he
  filter_upwards [hU] with t ht
  exact finiteEnergy_tendsto P μ U t ht

/-- A coarse integrable scalar domination yields actual integrability. -/
theorem totalEnergy_integrable (ν : Measure Ω)
    (hU : ∀ᵐ t ∂ν,U t ∈ WeightedPeriodicFourierPhysical.periodicSpace P (μ t))
    (he : ∀ j,AEStronglyMeasurable (finiteEnergy P μ U j) ν)
    {B : Ω → ℝ} (hB : Integrable B ν)
    (hbound : ∀ᵐ t ∂ν,totalEnergy μ U t ≤ B t) : Integrable (totalEnergy μ U) ν :=
  hB.mono' (totalEnergy_aestronglyMeasurable P μ U ν hU he) (by
    filter_upwards [hbound] with t ht
    simpa only [totalEnergy,Real.norm_of_nonneg (sq_nonneg ‖U t‖)] using ht)

theorem finiteEnergy_integrable (ν : Measure Ω)
    (hE : Integrable (totalEnergy μ U) ν)
    (he : ∀ j,AEStronglyMeasurable (finiteEnergy P μ U j) ν) (j : ℕ) :
    Integrable (finiteEnergy P μ U j) ν :=
  hE.mono' (he j) (Eventually.of_forall (fun t => by
    rw [Real.norm_of_nonneg (finiteEnergy_nonneg P μ U j t)]
    exact finiteEnergy_le P μ U j t))

theorem gap_integrable (ν : Measure Ω)
    (hE : Integrable (totalEnergy μ U) ν)
    (he : ∀ j,AEStronglyMeasurable (finiteEnergy P μ U j) ν) (j : ℕ) :
    Integrable (gap P μ U j) ν :=
  hE.sub (finiteEnergy_integrable P μ U ν hE he j)

/-- The actual scalar gap vanishes in L¹ under the derived domination. -/
theorem integral_norm_gap_tendsto (ν : Measure Ω)
    (hU : ∀ᵐ t ∂ν,U t ∈ WeightedPeriodicFourierPhysical.periodicSpace P (μ t))
    (he : ∀ j,AEStronglyMeasurable (finiteEnergy P μ U j) ν)
    {B : Ω → ℝ} (hB : Integrable B ν)
    (hbound : ∀ᵐ t ∂ν,totalEnergy μ U t ≤ B t) :
    Tendsto (fun j => ∫ t,‖gap P μ U j t‖ ∂ν) atTop (𝓝 0) :=
  RegularizedTrialConvergencePhysical.canonical_integral_norm_energy_error_tendsto
    P ν μ U hU hB hbound he

/-- Any fixed real coefficient multiplying the genuine trial gap disappears
in L¹. Its sign is irrelevant and no bound uniform in the particle number is
needed for this limiting step. -/
theorem integral_norm_mul_gap_tendsto (ν : Measure Ω) (K : ℝ)
    (hU : ∀ᵐ t ∂ν,U t ∈ WeightedPeriodicFourierPhysical.periodicSpace P (μ t))
    (he : ∀ j,AEStronglyMeasurable (finiteEnergy P μ U j) ν)
    {B : Ω → ℝ} (hB : Integrable B ν)
    (hbound : ∀ᵐ t ∂ν,totalEnergy μ U t ≤ B t) :
    Tendsto (fun j => ∫ t,‖K*gap P μ U j t‖ ∂ν) atTop (𝓝 0) := by
  have h := (integral_norm_gap_tendsto P μ U ν hU he hB hbound).const_mul ‖K‖
  simpa only [norm_mul,integral_const_mul,mul_zero] using h

end SharpWasserstein.VolterraFourier
