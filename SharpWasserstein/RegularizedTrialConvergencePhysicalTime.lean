module

public import SharpWasserstein.Compat
public import SharpWasserstein.RegularizedTrialConvergencePhysical
public import SharpWasserstein.RegularizedTrialConvergenceSequence

@[expose] public section

/-! Actual `L¹` recovery for physical Fourier trial energies along varying
finite carrying measures. Only the finite scalar energies must be measurable;
the total scalar energy is proved measurable from their genuine limit. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace SharpWasserstein.RegularizedTrialConvergencePhysical
open WeightedTangent RegularizedTrialConvergence

variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
  [MeasurableSpace (Point n)] [BorelSpace (Point n)]

/-- Scalar residuals of the literal finite physical Fourier gradient trials
vanish in `L¹` under a coarse integrable energy bound. No optimizer field
measurability is assumed or inferred. -/
theorem integral_norm_energy_error_tendsto_of_bound
    (P : ℝ) (ν : Measure Ω) (μ : Ω → Measure (Point n)) [∀ t,IsFiniteMeasure (μ t)]
    (U : (t : Ω) → gradientClosure (μ t))
    (s : ℕ → Finset ((Fin n → ℤ) × Bool)) (δ : ℕ → ℝ)
    (hs : ∀ p,∀ᶠ j in atTop,p ∈ s j) (hδpos : ∀ j,0 < δ j)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hU : ∀ᵐ t ∂ν,U t ∈ WeightedPeriodicFourierPhysical.periodicSpace P (μ t))
    {B : Ω → ℝ} (hB : Integrable B ν) (hbound : ∀ᵐ t ∂ν,‖U t‖^2 ≤ B t)
    (he : ∀ j,AEStronglyMeasurable
      (fun t => RegularizedTrialEnergy.energy (trial P (μ t) (s j)) (δ j) (U t).val) ν) :
    Tendsto (fun j => ∫ t,‖‖U t‖^2-
      RegularizedTrialEnergy.energy (trial P (μ t) (s j)) (δ j) (U t).val‖ ∂ν)
      atTop (𝓝 0) := by
  have hU' : ∀ᵐ t ∂ν,(U t).val ∈
      (Submodule.span ℝ (Set.range (atomVector P (μ t)))).topologicalClosure :=
    hU.mono (fun t ht => periodic_mem_atomClosure P (μ t) ht)
  have he' (j : ℕ) : AEStronglyMeasurable
      (fun t => RegularizedTrialEnergy.energy (synthesis (atomVector P (μ t)) (s j)) (δ j) (U t).val) ν := by
    simpa only [trial_eq_synthesis] using he j
  have hb' : ∀ᵐ t ∂ν,‖(U t).val‖^2 ≤ B t := by
    simpa only [Submodule.norm_coe] using hbound
  have hh := RegularizedTrialConvergence.integral_norm_energy_error_tendsto_of_bound ν
    (fun t => atomVector P (μ t)) (fun t => (U t).val) s δ hs hδpos hδ hU' hB hb' he'
  simpa only [trial_eq_synthesis,Submodule.norm_coe] using hh

/-- A fully specified nested physical Fourier recovery sequence with
penalty `1/(j+1)` has the same genuine scalar `L¹` error convergence. -/
theorem canonical_integral_norm_energy_error_tendsto
    (P : ℝ) (ν : Measure Ω) (μ : Ω → Measure (Point n)) [∀ t,IsFiniteMeasure (μ t)]
    (U : (t : Ω) → gradientClosure (μ t))
    (hU : ∀ᵐ t ∂ν,U t ∈ WeightedPeriodicFourierPhysical.periodicSpace P (μ t))
    {B : Ω → ℝ} (hB : Integrable B ν) (hbound : ∀ᵐ t ∂ν,‖U t‖^2 ≤ B t)
    (he : ∀ j,AEStronglyMeasurable
      (fun t => RegularizedTrialEnergy.energy
        (trial P (μ t) (exhaustion ((Fin n → ℤ) × Bool) j)) (penalty j) (U t).val) ν) :
    Tendsto (fun j => ∫ t,‖‖U t‖^2-
      RegularizedTrialEnergy.energy (trial P (μ t) (exhaustion ((Fin n → ℤ) × Bool) j))
        (penalty j) (U t).val‖ ∂ν) atTop (𝓝 0) :=
  integral_norm_energy_error_tendsto_of_bound P ν μ U _ _
    (eventually_mem_exhaustion _) penalty_pos penalty_tendsto hU hB hbound he

end SharpWasserstein.RegularizedTrialConvergencePhysical
