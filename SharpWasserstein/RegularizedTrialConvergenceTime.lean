module

public import SharpWasserstein.Compat
public import SharpWasserstein.RegularizedTrialConvergence
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-! Dominated convergence of the genuine regularized energy residuals.
Only scalar energies are assumed measurable. The optimizer vector may live
in a different weighted Hilbert space at each time and needs no measurable
selection or common ambient realization. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace SharpWasserstein.RegularizedTrialConvergence

variable {Ω I : Type*} [MeasurableSpace Ω] {H : Ω → Type*}
  [∀ t,NormedAddCommGroup (H t)] [∀ t,InnerProductSpace ℝ (H t)] [∀ t,CompleteSpace (H t)]

/-- Scalar total energy is measurable because it is the proved pointwise
limit of the actual measurable finite energies. No measurability of `U` is
required even when its Hilbert space depends on time. -/
theorem energy_aestronglyMeasurable
    (ν : Measure Ω) (v : (t : Ω) → I → H t) (U : (t : Ω) → H t)
    (s : ℕ → Finset I) (δ : ℕ → ℝ)
    (hs : ∀ i,∀ᶠ j in atTop,i ∈ s j) (hδpos : ∀ j,0 < δ j)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hU : ∀ᵐ t ∂ν,U t ∈ (Submodule.span ℝ (Set.range (v t))).topologicalClosure)
    (he : ∀ j,AEStronglyMeasurable
      (fun t => RegularizedTrialEnergy.energy (synthesis (v t) (s j)) (δ j) (U t)) ν) :
    AEStronglyMeasurable (fun t => ‖U t‖^2) ν := by
  apply aestronglyMeasurable_of_tendsto_ae atTop he
  filter_upwards [hU] with t ht
  exact energy_tendsto (v t) s δ hs hδpos hδ (U t) ht

/-- Actual finite-atom recovery at each time and an integrable total-energy
bound imply that the scalar energy loss vanishes in `L¹` of time. -/
theorem integral_energy_error_tendsto
    (ν : Measure Ω) (v : (t : Ω) → I → H t) (U : (t : Ω) → H t)
    (s : ℕ → Finset I) (δ : ℕ → ℝ)
    (hs : ∀ i,∀ᶠ j in atTop,i ∈ s j) (hδpos : ∀ j,0 < δ j)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hU : ∀ᵐ t ∂ν,U t ∈ (Submodule.span ℝ (Set.range (v t))).topologicalClosure)
    (hE : Integrable (fun t => ‖U t‖^2) ν)
    (he : ∀ j,AEStronglyMeasurable
      (fun t => RegularizedTrialEnergy.energy (synthesis (v t) (s j)) (δ j) (U t)) ν) :
    Tendsto (fun j => ∫ t,‖U t‖^2-
      RegularizedTrialEnergy.energy (synthesis (v t) (s j)) (δ j) (U t) ∂ν)
      atTop (𝓝 0) := by
  have hconv := tendsto_integral_of_dominated_convergence
    (μ := ν) (f := fun _ => (0 : ℝ)) (fun t => ‖U t‖^2)
    (fun j => hE.aestronglyMeasurable.sub (he j)) hE ?_ ?_
  · simpa only [integral_zero,Pi.sub_apply] using hconv
  · intro j
    filter_upwards [] with t
    have hb := energy_error_bounds (v t) (s j) (hδpos j) (U t)
    rw [Pi.sub_apply,Real.norm_eq_abs,abs_of_nonneg hb.1]
    exact hb.2
  · filter_upwards [hU] with t ht
    have hh := (tendsto_const_nhds (x := ‖U t‖^2)).sub (energy_tendsto (v t) s δ hs hδpos hδ (U t) ht)
    simpa only [sub_self,Pi.sub_apply] using hh

/-- Because the residuals are nonnegative, the same result is literally an
`L¹` norm convergence of the scalar energy error. -/
theorem integral_norm_energy_error_tendsto
    (ν : Measure Ω) (v : (t : Ω) → I → H t) (U : (t : Ω) → H t)
    (s : ℕ → Finset I) (δ : ℕ → ℝ)
    (hs : ∀ i,∀ᶠ j in atTop,i ∈ s j) (hδpos : ∀ j,0 < δ j)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hU : ∀ᵐ t ∂ν,U t ∈ (Submodule.span ℝ (Set.range (v t))).topologicalClosure)
    (hE : Integrable (fun t => ‖U t‖^2) ν)
    (he : ∀ j,AEStronglyMeasurable
      (fun t => RegularizedTrialEnergy.energy (synthesis (v t) (s j)) (δ j) (U t)) ν) :
    Tendsto (fun j => ∫ t,‖‖U t‖^2-
      RegularizedTrialEnergy.energy (synthesis (v t) (s j)) (δ j) (U t)‖ ∂ν)
      atTop (𝓝 0) := by
  have hh := integral_energy_error_tendsto ν v U s δ hs hδpos hδ hU hE he
  convert hh using 1
  funext j
  apply integral_congr_ae
  filter_upwards [] with t
  exact Real.norm_of_nonneg (energy_error_bounds (v t) (s j) (hδpos j) (U t)).1

/-- A coarse integrable upper bound suffices: scalar energy measurability
and the true `L¹` residual limit are both derived from finite trial energies. -/
theorem integral_norm_energy_error_tendsto_of_bound
    (ν : Measure Ω) (v : (t : Ω) → I → H t) (U : (t : Ω) → H t)
    (s : ℕ → Finset I) (δ : ℕ → ℝ)
    (hs : ∀ i,∀ᶠ j in atTop,i ∈ s j) (hδpos : ∀ j,0 < δ j)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hU : ∀ᵐ t ∂ν,U t ∈ (Submodule.span ℝ (Set.range (v t))).topologicalClosure)
    {B : Ω → ℝ} (hB : Integrable B ν) (hbound : ∀ᵐ t ∂ν,‖U t‖^2 ≤ B t)
    (he : ∀ j,AEStronglyMeasurable
      (fun t => RegularizedTrialEnergy.energy (synthesis (v t) (s j)) (δ j) (U t)) ν) :
    Tendsto (fun j => ∫ t,‖‖U t‖^2-
      RegularizedTrialEnergy.energy (synthesis (v t) (s j)) (δ j) (U t)‖ ∂ν)
      atTop (𝓝 0) := by
  have hEm := energy_aestronglyMeasurable ν v U s δ hs hδpos hδ hU he
  have hEi : Integrable (fun t => ‖U t‖^2) ν := hB.mono' hEm (by
    filter_upwards [hbound] with t ht
    simpa only [Real.norm_of_nonneg (sq_nonneg ‖U t‖)] using ht)
  exact integral_norm_energy_error_tendsto ν v U s δ hs hδpos hδ hU hEi he

end SharpWasserstein.RegularizedTrialConvergence
