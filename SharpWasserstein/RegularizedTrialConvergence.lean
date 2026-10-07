module

public import SharpWasserstein.Compat
public import SharpWasserstein.RegularizedTrialEnergy
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Order.Filter.Finite

@[expose] public section

/-! Genuine finite-coefficient recovery for regularized trial energies.
The approximation comes from membership in the closed span of actual atoms.
A fixed finitely supported coefficient vector is extended by zero; its norm
is unchanged as the finite trial family grows. No energy convergence premise
or measurable choice of an optimizer is used. -/
noncomputable section
open Set Filter
open scoped Topology InnerProductSpace BigOperators
namespace SharpWasserstein.RegularizedTrialConvergence
variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The actual coefficient synthesis operator of a finite atom family. -/
def synthesis (v : I → H) (s : Finset I) : EuclideanSpace ℝ s →L[ℝ] H :=
  ∑ i : s,(EuclideanSpace.proj i).smulRight (v i)

theorem synthesis_apply (v : I → H) (s : Finset I) (c : EuclideanSpace ℝ s) :
    synthesis v s c = ∑ i : s,c i • v i := by
  simp only [synthesis,sum_apply,ContinuousLinearMap.smulRight_apply]
  rfl

/-- A fixed finitely supported coefficient vector, read on a larger finite set. -/
def coefficients (s : Finset I) (c : I →₀ ℝ) : EuclideanSpace ℝ s :=
  WithLp.toLp 2 (fun i => c i)

theorem synthesis_coefficients (v : I → H) (s : Finset I) (c : I →₀ ℝ)
    (hs : c.support ⊆ s) :
    synthesis v s (coefficients s c) = c.sum (fun i r => r • v i) := by
  rw [synthesis_apply]
  change (∑ i : s,c i • v i) = _
  rw [Finset.sum_coe_sort s (fun i : I => c i • v i)]
  exact (c.sum_of_support_subset hs (fun i r => r • v i) (fun _ _ => zero_smul _ _)).symm

/-- Zero extension preserves the exact Euclidean coefficient norm. -/
theorem coefficients_norm_sq (s : Finset I) (c : I →₀ ℝ) (hs : c.support ⊆ s) :
    ‖coefficients s c‖^2 = c.sum (fun _ r => ‖r‖^2) := by
  rw [PiLp.norm_sq_eq_of_L2]
  change (∑ i : s,‖c i‖^2) = _
  rw [Finset.sum_coe_sort s (fun i : I => ‖c i‖^2)]
  exact (c.sum_of_support_subset hs (fun _ r => ‖r‖^2) (fun _ _ => by simp)).symm

/-- Closed-span membership supplies an actual finite coefficient recovery,
with an arbitrarily small squared approximation error. -/
theorem exists_finite_recovery (v : I → H) {U : H}
    (hU : U ∈ (Submodule.span ℝ (Set.range v)).topologicalClosure)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ c : I →₀ ℝ,‖U-c.sum (fun i r => r • v i)‖^2 < ε := by
  have hu : U ∈ closure (Submodule.span ℝ (Set.range v) : Set H) := by
    rw [← SetLike.mem_coe,Submodule.topologicalClosure_coe] at hU
    exact hU
  obtain ⟨W,hW,hd⟩ := Metric.mem_closure_iff.mp hu (Real.sqrt ε) (Real.sqrt_pos.mpr hε)
  obtain ⟨c,rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hW
  refine ⟨c,?_⟩
  rw [dist_eq_norm] at hd
  have hs := Real.sq_sqrt hε.le
  nlinarith [norm_nonneg (U-c.sum (fun i r => r • v i)),Real.sqrt_nonneg ε]

variable [CompleteSpace H]

/-- Dense actual finite atoms plus a vanishing coefficient penalty give the
true energy limit. The finite sets need only eventually contain each atom;
monotone exhausting sequences are a special case. -/
theorem energy_tendsto {J : Type*} {l : Filter J}
    (v : I → H) (s : J → Finset I) (δ : J → ℝ)
    (hs : ∀ i,∀ᶠ j in l,i ∈ s j) (hδpos : ∀ j,0 < δ j)
    (hδ : Tendsto δ l (𝓝 0)) (U : H)
    (hU : U ∈ (Submodule.span ℝ (Set.range v)).topologicalClosure) :
    Tendsto (fun j => RegularizedTrialEnergy.energy (synthesis v (s j)) (δ j) U) l (𝓝 (‖U‖^2)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨c,hc⟩ := exists_finite_recovery v hU (half_pos hε)
  have hsupp : ∀ᶠ j in l,c.support ⊆ s j := by
    exact (Filter.eventually_all_finset c.support).mpr (fun i _ => hs i)
  have hp : Tendsto (fun j => δ j*c.sum (fun _ r => ‖r‖^2)) l (𝓝 0) := by
    simpa only [zero_mul] using hδ.mul_const (c.sum (fun _ r => ‖r‖^2))
  have hpε : ∀ᶠ j in l,δ j*c.sum (fun _ r => ‖r‖^2) < ε/2 :=
    (tendsto_order.mp hp).2 _ (half_pos hε)
  filter_upwards [hsupp,hpε] with j hsj hpj
  have hgap := RegularizedTrialEnergy.energy_gap_le_trial (synthesis v (s j)) (δ j)
    (hδpos j) U (coefficients (s j) c)
  rw [synthesis_coefficients v (s j) c hsj,coefficients_norm_sq (s j) c hsj] at hgap
  have hupper := RegularizedTrialEnergy.energy_le (synthesis v (s j)) (δ j) (hδpos j) U
  rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hupper)]
  linarith

/-- The actual regularized residual always lies between zero and the total
energy; this is the bound used in dominated time convergence. -/
theorem energy_error_bounds (v : I → H) (s : Finset I) {δ : ℝ} (hδ : 0 < δ) (U : H) :
    0 ≤ ‖U‖^2-RegularizedTrialEnergy.energy (synthesis v s) δ U ∧
      ‖U‖^2-RegularizedTrialEnergy.energy (synthesis v s) δ U ≤ ‖U‖^2 :=
  ⟨sub_nonneg.mpr (RegularizedTrialEnergy.energy_le _ _ hδ U),
    sub_le_self _ (RegularizedTrialEnergy.energy_nonneg _ _ hδ U)⟩

end SharpWasserstein.RegularizedTrialConvergence
