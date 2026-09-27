import SharpWasserstein.RegularizedTrialConvergenceTime
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Logic.Encodable.Basic

/-! An actual countable nested trial exhaustion and strictly positive
vanishing regularization, so the sequential recovery theorem needs no supplied
choice of a dense approximation sequence. -/
noncomputable section
open Filter Set
open scoped Topology
namespace SharpWasserstein.RegularizedTrialConvergence
variable (I : Type*) [Encodable I]

/-- The first finitely many encoded atoms, retaining their original values. -/
def exhaustion (j : ℕ) : Finset I :=
  (Finset.range j).preimage Encodable.encode Encodable.encode_injective.injOn

theorem mem_exhaustion (i : I) (j : ℕ) :
    i ∈ exhaustion I j ↔ Encodable.encode i < j := by
  simp only [exhaustion,Finset.mem_preimage,Finset.mem_range]

theorem exhaustion_monotone : Monotone (exhaustion I) := by
  intro j k hjk i hi
  exact (mem_exhaustion I i k).mpr ((mem_exhaustion I i j).mp hi |>.trans_le hjk)

theorem eventually_mem_exhaustion (i : I) : ∀ᶠ j in atTop,i ∈ exhaustion I j := by
  simpa only [mem_exhaustion] using eventually_gt_atTop (Encodable.encode i)

/-- A definite positive coefficient penalty at every finite stage. -/
def penalty (j : ℕ) : ℝ := 1/((j:ℝ)+1)

theorem penalty_pos (j : ℕ) : 0 < penalty j := by
  unfold penalty
  positivity

theorem penalty_tendsto : Tendsto penalty atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

variable {I} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Genuine regularized finite energies converge along this explicit nested
exhaustion; only membership in the actual closed atom span remains. -/
theorem canonical_energy_tendsto (v : I → H) (U : H)
    (hU : U ∈ (Submodule.span ℝ (Set.range v)).topologicalClosure) :
    Tendsto (fun j => RegularizedTrialEnergy.energy (synthesis v (exhaustion I j)) (penalty j) U)
      atTop (𝓝 (‖U‖^2)) :=
  energy_tendsto v (exhaustion I) penalty (eventually_mem_exhaustion I) penalty_pos penalty_tendsto U hU

end SharpWasserstein.RegularizedTrialConvergence
