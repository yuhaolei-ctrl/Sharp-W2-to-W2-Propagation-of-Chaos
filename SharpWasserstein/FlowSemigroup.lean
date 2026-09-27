import SharpWasserstein.BrownianSplit

/-! Pathwise composition of the actual bounded autonomous additive flow.
The driving path is split into its past and its restarted increment path. -/
noncomputable section
open Set MeasureTheory
open scoped Interval NNReal
namespace SharpWasserstein
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Shifting an autonomous integral trajectory gives a trajectory started at
its current state and forced by the shifted increments of the original path. -/
theorem FiniteAdditiveTrajectory.shift_autonomous
    {b : E → E} {w X : ℝ → E} {x : E} {S T : ℝ}
    (h : FiniteAdditiveTrajectory (fun _ => b) w x (S+T) X)
    (hS : 0 ≤ S) (hT : 0 ≤ T) :
    FiniteAdditiveTrajectory (fun _ => b) (fun t => w (S+t)-w S) (X S) T
      (fun t => X (S+t)) := by
  have hm : MapsTo (fun t : ℝ => S+t) (Icc 0 T) (Icc 0 (S+T)) := by
    intro t ht
    exact ⟨add_nonneg hS ht.1,add_le_add_right ht.2 S⟩
  refine ⟨h.continuous.comp (continuous_const.add continuous_id).continuousOn hm,
    h.driftContinuous.comp (continuous_const.add continuous_id).continuousOn hm, ?_⟩
  intro t ht
  have hs : S ∈ Icc 0 (S+T) := ⟨hS,le_add_of_nonneg_right hT⟩
  have hst : S+t ∈ Icc 0 (S+T) := hm ht
  have h₁ : IntervalIntegrable (fun u => b (X u)) volume 0 S :=
    (h.driftContinuous.mono (Icc_subset_Icc_right hs.2)).intervalIntegrable_of_Icc hS
  have h₂ : IntervalIntegrable (fun u => b (X u)) volume S (S+t) :=
    (h.driftContinuous.mono (Icc_subset_Icc hS hst.2)).intervalIntegrable_of_Icc
      (le_add_of_nonneg_right ht.1)
  have hi := intervalIntegral.integral_add_adjacent_intervals h₁ h₂
  have hshift := intervalIntegral.integral_comp_add_left (a := 0) (b := t) (fun u => b (X u)) S
  simp only [add_zero] at hshift
  rw [hshift,h.equation (S+t) hst,h.equation S hs]
  change x+(∫ u in 0..S+t,b (X u))+w (S+t) =
    x+(∫ u in 0..S,b (X u))+w S+(∫ u in S..S+t,b (X u))+(w (S+t)-w S)
  rw [← hi]
  abel

namespace BoundedFlow
variable [CompleteSpace E]
variable {b : E → E} {M K : ℝ≥0}
  (hv : Continuous (Function.uncurry (fun _ : ℝ => b)))
  (hb : ∀ _ : ℝ, ∀ x, ‖b x‖ ≤ M) (hl : ∀ _ : ℝ, LipschitzWith K b)

/-- Actual endpoint composition, proved from the integral equation and pathwise
uniqueness. No probability or Markov hypothesis is used. -/
theorem flow_add {S T : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T)
    (x : E) (w : C(Icc 0 (S+T),E)) :
    flow hv hb hl (add_nonneg hS hT) x w (S+T) =
    flow hv hb hl hT
      (flow hv hb hl hS x (restrictPath (le_add_of_nonneg_right hT) w) S)
      (shiftPath hS hT w) T := by
  let X := flow hv hb hl (add_nonneg hS hT) x w
  have hs := (flow_trajectory hv hb hl (add_nonneg hS hT) x w).shift_autonomous hS hT
  have hs' : FiniteAdditiveTrajectory (fun _ : ℝ => b)
      (noiseExtension hT (shiftPath hS hT w)) (X S) T (fun t => X (S+t)) := by
    apply hs.congr_forcing
    intro t ht
    have hst : S+t ∈ Icc 0 (S+T) := ⟨add_nonneg hS ht.1,add_le_add_right ht.2 S⟩
    simp only [noiseExtension,projIcc_of_mem _ hst,
      projIcc_of_mem _ (show S ∈ Icc 0 (S+T) from ⟨hS,le_add_of_nonneg_right hT⟩),
      projIcc_of_mem _ ht,shiftPath,ContinuousMap.coe_mk]
  have hr := flow_restrict hv hb hl hS (le_add_of_nonneg_right hT) x w
    (show S ∈ Icc 0 S from ⟨hS,le_rfl⟩)
  rw [hr]
  exact (flow_eq_of_trajectory hv hb hl hT (X S) (shiftPath hS hT w) hs' ⟨hT,le_rfl⟩).symm

end BoundedFlow
end SharpWasserstein
