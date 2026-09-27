import SharpWasserstein.BoundedFlow

/-! Causality and horizon consistency of the constructed additive solution.
These remove any dependence of the selected solution on future input values. -/

noncomputable section
open Set
open scoped NNReal

namespace SharpWasserstein

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem FiniteAdditiveTrajectory.restrict_horizon
    {v : ℝ → E → E} {w X : ℝ → E} {x : E} {S T : ℝ}
    (h : FiniteAdditiveTrajectory v w x T X) (hST : S ≤ T) :
    FiniteAdditiveTrajectory v w x S X :=
  ⟨h.continuous.mono (Icc_subset_Icc_right hST),
    h.driftContinuous.mono (Icc_subset_Icc_right hST),
    fun t ht => h.equation t ⟨ht.1,ht.2.trans hST⟩⟩

theorem FiniteAdditiveTrajectory.congr_forcing
    {v : ℝ → E → E} {w z X : ℝ → E} {x : E} {T : ℝ}
    (h : FiniteAdditiveTrajectory v w x T X) (hwz : ∀ t ∈ Icc 0 T, w t = z t) :
    FiniteAdditiveTrajectory v z x T X := by
  refine ⟨h.continuous,h.driftContinuous,fun t ht => ?_⟩
  rw [h.equation t ht,hwz t ht]

theorem FiniteAdditiveTrajectory.causal_eq [CompleteSpace E]
    {v : ℝ → E → E} {w z X Y : ℝ → E} {x : E} {S T t : ℝ} {K : ℝ≥0}
    (hv : ∀ s, LipschitzWith K (v s))
    (hX : FiniteAdditiveTrajectory v w x S X) (hY : FiniteAdditiveTrajectory v z x T Y)
    (htS : t ∈ Icc 0 S) (htT : t ∈ Icc 0 T)
    (hwz : ∀ s ∈ Icc 0 t, w s = z s) : X t = Y t := by
  have hy := (hY.restrict_horizon htT.2).congr_forcing (fun s hs => (hwz s hs).symm)
  have h := (hX.restrict_horizon htS.2).stability (fun s _ => hv s) hy ⟨htS.1,le_rfl⟩
  simpa only [sub_self,norm_zero,zero_mul,norm_le_zero_iff,sub_eq_zero] using h

namespace BoundedFlow

def restrictPath {S T : ℝ} (hST : S ≤ T) (w : C(Icc 0 T,E)) : C(Icc 0 S,E) :=
  ⟨fun t => w ⟨t, t.property.1,t.property.2.trans hST⟩,
    w.continuous.comp (continuous_subtype_val.subtype_mk _)⟩

theorem flow_restrict [CompleteSpace E]
    {v : ℝ → E → E} {M K : ℝ≥0}
    (hv : Continuous (Function.uncurry v)) (hb : ∀ t x, ‖v t x‖ ≤ M)
    (hl : ∀ t, LipschitzWith K (v t)) {S T : ℝ}
    (hS : 0 ≤ S) (hST : S ≤ T) (x : E) (w : C(Icc 0 T,E))
    {t : ℝ} (ht : t ∈ Icc 0 S) :
    flow hv hb hl hS x (restrictPath hST w) t = flow hv hb hl (hS.trans hST) x w t := by
  apply FiniteAdditiveTrajectory.causal_eq hl
    (flow_trajectory hv hb hl hS x (restrictPath hST w))
    (flow_trajectory hv hb hl (hS.trans hST) x w) ht ⟨ht.1,ht.2.trans hST⟩
  intro s hs
  have hsS : s ∈ Icc 0 S := ⟨hs.1,hs.2.trans ht.2⟩
  have hsT : s ∈ Icc 0 T := ⟨hs.1,hsS.2.trans hST⟩
  simp only [noiseExtension,projIcc_of_mem _ hsS,projIcc_of_mem _ hsT,restrictPath,ContinuousMap.coe_mk]

end BoundedFlow
end SharpWasserstein
