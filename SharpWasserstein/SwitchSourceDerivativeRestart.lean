module

public import SharpWasserstein.Compat
public import SharpWasserstein.BrownianSemigroup

@[expose] public section

/-! Actual time-dependent restart. Both the pathwise composition and the
law identity are derived from the constructed trajectories and independent
Brownian increments; no Markov or transition-law axiom is assumed. -/
noncomputable section
open Set MeasureTheory
open scoped Interval NNReal ENNReal
namespace SharpWasserstein.SwitchSourceDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Shift the absolute time in the drift, while restarting the forcing at zero. -/
def shiftedDrift (v : ℝ → E → E) (S : ℝ) : ℝ → E → E := fun t x => v (S+t) x

omit [NormedSpace ℝ E] in
theorem shiftedDrift_continuous {v : ℝ → E → E}
    (hv : Continuous (Function.uncurry v)) (S : ℝ) :
    Continuous (Function.uncurry (shiftedDrift v S)) :=
  hv.comp ((continuous_const.add continuous_fst).prodMk continuous_snd)

/-- A genuine time-dependent trajectory restarts at every nonnegative time. -/
theorem trajectory_shift
    {v : ℝ → E → E} {w X : ℝ → E} {x : E} {S T : ℝ}
    (h : FiniteAdditiveTrajectory v w x (S+T) X)
    (hS : 0 ≤ S) (hT : 0 ≤ T) :
    FiniteAdditiveTrajectory (shiftedDrift v S) (fun t => w (S+t)-w S) (X S) T
      (fun t => X (S+t)) := by
  have hm : MapsTo (fun t : ℝ => S+t) (Icc 0 T) (Icc 0 (S+T)) := by
    intro t ht
    exact ⟨add_nonneg hS ht.1,add_le_add_right ht.2 S⟩
  refine ⟨h.continuous.comp (continuous_const.add continuous_id).continuousOn hm,
    h.driftContinuous.comp (continuous_const.add continuous_id).continuousOn hm, ?_⟩
  intro t ht
  have hs : S ∈ Icc 0 (S+T) := ⟨hS,le_add_of_nonneg_right hT⟩
  have hst : S+t ∈ Icc 0 (S+T) := hm ht
  have h₁ : IntervalIntegrable (fun u => v u (X u)) volume 0 S :=
    (h.driftContinuous.mono (Icc_subset_Icc_right hs.2)).intervalIntegrable_of_Icc hS
  have h₂ : IntervalIntegrable (fun u => v u (X u)) volume S (S+t) :=
    (h.driftContinuous.mono (Icc_subset_Icc hS hst.2)).intervalIntegrable_of_Icc
      (le_add_of_nonneg_right ht.1)
  have hi := intervalIntegral.integral_add_adjacent_intervals h₁ h₂
  have hshift := intervalIntegral.integral_comp_add_left (a := 0) (b := t)
    (fun u => v u (X u)) S
  simp only [add_zero] at hshift
  change X (S+t) = X S+(∫ u in (0:ℝ)..t,v (S+u) (X (S+u)))+(w (S+t)-w S)
  rw [hshift,h.equation (S+t) hst,h.equation S hs,← hi]
  abel

section Flow
variable [CompleteSpace E]
  {v : ℝ → E → E} {M K : ℝ≥0}
  (hv : Continuous (Function.uncurry v))
  (hb : ∀ t x, ‖v t x‖ ≤ M) (hl : ∀ t, LipschitzWith K (v t))

/-- Exact composition of the selected flow with the actual time-shifted drift. -/
theorem flow_add_shift {S T : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T)
    (x : E) (w : C(Icc 0 (S+T),E)) :
    BoundedFlow.flow hv hb hl (add_nonneg hS hT) x w (S+T) =
      BoundedFlow.flow (shiftedDrift_continuous hv S)
        (fun t => hb (S+t)) (fun t => hl (S+t)) hT
        (BoundedFlow.flow hv hb hl hS x
          (BoundedFlow.restrictPath (le_add_of_nonneg_right hT) w) S)
        (BoundedFlow.shiftPath hS hT w) T := by
  let X := BoundedFlow.flow hv hb hl (add_nonneg hS hT) x w
  have hs := trajectory_shift (BoundedFlow.flow_trajectory hv hb hl (add_nonneg hS hT) x w) hS hT
  have hs' : FiniteAdditiveTrajectory (shiftedDrift v S)
      (BoundedFlow.noiseExtension hT (BoundedFlow.shiftPath hS hT w)) (X S) T
      (fun t => X (S+t)) := by
    apply hs.congr_forcing
    intro t ht
    have hst : S+t ∈ Icc 0 (S+T) := ⟨add_nonneg hS ht.1,add_le_add_right ht.2 S⟩
    simp only [BoundedFlow.noiseExtension,projIcc_of_mem _ hst,
      projIcc_of_mem _ (show S ∈ Icc 0 (S+T) from ⟨hS,le_add_of_nonneg_right hT⟩),
      projIcc_of_mem _ ht,BoundedFlow.shiftPath,ContinuousMap.coe_mk]
  have hr := BoundedFlow.flow_restrict hv hb hl hS (le_add_of_nonneg_right hT) x w
    (show S ∈ Icc 0 S from ⟨hS,le_rfl⟩)
  rw [hr]
  exact (BoundedFlow.flow_eq_of_trajectory (shiftedDrift_continuous hv S)
    (fun t => hb (S+t)) (fun t => hl (S+t)) hT (X S)
      (BoundedFlow.shiftPath hS hT w) hs' ⟨hT,le_rfl⟩).symm

end Flow

section Brownian
variable {d N : ℕ} {v : ℝ → Configuration d N → Configuration d N} {M K : ℝ≥0}
  (hv : Continuous (Function.uncurry v))
  (hb : ∀ t x, ‖v t x‖ ≤ M) (hl : ∀ t, LipschitzWith K (v t))

/-- Restart the actual sqrt(2)-Brownian law under a time-dependent drift. -/
theorem brownianLaw_add_shift {S T : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T)
    (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ] :
    BrownianFlow.law hv hb hl (add_nonneg hS hT) μ (S+T) =
      BrownianFlow.law (shiftedDrift_continuous hv S)
        (fun t => hb (S+t)) (fun t => hl (S+t)) hT
        (BrownianFlow.law hv hb hl hS μ S) T := by
  let ξS := BrownianNoise.configurationLaw d N S
  let ξT := BrownianNoise.configurationLaw d N T
  let ξST := BrownianNoise.configurationLaw d N (S+T)
  let fS : Configuration d N × C(Icc 0 S,Configuration d N) → Configuration d N :=
    fun p => BoundedFlow.flow hv hb hl hS p.1 p.2 S
  let fT : Configuration d N × C(Icc 0 T,Configuration d N) → Configuration d N :=
    fun p => BoundedFlow.flow (shiftedDrift_continuous hv S)
      (fun t => hb (S+t)) (fun t => hl (S+t)) hT p.1 p.2 T
  have hfS : Measurable fS := (BoundedFlow.flow_continuous hv hb hl hS ⟨hS,le_rfl⟩).measurable
  have hfT : Measurable fT := (BoundedFlow.flow_continuous (shiftedDrift_continuous hv S)
    (fun t => hb (S+t)) (fun t => hl (S+t)) hT ⟨hT,le_rfl⟩).measurable
  let F : Configuration d N × C(Icc 0 S,Configuration d N) × C(Icc 0 T,Configuration d N) →
      Configuration d N := fun p => fT (fS (p.1,p.2.1),p.2.2)
  have hF : Measurable F := hfT.comp ((hfS.comp
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
      (measurable_snd.comp measurable_snd))
  let R := Prod.map (id : Configuration d N → Configuration d N)
    (BoundedFlow.splitPath (E := Configuration d N) hS hT)
  have hR : MeasurePreserving R (μ.prod ξST) (μ.prod (ξS.prod ξT)) :=
    (MeasurePreserving.id μ).prod (BrownianNoise.configurationLaw_split d N hS hT)
  have hsplit : BrownianFlow.law hv hb hl (add_nonneg hS hT) μ (S+T) =
      (μ.prod (ξS.prod ξT)).map F := by
    rw [← hR.map_eq,Measure.map_map hF hR.measurable]
    unfold BrownianFlow.law
    congr 1
    funext p
    exact flow_add_shift hv hb hl hS hT p.1 p.2
  have hfirst : MeasurePreserving fS (μ.prod ξS) (BrownianFlow.law hv hb hl hS μ S) := ⟨hfS,rfl⟩
  have hp := hfirst.prod (MeasurePreserving.id ξT)
  rw [hsplit,← (measurePreserving_prodAssoc μ ξS ξT).map_eq,
    Measure.map_map hF MeasurableEquiv.prodAssoc.measurable]
  change _ = Measure.map fT ((BrownianFlow.law hv hb hl hS μ S).prod ξT)
  rw [← hp.map_eq,Measure.map_map hfT hp.measurable]
  rfl

/-- The global time-dependent law satisfies the same genuine restart identity. -/
theorem brownianGlobalLaw_add_shift {S T : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T)
    (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ] :
    BrownianFlow.globalLaw hv hb hl μ (S+T) =
      BrownianFlow.globalLaw (shiftedDrift_continuous hv S)
        (fun t => hb (S+t)) (fun t => hl (S+t))
        (BrownianFlow.globalLaw hv hb hl μ S) T := by
  letI := BrownianFlow.globalLaw_probability hv hb hl μ hS
  rw [BrownianFlow.globalLaw_eq hv hb hl (add_nonneg hS hT) μ ⟨add_nonneg hS hT,le_rfl⟩,
    BrownianFlow.globalLaw_eq (shiftedDrift_continuous hv S)
      (fun t => hb (S+t)) (fun t => hl (S+t)) hT
      (BrownianFlow.globalLaw hv hb hl μ S) ⟨hT,le_rfl⟩,
    BrownianFlow.globalLaw_eq hv hb hl hS μ ⟨hS,le_rfl⟩]
  exact brownianLaw_add_shift hv hb hl hS hT μ

end Brownian
end SharpWasserstein.SwitchSourceDerivative
