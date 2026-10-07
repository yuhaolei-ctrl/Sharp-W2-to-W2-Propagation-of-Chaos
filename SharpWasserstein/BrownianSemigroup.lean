module

public import SharpWasserstein.Compat
public import SharpWasserstein.FlowSemigroup
public import SharpWasserstein.BrownianFlow

@[expose] public section

/-! The Markov semigroup identity for the actually constructed autonomous
Brownian flow, obtained from independent path increments and pathwise flow
composition. -/
noncomputable section
open Set MeasureTheory
open scoped NNReal ENNReal
namespace SharpWasserstein.BrownianFlow
variable {d N : ℕ} {b : Configuration d N → Configuration d N} {M K : ℝ≥0}
  (hv : Continuous (Function.uncurry (fun _ : ℝ => b)))
  (hb : ∀ _ : ℝ, ∀ x, ‖b x‖ ≤ M) (hl : ∀ _ : ℝ, LipschitzWith K b)

/-- The autonomous finite-horizon law at `S+T` is the law over the second
interval started from the actual law at `S`. -/
theorem law_add {S T : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T)
    (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ] :
    law hv hb hl (add_nonneg hS hT) μ (S+T) =
      law hv hb hl hT (law hv hb hl hS μ S) T := by
  let ξS := BrownianNoise.configurationLaw d N S
  let ξT := BrownianNoise.configurationLaw d N T
  let ξST := BrownianNoise.configurationLaw d N (S+T)
  let fS : Configuration d N × C(Icc 0 S,Configuration d N) → Configuration d N :=
    fun p => BoundedFlow.flow hv hb hl hS p.1 p.2 S
  let fT : Configuration d N × C(Icc 0 T,Configuration d N) → Configuration d N :=
    fun p => BoundedFlow.flow hv hb hl hT p.1 p.2 T
  have hfS : Measurable fS := (BoundedFlow.flow_continuous hv hb hl hS ⟨hS,le_rfl⟩).measurable
  have hfT : Measurable fT := (BoundedFlow.flow_continuous hv hb hl hT ⟨hT,le_rfl⟩).measurable
  let F : Configuration d N × C(Icc 0 S,Configuration d N) × C(Icc 0 T,Configuration d N) →
      Configuration d N := fun p => fT (fS (p.1,p.2.1),p.2.2)
  have hF : Measurable F := hfT.comp ((hfS.comp
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
      (measurable_snd.comp measurable_snd))
  let R := Prod.map (id : Configuration d N → Configuration d N)
    (BoundedFlow.splitPath (E := Configuration d N) hS hT)
  have hR : MeasurePreserving R (μ.prod ξST) (μ.prod (ξS.prod ξT)) :=
    (MeasurePreserving.id μ).prod (BrownianNoise.configurationLaw_split d N hS hT)
  have hsplit : law hv hb hl (add_nonneg hS hT) μ (S+T) =
      (μ.prod (ξS.prod ξT)).map F := by
    rw [← hR.map_eq,Measure.map_map hF hR.measurable]
    unfold law
    congr 1
    funext p
    exact BoundedFlow.flow_add hv hb hl hS hT p.1 p.2
  have hfirst : MeasurePreserving fS (μ.prod ξS) (law hv hb hl hS μ S) := ⟨hfS,rfl⟩
  have hp := hfirst.prod (MeasurePreserving.id ξT)
  rw [hsplit,← (measurePreserving_prodAssoc μ ξS ξT).map_eq,
    Measure.map_map hF MeasurableEquiv.prodAssoc.measurable]
  change _ = (Measure.map fT ((law hv hb hl hS μ S).prod ξT))
  rw [← hp.map_eq,Measure.map_map hfT hp.measurable]
  rfl

/-- The actual autonomous global Brownian laws form a semigroup for every
probability initial law, including zero time and without a moment assumption. -/
theorem globalLaw_add {S T : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T)
    (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ] :
    globalLaw hv hb hl μ (S+T) =
      globalLaw hv hb hl (globalLaw hv hb hl μ S) T := by
  letI := globalLaw_probability hv hb hl μ hS
  rw [globalLaw_eq hv hb hl (add_nonneg hS hT) μ ⟨add_nonneg hS hT,le_rfl⟩,
    globalLaw_eq hv hb hl hT (globalLaw hv hb hl μ S) ⟨hT,le_rfl⟩,
    globalLaw_eq hv hb hl hS μ ⟨hS,le_rfl⟩]
  exact law_add hv hb hl hS hT μ


/-- The transition operator of the constructed process satisfies the exact
iterated-expectation formula for every bounded continuous real test. -/
theorem globalLaw_add_integral {S T : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T)
    (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    {φ : Configuration d N → ℝ} (hφ : Continuous φ) {B : ℝ}
    (hB : ∀ x, ‖φ x‖ ≤ B) :
    (∫ z, φ z ∂globalLaw hv hb hl μ (S+T)) =
      ∫ x, (∫ z, φ z ∂globalLaw hv hb hl (Measure.dirac x) T)
        ∂globalLaw hv hb hl μ S := by
  let ν := globalLaw hv hb hl μ S
  letI : IsProbabilityMeasure ν := globalLaw_probability hv hb hl μ hS
  have hflow := BoundedFlow.flow_continuous hv hb hl hT (show T ∈ Icc 0 T from ⟨hT,le_rfl⟩)
  have hcomp : Integrable
      (fun p : Configuration d N × C(Icc 0 T,Configuration d N) =>
        φ (BoundedFlow.flow hv hb hl hT p.1 p.2 T))
      (ν.prod (BrownianNoise.configurationLaw d N T)) :=
    Integrable.of_bound (hφ.comp hflow).aestronglyMeasurable B
      (Filter.Eventually.of_forall (fun p => hB _))
  rw [globalLaw_add hv hb hl hS hT μ,
    globalLaw_eq hv hb hl hT ν ⟨hT,le_rfl⟩,
    law_integral_eq hv hb hl hT ν hφ ⟨hT,le_rfl⟩,
    integral_prod _ hcomp]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  dsimp only
  rw [globalLaw_eq hv hb hl hT (Measure.dirac x) ⟨hT,le_rfl⟩,
    law_integral_eq hv hb hl hT (Measure.dirac x) hφ ⟨hT,le_rfl⟩,
    Measure.dirac_prod]
  exact (integral_map measurable_prodMk_left.aemeasurable (hφ.comp hflow).aestronglyMeasurable).symm

end SharpWasserstein.BrownianFlow

namespace SharpWasserstein.BrownianParticle
variable {d N : ℕ} {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
  (hN : 0 < N) (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
  (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)

/-- The actual self-inclusive interacting particle laws form an autonomous
semigroup. The initial law can be any probability measure. -/
theorem globalLaw_add {S T : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T)
    (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ] :
    globalLaw hN hb hbound hM hL₁ hL₂ μ (S+T) =
      globalLaw hN hb hbound hM hL₁ hL₂
        (globalLaw hN hb hbound hM hL₁ hL₂ μ S) T :=
  BrownianFlow.globalLaw_add
    ((particleDrift_lipschitz hN hb hbound hL₁ hL₂).continuous.comp continuous_snd)
    (M := ⟨M,hM⟩) (fun _ x => particleDrift_norm_bound hN hbound hM x)
    (fun _ => particleDrift_lipschitz hN hb hbound hL₁ hL₂) hS hT μ

theorem globalLaw_add_integral {S T : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T)
    (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    {φ : Configuration d N → ℝ} (hφ : Continuous φ) {B : ℝ}
    (hB : ∀ x, ‖φ x‖ ≤ B) :
    (∫ z, φ z ∂globalLaw hN hb hbound hM hL₁ hL₂ μ (S+T)) =
      ∫ x, (∫ z, φ z ∂globalLaw hN hb hbound hM hL₁ hL₂ (Measure.dirac x) T)
        ∂globalLaw hN hb hbound hM hL₁ hL₂ μ S :=
  BrownianFlow.globalLaw_add_integral
    ((particleDrift_lipschitz hN hb hbound hL₁ hL₂).continuous.comp continuous_snd)
    (M := ⟨M,hM⟩) (fun _ x => particleDrift_norm_bound hN hbound hM x)
    (fun _ => particleDrift_lipschitz hN hb hbound hL₁ hL₂) hS hT μ hφ hB

end SharpWasserstein.BrownianParticle
