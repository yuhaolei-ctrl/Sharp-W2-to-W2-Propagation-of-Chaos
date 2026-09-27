import SharpWasserstein.ContinuousPathLaw
import SharpWasserstein.BrownianHorizon

/-! Independent past and shifted future for the actual continuous Brownian
path law. Process independence is transported through the evaluation-generated
path sigma-algebra, rather than assumed as a Markov property. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace SharpWasserstein
namespace BoundedFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def shiftPath {S T : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T)
    (w : C(Icc 0 (S+T),E)) : C(Icc 0 T,E) :=
  ⟨fun t => w ⟨S+t,add_nonneg hS t.property.1,add_le_add_right t.property.2 S⟩ -
    w ⟨S,hS,le_add_of_nonneg_right hT⟩,
    (w.continuous.comp ((continuous_const.add continuous_subtype_val).subtype_mk _)).sub continuous_const⟩

omit [NormedSpace ℝ E] in
theorem shiftPath_measurable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {S T : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T) : Measurable (shiftPath (E := E) hS hT) := by
  apply (ContinuousMap.measurable_iff_eval _).mpr
  intro t
  change Measurable (fun w : C(Icc 0 (S+T),E) =>
    w ⟨S+t,add_nonneg hS t.property.1,add_le_add_right t.property.2 S⟩ -
    w ⟨S,hS,le_add_of_nonneg_right hT⟩)
  fun_prop

def splitPath {S T : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T) (w : C(Icc 0 (S+T),E)) :
    C(Icc 0 S,E) × C(Icc 0 T,E) :=
  (restrictPath (le_add_of_nonneg_right hT) w,shiftPath hS hT w)

theorem splitPath_measurable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {S T : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T) : Measurable (splitPath (E := E) hS hT) :=
  (restrictPath_measurable (le_add_of_nonneg_right hT)).prodMk (shiftPath_measurable hS hT)

end BoundedFlow
namespace BrownianNoise
open BoundedFlow

theorem shiftedScalarPath_hasLaw {S T : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T) :
    HasLaw (fun ω : Sample => shiftPath hS hT (scalarPath ω)) (scalarLaw T) gaussianLimit := by
  have hm : Measurable (fun ω : Sample => shiftPath hS hT (scalarPath ω)) :=
    (shiftPath_measurable (E := ℝ) hS hT).comp scalarPath_measurable
  refine ⟨hm.aemeasurable, ?_⟩
  apply continuousPath_map_coe_injective
  rw [Measure.map_map continuousPath_coe_measurable hm,scalarLaw,
    Measure.map_map continuousPath_coe_measurable scalarPath_measurable]
  let F : Sample → Icc 0 T → ℝ := fun z t => Real.sqrt 2*z ⟨t,t.property.1⟩
  have hF : Measurable F := by unfold F; fun_prop
  have hFlaw : HasLaw F (gaussianLimit.map F) gaussianLimit := ⟨hF.aemeasurable,rfl⟩
  have hs := (isBrownianReal_brownian.toIsPreBrownianReal.shift ⟨S,hS⟩).hasLaw_gaussianLimit
    (by apply Measurable.aemeasurable; apply measurable_pi_lambda; intro t; fun_prop)
  have hmap := (hFlaw.comp hs).map_eq.trans (hFlaw.comp hasLaw_brownian).map_eq.symm
  convert hmap using 1
  · congr 1
    funext ω t
    have hadd : (⟨S+(t:ℝ),add_nonneg hS t.property.1⟩ : ℝ≥0) =
        ⟨S,hS⟩+⟨t,t.property.1⟩ := by ext; rfl
    change Real.sqrt 2*brownian _ ω-Real.sqrt 2*brownian _ ω = Real.sqrt 2*(brownian _ ω-brownian _ ω)
    rw [hadd, mul_sub]
    congr 3
  · rfl

theorem scalarPath_indep_shift {S T : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T) :
    IndepFun (scalarPath (T := S)) (fun ω : Sample => shiftPath hS hT (scalarPath ω)) gaussianLimit := by
  apply continuousPath_indepFun_of_coe
  let F : (Iic (NNReal.mk S hS) → ℝ) → Icc 0 S → ℝ :=
    fun z t => Real.sqrt 2*z ⟨⟨t,t.property.1⟩,t.property.2⟩
  let G : Sample → Icc 0 T → ℝ := fun z t => Real.sqrt 2*z ⟨t,t.property.1⟩
  have hF : Measurable F := by unfold F; fun_prop
  have hG : Measurable G := by unfold G; fun_prop
  have hi := (isBrownianReal_brownian.toIsPreBrownianReal.indepFun_shift ⟨S,hS⟩).symm.comp hF hG
  convert hi using 1
  · rfl
  · funext ω t
    have hadd : (⟨S+(t:ℝ),add_nonneg hS t.property.1⟩ : ℝ≥0) =
        ⟨S,hS⟩+⟨t,t.property.1⟩ := by ext; rfl
    change Real.sqrt 2*brownian _ ω-Real.sqrt 2*brownian _ ω = Real.sqrt 2*(brownian _ ω-brownian _ ω)
    rw [hadd, mul_sub]
    congr 3

/-- Splitting the actual scalar Brownian path gives independent Brownian
past and future paths, with the future restarted at zero. -/
theorem scalarLaw_split {S T : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T) :
    MeasurePreserving (splitPath (E := ℝ) hS hT) (scalarLaw (S+T))
      ((scalarLaw S).prod (scalarLaw T)) := by
  refine ⟨splitPath_measurable hS hT, ?_⟩
  have hp : HasLaw (scalarPath (T := S)) (scalarLaw S) gaussianLimit :=
    ⟨scalarPath_measurable.aemeasurable,rfl⟩
  have hi := IndepFun.hasLaw_prod hp (shiftedScalarPath_hasLaw hS hT) (scalarPath_indep_shift hS hT)
  rw [scalarLaw,Measure.map_map (splitPath_measurable hS hT) scalarPath_measurable]
  exact hi.map_eq


theorem coordinateLaw_split (d : ℕ) {S T : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T) :
    MeasurePreserving (fun w : Fin d → C(Icc 0 (S+T),ℝ) =>
      (fun a => restrictPath (le_add_of_nonneg_right hT) (w a),
       fun a => shiftPath hS hT (w a)))
      (coordinateLaw d (S+T)) ((coordinateLaw d S).prod (coordinateLaw d T)) := by
  exact (measurePreserving_arrowProdEquivProdArrow C(Icc 0 S,ℝ) C(Icc 0 T,ℝ) (Fin d)
    (fun _ => scalarLaw S) (fun _ => scalarLaw T)).comp
      (measurePreserving_pi (fun _ => scalarLaw (S+T))
        (fun _ => (scalarLaw S).prod (scalarLaw T)) (fun _ => scalarLaw_split hS hT))

theorem pathLabels_split (d N : ℕ) {S T : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T) :
    MeasurePreserving (fun w : Fin N → Fin d → C(Icc 0 (S+T),ℝ) =>
      (fun i a => restrictPath (le_add_of_nonneg_right hT) (w i a),
       fun i a => shiftPath hS hT (w i a)))
      (pathLabels d N (S+T)) ((pathLabels d N S).prod (pathLabels d N T)) := by
  exact (measurePreserving_arrowProdEquivProdArrow
    (Fin d → C(Icc 0 S,ℝ)) (Fin d → C(Icc 0 T,ℝ)) (Fin N)
    (fun _ => coordinateLaw d S) (fun _ => coordinateLaw d T)).comp
      (measurePreserving_pi (fun _ => coordinateLaw d (S+T))
        (fun _ => (coordinateLaw d S).prod (coordinateLaw d T))
        (fun _ => coordinateLaw_split d hS hT))

/-- The past and restarted future of the complete particle Brownian path
are independent, with the actual finite-horizon configuration path laws. -/
theorem configurationLaw_split (d N : ℕ) {S T : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T) :
    MeasurePreserving (splitPath (E := Configuration d N) hS hT)
      (configurationLaw d N (S+T))
      ((configurationLaw d N S).prod (configurationLaw d N T)) := by
  have hc (U : ℝ) : MeasurePreserving (configurationPath (d := d) (N := N) (T := U))
      (pathLabels d N U) (configurationLaw d N U) := ⟨configurationPath_measurable,rfl⟩
  have hp := ((hc S).prod (hc T)).comp (pathLabels_split d N hS hT)
  refine ⟨splitPath_measurable hS hT, ?_⟩
  rw [configurationLaw,Measure.map_map (splitPath_measurable hS hT) configurationPath_measurable]
  exact hp.map_eq

end BrownianNoise
end SharpWasserstein
