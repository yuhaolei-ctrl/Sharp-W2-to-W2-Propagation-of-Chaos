module

public import SharpWasserstein.Compat
public import SharpWasserstein.GaussianControlledBridge
public import SharpWasserstein.BrownianGaussianHistory
public import SharpWasserstein.CouplingMoments

@[expose] public section

/-! Initial P₂ couplings supply the actual finite Euclidean displacement moment
required by the Gaussian bridge. Flattening changes no transport normalization. -/
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators
namespace SharpWasserstein

@[simp] theorem configurationFlatten_apply_coordinate {d N : ℕ}
    (x : Configuration d N) (i : Fin N) (a : Fin d) :
    configurationFlatten d N x (finProdFinEquiv (i,a)) = x i a := by
  simp only [configurationFlatten, MeasurableEquiv.trans_apply,
    MeasurableEquiv.piCongrLeft_apply_apply]
  rfl

namespace GaussianBridge

def flattenedCoupling {d N : ℕ} (γ : Measure (Configuration d N × Configuration d N)) :
    Measure (Labels (N*d)) := γ.map ((configurationFlatten d N).prodCongr (configurationFlatten d N))

instance flattenedCoupling_isProbability {d N : ℕ}
    (γ : Measure (Configuration d N × Configuration d N)) [IsProbabilityMeasure γ] :
    IsProbabilityMeasure (flattenedCoupling γ) :=
  Measure.isProbabilityMeasure_map ((configurationFlatten d N).prodCongr (configurationFlatten d N)).measurable.aemeasurable

theorem displacementSq_flatten {d N : ℕ} (x y : Configuration d N) :
    displacementSq (configurationFlatten d N x, configurationFlatten d N y) = productCost x y := by
  change (∑ i, (configurationFlatten d N y i - configurationFlatten d N x i)^2) =
    ∑ i, ∑ a, (x i a - y i a)^2
  calc
    _ = ∑ p : Fin N × Fin d, (x p.1 p.2 - y p.1 p.2)^2 := by
      symm
      apply Fintype.sum_equiv finProdFinEquiv
      intro p
      rw [configurationFlatten_apply_coordinate, configurationFlatten_apply_coordinate]
      ring
    _ = _ := Fintype.sum_prod_type _

/-- Every coupling of the actual P₂ configuration laws meets the bridge's
finite-cost hypothesis after exact Euclidean reindexing. -/
theorem flattenedCoupling_displacement_integrable {d N : ℕ}
    {μ ν : Measure (Configuration d N)} {γ : Measure (Configuration d N × Configuration d N)}
    (hγ : IsCoupling μ ν γ) (hμ : HasSecondMoment μ) (hν : HasSecondMoment ν) :
    Integrable displacementSq (flattenedCoupling γ) := by
  rw [flattenedCoupling, integrable_map_measure (measurable_displacementSq (N*d)).aestronglyMeasurable
    ((configurationFlatten d N).prodCongr (configurationFlatten d N)).measurable.aemeasurable]
  have he : displacementSq ∘ ((configurationFlatten d N).prodCongr (configurationFlatten d N)) =
      (fun z ↦ productCost z.1 z.2) := funext fun z ↦ displacementSq_flatten z.1 z.2
  rw [he]
  exact coupling_productCost_integrable hγ hμ hν

theorem flattenedCoupling_displacement_integral {d N : ℕ}
    (γ : Measure (Configuration d N × Configuration d N)) :
    (∫ z, displacementSq z ∂flattenedCoupling γ) = ∫ z, productCost z.1 z.2 ∂γ := by
  rw [flattenedCoupling, integral_map
    ((configurationFlatten d N).prodCongr (configurationFlatten d N)).measurable.aemeasurable
    (measurable_displacementSq (N*d)).aestronglyMeasurable]
  exact integral_congr_ae (Filter.Eventually.of_forall fun z ↦ displacementSq_flatten z.1 z.2)

/-- The finite Gaussian bridge entropy bound for an arbitrary actual P₂
coupling, with no factor depending on spatial dimension or particle count. -/
theorem observation_entropy_le_coupling {E : Type*} [MeasurableSpace E] {d N : ℕ}
    {μ ν : Measure (Configuration d N)} {γ : Measure (Configuration d N × Configuration d N)}
    (hγ : IsCoupling μ ν γ) (hμ : HasSecondMoment μ) (hν : HasSecondMoment ν)
    {v : ℝ → Position (N*d) → Position (N*d)} (hv : ∀ t, Measurable (v t))
    {T : ℝ} {δ : ℝ≥0} (hδ : δ ≠ 0) {K : ℝ≥0}
    (hl : ∀ t, LipschitzWith K (euclideanDrift v t)) (hT : 0 < T)
    (n : ℕ) (hgrid : (n : ℝ)*δ ≤ T) (f : History (N*d) n → E) (hf : Measurable f) :
    klDiv ((ordinaryLaw (flattenedCoupling γ) v hv δ n).map f)
      ((shiftedLaw (flattenedCoupling γ) v hv T δ n).map f) ≤
      ENNReal.ofReal (((δ : ℝ)/4 * ∑ j ∈ Finset.range n,
        (RegularizationRates.bridgeRate K T ((j : ℝ)*δ))^2) * ∫ z, productCost z.1 z.2 ∂γ) := by
  letI := hγ.1
  have h := observation_entropy_le (flattenedCoupling γ) hv hδ hl hT
    (flattenedCoupling_displacement_integrable hγ hμ hν) n hgrid f hf
  rwa [flattenedCoupling_displacement_integral] at h

end GaussianBridge
end SharpWasserstein
