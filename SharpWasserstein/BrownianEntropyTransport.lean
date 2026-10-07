module

public import SharpWasserstein.Compat
public import SharpWasserstein.BrownianEntropyCost
public import SharpWasserstein.RandomMapTransport

@[expose] public section

/-! Optimize the proved Brownian entropy bound over actual probability
couplings. This yields the manuscript's Wasserstein entropy-cost inequality. -/
noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal NNReal
namespace SharpWasserstein.BrownianEntropy

theorem flow_entropy_le_wassersteinSq {d N : ℕ} {T : ℝ}
    {v : ℝ → Configuration d N → Configuration d N} {M K L : ℝ≥0}
    (μ ν : Measure (Configuration d N)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : HasSecondMoment μ) (hν : HasSecondMoment ν)
    (hv : Continuous (Function.uncurry v)) (hb : ∀ t x, ‖v t x‖ ≤ M)
    (hl : ∀ t, LipschitzWith K (v t))
    (he : ∀ t, LipschitzWith L (GaussianBridge.euclideanDrift (flattenedDrift v) t))
    (hT : 0 < T) :
    klDiv (flowLaw μ hv hb hl hT.le : Measure (Configuration d N))
      (flowLaw ν hv hb hl hT.le : Measure (Configuration d N)) ≤
      ENNReal.ofReal (RegularizationRates.bridgeCost L T) * wassersteinSq μ ν := by
  letI : Nonempty {γ // IsCoupling μ ν γ} := ⟨⟨μ.prod ν, product_isCoupling μ ν⟩⟩
  rw [wassersteinSq_eq_iInf_coupling μ ν, ENNReal.mul_iInf (by simp)]
  apply le_iInf
  intro γ
  have h := flow_entropy_le_coupling μ ν γ.property hμ hν hv hb hl he hT
  have hi := coupling_productCost_integrable γ.property hμ hν
  have hC : 0 ≤ RegularizationRates.bridgeCost L T := by
    unfold RegularizationRates.bridgeCost
    positivity
  rw [ENNReal.ofReal_mul hC,ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun z => productCost_nonneg z.1 z.2))] at h
  exact h

theorem flow_entropy_finite {d N : ℕ} {T : ℝ}
    {v : ℝ → Configuration d N → Configuration d N} {M K L : ℝ≥0}
    (μ ν : Measure (Configuration d N)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : HasSecondMoment μ) (hν : HasSecondMoment ν)
    (hv : Continuous (Function.uncurry v)) (hb : ∀ t x, ‖v t x‖ ≤ M)
    (hl : ∀ t, LipschitzWith K (v t))
    (he : ∀ t, LipschitzWith L (GaussianBridge.euclideanDrift (flattenedDrift v) t))
    (hT : 0 < T) :
    klDiv (flowLaw μ hv hb hl hT.le : Measure (Configuration d N))
      (flowLaw ν hv hb hl hT.le : Measure (Configuration d N)) < ∞ := by
  exact (flow_entropy_le_wassersteinSq μ ν hμ hν hv hb hl he hT).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (wassersteinSq_lt_top μ ν hμ hν))

end SharpWasserstein.BrownianEntropy
