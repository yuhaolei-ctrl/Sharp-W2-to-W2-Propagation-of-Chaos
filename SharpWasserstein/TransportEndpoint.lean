import SharpWasserstein.TransportTriangle
import SharpWasserstein.Assembly

/-!
# Endpoint assembly for the actual quadratic Wasserstein infimum

This specializes the proved metric estimate to the P₂ pseudometric constructed
from actual probability couplings. The two remaining analytic hypotheses are
an interpolation length bound and a decoupled stability bound. No claim is made
here that diffusion laws supply those hypotheses.
-/

noncomputable section

open MeasureTheory Real
open scoped ENNReal

namespace SharpWasserstein

/-- Conditional endpoint estimate with the manuscript's genuine transport cost.
All three laws are probability laws with finite second moments, so the real
square roots and the extended-valued conclusion agree without an infinity convention. -/
theorem wasserstein_endpoint_assembly
    {d k N : ℕ} (μ r ν : Measure (Configuration d k))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure r] [IsProbabilityMeasure ν]
    (hμ : HasSecondMoment μ) (hr : HasSecondMoment r) (hν : HasSecondMoment ν)
    {K L C₀ T : ℝ} (hK : 0 ≤ K) (hT : 0 ≤ T)
    (hlength : Real.sqrt (wassersteinSq μ r).toReal ≤
      K * (∫ s in (0 : ℝ)..T, RegularizationRates.speedRate s) * ((k : ℝ) / N))
    (hdecoupled : Real.sqrt (wassersteinSq r ν).toReal ≤
      exp (L * T) * sqrt C₀ * ((k : ℝ) / N)) :
    wassersteinSq μ ν ≤
      ENNReal.ofReal (endpointConstant K L C₀ T * (k : ℝ) ^ 2 / (N : ℝ) ^ 2) := by
  let x : QuadraticProbabilityLaw d k := ⟨μ, inferInstance, hμ⟩
  let z : QuadraticProbabilityLaw d k := ⟨r, inferInstance, hr⟩
  let y : QuadraticProbabilityLaw d k := ⟨ν, inferInstance, hν⟩
  have ht := metric_endpoint_assembly x z y hK hT hlength hdecoupled
  have he : ENNReal.ofReal (dist x y ^ 2) = wassersteinSq μ ν :=
    quadraticProbability_ofReal_dist_sq x y
  rw [← he]
  exact ENNReal.ofReal_le_ofReal ht

end SharpWasserstein
