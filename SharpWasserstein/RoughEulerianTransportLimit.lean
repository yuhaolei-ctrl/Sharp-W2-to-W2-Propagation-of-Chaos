import SharpWasserstein.TransportTriangle

/-! Removing actual endpoint regularizations in the true unnormalized
Wasserstein cost. All measures have their actual finite second moments; no
identification of narrow convergence with W₂ convergence is assumed. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace SharpWasserstein.RoughEulerianTransport

/-- Actual squared-W₂ convergence is convergence in the proved P₂ pseudometric. -/
theorem quadraticLaw_tendsto_of_wassersteinSq {d N : ℕ} {J : Type*} {l : Filter J}
    {μ : J → QuadraticProbabilityLaw d N} {ν : QuadraticProbabilityLaw d N}
    (h : Tendsto (fun j => wassersteinSq (μ j).measure ν.measure) l (𝓝 0)) :
    Tendsto μ l (𝓝 ν) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp
    ((ENNReal.tendsto_toReal (by simp : (0:ℝ≥0∞) ≠ ⊤)).comp h)
  simpa only [quadraticProbability_dist_eq,Function.comp_def,ENNReal.toReal_zero,Real.sqrt_zero] using ht

/-- Converging both genuine endpoints preserves the actual squared transport
cost, since all endpoint laws lie in P₂. -/
theorem wassersteinSq_tendsto_of_endpoints {d N : ℕ} {J : Type*} {l : Filter J}
    {μ ν : J → QuadraticProbabilityLaw d N} {μ₀ ν₀ : QuadraticProbabilityLaw d N}
    (hμ : Tendsto (fun j => wassersteinSq (μ j).measure μ₀.measure) l (𝓝 0))
    (hν : Tendsto (fun j => wassersteinSq (ν j).measure ν₀.measure) l (𝓝 0)) :
    Tendsto (fun j => wassersteinSq (μ j).measure (ν j).measure) l
      (𝓝 (wassersteinSq μ₀.measure ν₀.measure)) := by
  have ht := ENNReal.tendsto_ofReal
    (((quadraticLaw_tendsto_of_wassersteinSq hμ).dist (quadraticLaw_tendsto_of_wassersteinSq hν)).pow 2)
  simpa only [quadraticProbability_ofReal_dist_sq] using ht

/-- Any uniform finite transport estimate on the regularized endpoint laws
passes to the original endpoints through their actual W₂ convergence. -/
theorem wassersteinSq_le_of_regularized_endpoints {d N : ℕ} {J : Type*} {l : Filter J} [l.NeBot]
    {μ ν : J → QuadraticProbabilityLaw d N} {μ₀ ν₀ : QuadraticProbabilityLaw d N}
    (hμ : Tendsto (fun j => wassersteinSq (μ j).measure μ₀.measure) l (𝓝 0))
    (hν : Tendsto (fun j => wassersteinSq (ν j).measure ν₀.measure) l (𝓝 0))
    {C : ℝ} (hC : ∀ᶠ j in l,wassersteinSq (μ j).measure (ν j).measure ≤ ENNReal.ofReal C) :
    wassersteinSq μ₀.measure ν₀.measure ≤ ENNReal.ofReal C :=
  le_of_tendsto (wassersteinSq_tendsto_of_endpoints hμ hν) hC

/-- A converging actual action upper bound may be used as well, without
replacing the endpoint convergence by a weak-topology premise. -/
theorem wassersteinSq_le_of_regularized_action_limit {d N : ℕ} {J : Type*} {l : Filter J} [l.NeBot]
    {μ ν : J → QuadraticProbabilityLaw d N} {μ₀ ν₀ : QuadraticProbabilityLaw d N}
    (hμ : Tendsto (fun j => wassersteinSq (μ j).measure μ₀.measure) l (𝓝 0))
    (hν : Tendsto (fun j => wassersteinSq (ν j).measure ν₀.measure) l (𝓝 0))
    {C : J → ℝ} {B : ℝ} (hC : Tendsto C l (𝓝 B))
    (hbound : ∀ᶠ j in l,wassersteinSq (μ j).measure (ν j).measure ≤ ENNReal.ofReal (C j)) :
    wassersteinSq μ₀.measure ν₀.measure ≤ ENNReal.ofReal B :=
  le_of_tendsto_of_tendsto (wassersteinSq_tendsto_of_endpoints hμ hν)
    (ENNReal.tendsto_ofReal hC) hbound

end SharpWasserstein.RoughEulerianTransport
