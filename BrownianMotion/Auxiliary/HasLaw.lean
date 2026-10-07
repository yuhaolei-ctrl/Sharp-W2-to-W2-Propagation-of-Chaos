/-
Vendored from github.com/RemyDegenne/brownian-motion.
Released under Apache 2.0 license as described in the file LICENSE.brownian-motion.
Adapted for Mathlib v4.35.0-rc3 in Sharp-W2-to-W2-Propagation-of-Chaos.
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

open MeasureTheory ENNReal WithLp

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

section HasLaw

variable {𝓧} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧} {μ : Measure 𝓧} {P : Measure Ω}

-- `hasLaw_map` has been upstreamed to Mathlib (`Mathlib.Probability.HasLaw`);
-- the vendored copy was removed.

section dirac

-- don't upstream this: it's too specific. Delete it here eventually.
lemma HasLaw.ae_eq_const_of_gaussianReal {X : Ω → ℝ} {μ : ℝ} (hX : HasLaw X (gaussianReal μ 0) P) :
    ∀ᵐ ω ∂P, X ω = μ := by
  rw [gaussianReal_zero_var] at hX
  exact hX.ae_eq_of_dirac

end dirac

end HasLaw

end ProbabilityTheory
