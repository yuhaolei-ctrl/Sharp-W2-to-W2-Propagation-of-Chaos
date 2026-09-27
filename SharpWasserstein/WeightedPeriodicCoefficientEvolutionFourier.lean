import SharpWasserstein.WeightedPeriodicCoefficientEvolution
import SharpWasserstein.PeriodicSmoothBounds
import SharpWasserstein.PeriodicFourierTests

/-! Concrete periodic and Fourier test instances of the actual weighted
coefficient equations. The needed global derivative bounds are derived from
the compact quotient torus rather than supplied as extra hypotheses. -/
noncomputable section
open scoped ContDiff
namespace SharpWasserstein.WeightedPeriodicCoefficientEvolution
open WeightedTangent NoiseAverage PeriodicIntegrationByParts PeriodicBochner PeriodicFourierTests
variable {n : ℕ}

/-- Every smooth periodic potential has actual global bounds at every
Fréchet derivative order, by descent to the compact quotient torus. -/
theorem periodic_allDerivativesBounded {f : Coordinates n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Periodic f) : AllDerivativesBounded f :=
  PeriodicSmoothBounds.iteratedFDeriv_bound hp hf

/-- Euclidean coordinate transport preserves all of those genuine bounds. -/
theorem periodic_pullback_allDerivativesBounded {f : Coordinates n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Periodic f) : AllDerivativesBounded (pullback f) :=
  (periodic_allDerivativesBounded hf hp).comp_linear hf (coordinateEquiv n).toContinuousLinearMap

theorem atom_pullback_smooth (p : (Fin n → ℤ) × Bool) :
    ContDiff ℝ ∞ (pullback (atom p)) :=
  (smooth_atom p).comp (coordinateEquiv n).contDiff

theorem atom_pullback_allDerivativesBounded (p : (Fin n → ℤ) × Bool) :
    AllDerivativesBounded (pullback (atom p)) :=
  periodic_pullback_allDerivativesBounded (smooth_atom p) (periodic_atom p)

/-- Every actual potential in the finite Fourier space satisfies the
coefficient-evolution test hypotheses, not just the individual atoms. -/
theorem frequencySpace_pullback_smooth_bounded
    {s : Finset ((Fin n → ℤ) × Bool)} {f : Coordinates n → ℝ}
    (hf : f ∈ frequencySpace s) :
    ContDiff ℝ ∞ (pullback f) ∧ AllDerivativesBounded (pullback f) := by
  obtain ⟨hs,hp,_⟩ := PeriodicFourierTests.frequencySpace_properties s hf
  exact ⟨hs.comp (coordinateEquiv n).contDiff,periodic_pullback_allDerivativesBounded hs hp⟩

/-- Products of genuine gradients from any two finite Fourier potentials
meet all scalar weak-generator hypotheses. -/
theorem frequencySpace_gramTest_smooth_bounded
    {s r : Finset ((Fin n → ℤ) × Bool)} {f g : Coordinates n → ℝ}
    (hf : f ∈ frequencySpace s) (hg : g ∈ frequencySpace r) :
    ContDiff ℝ ∞ (gramTest (pullback f) (pullback g)) ∧
      AllDerivativesBounded (gramTest (pullback f) (pullback g)) := by
  obtain ⟨hs,hBf⟩ := frequencySpace_pullback_smooth_bounded hf
  obtain ⟨ht,hBg⟩ := frequencySpace_pullback_smooth_bounded hg
  exact ⟨gramTest_smooth hs ht,gramTest_allDerivativesBounded hs ht hBf hBg⟩

end SharpWasserstein.WeightedPeriodicCoefficientEvolution
