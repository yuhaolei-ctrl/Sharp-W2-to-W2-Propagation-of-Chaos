module

public import SharpWasserstein.Compat
public import SharpWasserstein.BrownianGrid
public import SharpWasserstein.GaussianHistorySimulation

@[expose] public section

/-! Actual configuration Brownian increments, with independent initial labels,
generate the Gaussian transition-history law after flattening finite coordinates. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace SharpWasserstein

/-- Reindex a particle configuration as one real vector; no norm rescaling. -/
def configurationFlatten (d N : ℕ) : Configuration d N ≃ᵐ Position (N*d) :=
  (MeasurableEquiv.curry (Fin N) (Fin d) ℝ).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (N*d) => ℝ) finProdFinEquiv)

theorem configurationFlatten_gaussian {d N : ℕ} (v : ℝ≥0) :
    MeasurePreserving (configurationFlatten d N)
      (Measure.pi fun _ : Fin N => gaussianVectorLaw (0 : Position d) v)
      (gaussianVectorLaw (0 : Position (N*d)) v) := by
  have h₁ : MeasurePreserving (MeasurableEquiv.curry (Fin N) (Fin d) ℝ).symm
      (Measure.pi fun _ : Fin N => gaussianVectorLaw (0 : Position d) v)
      (Measure.pi fun _ : Fin N × Fin d => gaussianReal 0 v) := by
    refine ⟨(MeasurableEquiv.curry (Fin N) (Fin d) ℝ).symm.measurable, ?_⟩
    simpa only [Measure.infinitePi_eq_pi, gaussianVectorLaw, Pi.zero_apply] using
      Measure.infinitePi_map_curry_symm (fun (_ : Fin N) (_ : Fin d) => gaussianReal 0 v)
  exact (measurePreserving_piCongrLeft (fun _ : Fin (N*d) => gaussianReal 0 v)
    finProdFinEquiv).comp h₁

namespace BrownianNoise

def flattenedGridIncrement {T : ℝ} {n d N : ℕ} (τ : Fin (n+1) → Icc 0 T)
    (w : C(Icc 0 T, Configuration d N)) (j : Fin n) : Position (N*d) :=
  configurationFlatten d N (w (τ j.succ) - w (τ j.castSucc))

theorem flattenedGridIncrement_measurable {T : ℝ} {n d N : ℕ}
    (τ : Fin (n+1) → Icc 0 T) : Measurable (flattenedGridIncrement (d := d) (N := N) τ) :=
  Measurable.of_eval fun j => (configurationFlatten d N).measurable.comp
    (by fun_prop : Continuous (fun w : C(Icc 0 T, Configuration d N) =>
      w (τ j.succ) - w (τ j.castSucc))).measurable

theorem configurationLaw_flattenedGrid_hasLaw {T : ℝ} {n d N : ℕ}
    (τ : Fin (n+1) → Icc 0 T) (hτ : Monotone τ) :
    HasLaw (flattenedGridIncrement (d := d) (N := N) τ)
      (Measure.pi fun j : Fin n => gaussianVectorLaw (0 : Position (N*d))
        (2 * nndist (τ j.succ : ℝ) (τ j.castSucc : ℝ))) (configurationLaw d N T) := by
  have h := (configurationLaw_grid_hasLaw (d := d) (N := N) τ hτ).measurePreserving
    (Measurable.of_eval fun j => (by fun_prop : Continuous (fun w : C(Icc 0 T, Configuration d N) =>
      w (τ j.succ) - w (τ j.castSucc))).measurable)
  exact ((measurePreserving_pi _ _ fun j : Fin n => configurationFlatten_gaussian
    (d := d) (N := N) (2 * nndist (τ j.succ : ℝ) (τ j.castSucc : ℝ))).comp h).hasLaw

/-- A deterministic simulator fed actual Brownian grid increments has the
iterated Gaussian transition law. The initial label law is completely arbitrary. -/
theorem brownian_gaussianHistory_hasLaw {A : Type*} [MeasurableSpace A]
    {T : ℝ} {n d N : ℕ} (τ : Fin (n+1) → Icc 0 T) (hτ : Monotone τ)
    (μ₀ : Measure (GaussianHistory A (N*d) 0)) [IsProbabilityMeasure μ₀]
    (a : (m : ℕ) → GaussianHistory A (N*d) m → Position (N*d)) (ha : ∀ m, Measurable (a m))
    (v : ℕ → ℝ≥0) (hv : ∀ j : Fin n, v j = 2 * nndist (τ j.succ : ℝ) (τ j.castSucc : ℝ)) :
    HasLaw (fun p : GaussianHistory A (N*d) 0 × C(Icc 0 T, Configuration d N) =>
      gaussianHistorySimulator a n (p.1, flattenedGridIncrement τ p.2))
      (gaussianHistoryLaw μ₀ a ha v n) (μ₀.prod (configurationLaw d N T)) := by
  have hg : HasLaw (flattenedGridIncrement (d := d) (N := N) τ)
      (gaussianInnovationLaw (N*d) v n) (configurationLaw d N T) := by
    simpa only [gaussianInnovationLaw, hv] using configurationLaw_flattenedGrid_hasLaw τ hτ
  exact ((gaussianHistorySimulator_hasLaw μ₀ a ha v n).measurePreserving
    (gaussianHistorySimulator_measurable a ha n) |>.comp
      ((MeasurePreserving.id μ₀).prod (hg.measurePreserving (flattenedGridIncrement_measurable τ)))).hasLaw

end BrownianNoise
end SharpWasserstein
