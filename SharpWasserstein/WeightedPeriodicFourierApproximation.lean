module

public import SharpWasserstein.Compat
public import SharpWasserstein.WeightedPeriodicFourierSmoothing

@[expose] public section

/-! Genuine uniform C¹ approximation of a smooth periodic potential by
finite real trigonometric polynomials. No absolute continuity of any later
carrying measure is required. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff BigOperators
namespace SharpWasserstein.WeightedPeriodicFourier
open PeriodicIntegrationByParts PeriodicTorusBridge PeriodicPositiveKernel PeriodicConvolution
open PeriodicFourierTests PeriodicFourierPolynomials PeriodicFourierDensity
variable {n : ℕ}

theorem smoothedPolynomial_uniform_tendsto (κ : ℝ) (f : Coordinates n → ℝ)
    (hp : Periodic f) (hf : Continuous f) :
    ∀ ε > 0, ∀ᶠ s : Finset (Fin n → ℤ) in atTop, ∀ y,
      |testAverage κ (polynomial s f) y - testAverage κ f y| < ε := by
  intro ε hε
  have ht : Tendsto (fun s : Finset (Fin n → ℤ) =>
      (Real.exp |κ|/normalizer κ)^n *
        Real.sqrt (∫ x, (polynomial s f x-f x)^2 ∂cube n)) atTop (𝓝 0) := by
    simpa using (integral_polynomial_error_tendsto f hp hf).sqrt.const_mul
      ((Real.exp |κ|/normalizer κ)^n)
  filter_upwards [(tendsto_order.mp ht).2 ε hε] with s hs
  intro y
  have hb := testAverage_abs_le_L2 κ
    (fun i x => by simp only [Pi.sub_apply,periodic_polynomial s f i x,hp i x])
    ((smooth_polynomial s f).continuous.sub hf) y
  rw [testAverage_sub κ (smooth_polynomial s f).continuous hf] at hb
  exact hb.trans_lt hs

theorem smoothedPolynomial_partial_uniform_tendsto (κ : ℝ) (f : Coordinates n → ℝ)
    (hp : Periodic f) (hf : ContDiff ℝ ∞ f) (i : Fin n) :
    ∀ ε > 0, ∀ᶠ s : Finset (Fin n → ℤ) in atTop, ∀ y,
      |coordinatePartial (testAverage κ (polynomial s f)) i y -
        coordinatePartial (testAverage κ f) i y| < ε := by
  intro ε hε
  have h := smoothedPolynomial_uniform_tendsto κ (coordinatePartial f i)
    (periodic_coordinatePartial hp i) (continuous_coordinatePartial (hf.of_le (by simp)) i) ε hε
  filter_upwards [h] with s hs
  intro y
  rw [testAverage_coordinatePartial κ (smooth_polynomial s f) (periodic_polynomial s f),
    testAverage_coordinatePartial κ hf hp]
  change |testAverage κ (coordinatePartial (polynomial s f) i) y -
    testAverage κ (coordinatePartial f i) y| < ε
  rw [coordinatePartial_polynomial_eq s (hf.of_le (by simp)) hp]
  exact hs y

theorem testAverage_partial_uniform_tendsto (f : Coordinates n → ℝ)
    (hp : Periodic f) (hf : ContDiff ℝ ∞ f) (i : Fin n) :
    ∀ ε > 0, ∀ᶠ k : ℕ in atTop, ∀ y,
      |coordinatePartial (testAverage (k : ℝ) f) i y - coordinatePartial f i y| < ε := by
  intro ε hε
  have h := testAverage_uniform_tendsto (coordinatePartial f i)
    (periodic_coordinatePartial hp i) (continuous_coordinatePartial (hf.of_le (by simp)) i) ε hε
  filter_upwards [h] with k hk
  intro y
  rw [testAverage_coordinatePartial (k : ℝ) hf hp]
  exact hk y

/-- A single actual finite Fourier potential approximates the potential and
all first coordinate derivatives uniformly on the entire ambient space. -/
theorem exists_frequencySpace_uniform_C1 (f : Coordinates n → ℝ)
    (hp : Periodic f) (hf : ContDiff ℝ ∞ f) {ε : ℝ} (hε : 0 < ε) :
    ∃ (s : Finset (Fin n → ℤ)) (p : Coordinates n → ℝ),
      p ∈ frequencySpace (frequencySet s) ∧
      (∀ y, |p y-f y| < ε) ∧
      (∀ i y, |coordinatePartial p i y-coordinatePartial f i y| < ε) := by
  have he : 0 < ε/2 := half_pos hε
  have h1 := testAverage_uniform_tendsto f hp hf.continuous (ε/2) he
  have h2 : ∀ᶠ k : ℕ in atTop, ∀ i y,
      |coordinatePartial (testAverage (k : ℝ) f) i y - coordinatePartial f i y| < ε/2 :=
    eventually_all.mpr fun i => testAverage_partial_uniform_tendsto f hp hf i (ε/2) he
  obtain ⟨k,hk1,hk2⟩ := (h1.and h2).exists
  have h3 := smoothedPolynomial_uniform_tendsto (k : ℝ) f hp hf.continuous (ε/2) he
  have h4 : ∀ᶠ s : Finset (Fin n → ℤ) in atTop, ∀ i y,
      |coordinatePartial (testAverage (k : ℝ) (polynomial s f)) i y -
        coordinatePartial (testAverage (k : ℝ) f) i y| < ε/2 :=
    eventually_all.mpr fun i => smoothedPolynomial_partial_uniform_tendsto (k : ℝ) f hp hf i (ε/2) he
  obtain ⟨s,hs1,hs2⟩ := (h3.and h4).exists
  refine ⟨s,testAverage (k : ℝ) (polynomial s f),
    testAverage_frequencySpace (k : ℝ) s (polynomial_mem s f),?_,?_⟩
  · intro y
    calc
      _ ≤ |testAverage (k : ℝ) (polynomial s f) y-testAverage (k : ℝ) f y| +
        |testAverage (k : ℝ) f y-f y| := abs_sub_le _ _ _
      _ < ε/2+ε/2 := add_lt_add (hs1 y) (hk1 y)
      _ = ε := add_halves ε
  · intro i y
    calc
      _ ≤ |coordinatePartial (testAverage (k : ℝ) (polynomial s f)) i y -
          coordinatePartial (testAverage (k : ℝ) f) i y| +
        |coordinatePartial (testAverage (k : ℝ) f) i y-coordinatePartial f i y| :=
          abs_sub_le _ _ _
      _ < ε/2+ε/2 := add_lt_add (hs2 i y) (hk2 i y)
      _ = ε := add_halves ε

end SharpWasserstein.WeightedPeriodicFourier
