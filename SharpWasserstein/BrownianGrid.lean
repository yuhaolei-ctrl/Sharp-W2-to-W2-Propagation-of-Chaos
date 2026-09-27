import SharpWasserstein.ConfigurationBrownian
import SharpWasserstein.GaussianEntropyChain
import Mathlib.Probability.ProductMeasure

/-!
# Actual finite-grid Brownian innovations

The Gaussian laws and independent increments are derived from the constructed
continuous Brownian modification and transported to the concrete path measures.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators
namespace SharpWasserstein.BrownianNoise

def scalarGridIncrement {T : ℝ} {n : ℕ} (τ : Fin (n+1) → Icc 0 T)
    (w : C(Icc 0 T, ℝ)) (i : Fin n) : ℝ := w (τ i.succ) - w (τ i.castSucc)

theorem scalarGridIncrement_measurable {T : ℝ} {n : ℕ} (τ : Fin (n+1) → Icc 0 T) :
    Measurable (scalarGridIncrement τ) := by
  unfold scalarGridIncrement
  fun_prop

/-- Every concrete path increment has its exact centered Gaussian law. -/
theorem scalarLaw_increment_hasLaw {T : ℝ} (s t : Icc 0 T) :
    HasLaw (fun w : C(Icc 0 T, ℝ) => w t - w s)
      (gaussianReal 0 (2 * nndist (t : ℝ) (s : ℝ))) (scalarLaw T) := by
  have h := gaussianReal_const_mul
    (isBrownianReal_brownian.toIsPreBrownianReal.hasLaw_sub
      ⟨t, t.property.1⟩ ⟨s, s.property.1⟩) (Real.sqrt 2)
  have hs : NNReal.mk ((Real.sqrt 2)^2) (sq_nonneg _) = 2 := by
    apply Subtype.ext
    exact Real.sq_sqrt (by norm_num)
  rw [hs] at h
  refine ⟨(by fun_prop : Measurable (fun w : C(Icc 0 T, ℝ) => w t - w s)).aemeasurable, ?_⟩
  rw [scalarLaw, Measure.map_map (by fun_prop) scalarPath_measurable]
  convert h.map_eq using 1
  · congr 1
    funext ω
    simp [scalarPath, mul_sub]
  · simp

/-- The full grid-increment vector has the product Gaussian law, hence its increments are independent. -/
theorem scalarLaw_grid_hasLaw {T : ℝ} {n : ℕ} (τ : Fin (n+1) → Icc 0 T)
    (hτ : Monotone τ) :
    HasLaw (scalarGridIncrement τ)
      (Measure.pi fun i : Fin n => gaussianReal 0 (2 * nndist (τ i.succ : ℝ) (τ i.castSucc : ℝ)))
      (scalarLaw T) := by
  have hind := (isBrownianReal_brownian.toIsPreBrownianReal.hasIndepIncrements.smul (Real.sqrt 2)) n
    (fun i : Fin (n+1) => (⟨τ i, (τ i).property.1⟩ : ℝ≥0))
    (fun i j hij => hτ hij)
  have hi : ∀ i : Fin n, HasLaw
      (fun ω => Real.sqrt 2 * brownian ⟨τ i.succ, (τ i.succ).property.1⟩ ω -
        Real.sqrt 2 * brownian ⟨τ i.castSucc, (τ i.castSucc).property.1⟩ ω)
      (gaussianReal 0 (2 * nndist (τ i.succ : ℝ) (τ i.castSucc : ℝ))) gaussianLimit := by
    intro i
    have h := gaussianReal_const_mul
      (isBrownianReal_brownian.toIsPreBrownianReal.hasLaw_sub
        ⟨τ i.succ, (τ i.succ).property.1⟩ ⟨τ i.castSucc, (τ i.castSucc).property.1⟩) (Real.sqrt 2)
    have hs : NNReal.mk ((Real.sqrt 2)^2) (sq_nonneg _) = 2 := by
      apply Subtype.ext
      exact Real.sq_sqrt (by norm_num)
    rw [hs] at h
    simpa only [Pi.sub_apply, mul_sub, mul_zero] using h
  have hj := hind.hasLaw_pi hi
  refine ⟨(scalarGridIncrement_measurable τ).aemeasurable, ?_⟩
  rw [scalarLaw, Measure.map_map (scalarGridIncrement_measurable τ) scalarPath_measurable]
  exact hj.map_eq

/-- Exchanging the finite spatial and time axes preserves the actual product law. -/
theorem measurePreserving_pi_transpose {ι κ X : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace X] (μ : ι → κ → Measure X)
    [∀ i j, IsProbabilityMeasure (μ i j)] :
    MeasurePreserving (fun x : ι → κ → X => fun j i => x i j)
      (Measure.pi fun i => Measure.pi (μ i))
      (Measure.pi fun j => Measure.pi fun i => μ i j) := by
  have h₁ : MeasurePreserving (MeasurableEquiv.curry ι κ X).symm
      (Measure.pi fun i => Measure.pi (μ i)) (Measure.pi fun p : ι × κ => μ p.1 p.2) := by
    refine ⟨(MeasurableEquiv.curry ι κ X).symm.measurable, ?_⟩
    simpa only [Measure.infinitePi_eq_pi] using Measure.infinitePi_map_curry_symm μ
  have h₂ := measurePreserving_piCongrLeft (fun p : κ × ι => μ p.2 p.1) (Equiv.prodComm ι κ)
  have h₃ : MeasurePreserving (MeasurableEquiv.curry κ ι X)
      (Measure.pi fun p : κ × ι => μ p.2 p.1)
      (Measure.pi fun j => Measure.pi fun i => μ i j) := by
    refine ⟨(MeasurableEquiv.curry κ ι X).measurable, ?_⟩
    simpa only [Measure.infinitePi_eq_pi] using Measure.infinitePi_map_curry (fun j i => μ i j)
  exact h₃.comp (h₂.comp h₁)

/-- Independent spatial Brownian paths give independent Gaussian vector increments. -/
theorem coordinateLaw_grid_hasLaw {T : ℝ} {n d : ℕ} (τ : Fin (n+1) → Icc 0 T)
    (hτ : Monotone τ) :
    HasLaw (fun w : Fin d → C(Icc 0 T, ℝ) => fun j : Fin n => fun i : Fin d =>
      w i (τ j.succ) - w i (τ j.castSucc))
      (Measure.pi fun j : Fin n => gaussianVectorLaw (0 : Position d)
        (2 * nndist (τ j.succ : ℝ) (τ j.castSucc : ℝ))) (coordinateLaw d T) := by
  have h₁ := measurePreserving_pi (fun _ : Fin d => scalarLaw T)
    (fun _ : Fin d => Measure.pi fun j : Fin n => gaussianReal 0
      (2 * nndist (τ j.succ : ℝ) (τ j.castSucc : ℝ)))
    (fun _ => (scalarLaw_grid_hasLaw τ hτ).measurePreserving (scalarGridIncrement_measurable τ))
  exact ((measurePreserving_pi_transpose (fun (_ : Fin d) (j : Fin n) => gaussianReal 0
    (2 * nndist (τ j.succ : ℝ) (τ j.castSucc : ℝ)))).comp h₁).hasLaw

/-- All particle and spatial Brownian increments have their joint product law. -/
theorem configurationLaw_grid_hasLaw {T : ℝ} {n d N : ℕ} (τ : Fin (n+1) → Icc 0 T)
    (hτ : Monotone τ) :
    HasLaw (fun w : C(Icc 0 T, Configuration d N) => fun j : Fin n =>
      w (τ j.succ) - w (τ j.castSucc))
      (Measure.pi fun j : Fin n => Measure.pi fun _ : Fin N =>
        gaussianVectorLaw (0 : Position d) (2 * nndist (τ j.succ : ℝ) (τ j.castSucc : ℝ)))
      (configurationLaw d N T) := by
  have h₁ := measurePreserving_pi (fun _ : Fin N => coordinateLaw d T)
    (fun _ : Fin N => Measure.pi fun j : Fin n => gaussianVectorLaw (0 : Position d)
      (2 * nndist (τ j.succ : ℝ) (τ j.castSucc : ℝ)))
    (fun _ => (coordinateLaw_grid_hasLaw τ hτ).measurePreserving
      (measurable_pi_lambda _ fun j => measurable_pi_lambda _ fun i =>
        ((by fun_prop : Continuous (fun w : C(Icc 0 T, ℝ) => w (τ j.succ))).measurable.comp (measurable_pi_apply i)).sub
        ((by fun_prop : Continuous (fun w : C(Icc 0 T, ℝ) => w (τ j.castSucc))).measurable.comp (measurable_pi_apply i))))
  have h₂ := (measurePreserving_pi_transpose (fun (_ : Fin N) (j : Fin n) =>
    gaussianVectorLaw (0 : Position d) (2 * nndist (τ j.succ : ℝ) (τ j.castSucc : ℝ)))).comp h₁
  have hm : Measurable (fun w : C(Icc 0 T, Configuration d N) =>
      fun j : Fin n => w (τ j.succ) - w (τ j.castSucc)) :=
    measurable_pi_lambda _ fun j =>
      (by fun_prop : Continuous (fun w : C(Icc 0 T, Configuration d N) => w (τ j.succ) - w (τ j.castSucc))).measurable
  refine ⟨hm.aemeasurable, ?_⟩
  rw [configurationLaw, Measure.map_map hm configurationPath_measurable]
  exact h₂.map_eq

end SharpWasserstein.BrownianNoise
