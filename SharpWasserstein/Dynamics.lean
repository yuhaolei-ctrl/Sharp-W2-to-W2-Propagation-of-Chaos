module

public import SharpWasserstein.Compat
public import SharpWasserstein.Transport
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-! Concrete analytic target of the manuscript. `MainTheorem` below is a
proposition to be proved, NOT a theorem or an axiom. Weak Fokker--Planck
solutions are expressed using genuine derivatives, measures and integrals.
Establishing equivalence with the manuscript's SDEs remains an obligation. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators Interval

namespace SharpWasserstein

def coordinateVector {d N : ℕ} (i : Fin N) (a : Fin d) : Configuration d N :=
  fun j c => if j = i ∧ c = a then 1 else 0

def coordinateDerivative {d N : ℕ} (φ : Configuration d N → ℝ)
    (i : Fin N) (a : Fin d) (x : Configuration d N) : ℝ :=
  fderiv ℝ φ x (coordinateVector i a)

def laplacian {d N : ℕ} (φ : Configuration d N → ℝ) (x : Configuration d N) : ℝ :=
  ∑ i, ∑ a, coordinateDerivative (coordinateDerivative φ i a) i a x

def particleDrift {d N : ℕ} (b : Position d → Position d → Position d)
    (x : Configuration d N) (i : Fin N) : Position d :=
  (N : ℝ)⁻¹ • ∑ j, b (x i) (x j)

def nonlinearDrift {d : ℕ} (b : Position d → Position d → Position d)
    (μ : Measure (Position d)) (x : Position d) : Position d :=
  ∫ y, b x y ∂μ

def generator {d N : ℕ} (v : Configuration d N → Configuration d N)
    (φ : Configuration d N → ℝ) (x : Configuration d N) : ℝ :=
  laplacian φ x + ∑ i, ∑ a, v x i a * coordinateDerivative φ i a x

def SmoothCompactTest {d N : ℕ} (φ : Configuration d N → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ

/-- Integrated weak equation with explicit integrability, probability and
moment conditions. Diffusion coefficient is one, corresponding to sqrt(2) noise. -/
structure WeakEvolution {d N : ℕ}
    (v : ℝ → Configuration d N → Configuration d N)
    (P : ℝ → Measure (Configuration d N)) : Prop where
  probability : ∀ t, 0 ≤ t → IsProbabilityMeasure (P t)
  secondMoment : ∀ t, 0 ≤ t → HasSecondMoment (P t)
  momentBound : ∀ T, 0 < T → ∃ M : ℝ≥0∞, M < ∞ ∧
    ∀ t ∈ Icc 0 T, (∫⁻ x, ENNReal.ofReal (productCost x 0) ∂P t) ≤ M
  testContinuous : ∀ φ, SmoothCompactTest φ →
    ContinuousOn (fun t => ∫ x, φ x ∂P t) (Ici 0)
  generatorIntegrable : ∀ φ, SmoothCompactTest φ → ∀ t, 0 ≤ t →
    Integrable (generator (v t) φ) (P t)
  timeIntegrable : ∀ φ, SmoothCompactTest φ → ∀ t, 0 ≤ t →
    IntervalIntegrable (fun s => ∫ x, generator (v s) φ x ∂P s) volume 0 t
  equation : ∀ φ, SmoothCompactTest φ → ∀ t, 0 ≤ t →
    (∫ x, φ x ∂P t) - (∫ x, φ x ∂P 0) =
      ∫ s in 0..t, ∫ x, generator (v s) φ x ∂P s

structure BoundedSmoothKernel {d : ℕ}
    (b : Position d → Position d → Position d) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry b)
  boundedDerivatives : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ z, ‖iteratedFDeriv ℝ n (Function.uncurry b) z‖ ≤ C

/-- Uniform zeroth- and first-derivative bounds. In finite coordinates the
ambient norm is the sup norm; dimension-dependent equivalence with the
Euclidean norm is included in the allowed dependence on `d`. -/
structure KernelBounds {d : ℕ} (b : Position d → Position d → Position d)
    (M L₁ L₂ : ℝ) : Prop where
  value : ∀ x y, ‖b x y‖ ≤ M
  first : ∀ x y, ‖fderiv ℝ (fun z => b z y) x‖ ≤ L₁
  second : ∀ x y, ‖fderiv ℝ (b x) y‖ ≤ L₂

def IsParticleEvolution {d N : ℕ} (b : Position d → Position d → Position d)
    (P : ℝ → Measure (Configuration d N)) : Prop :=
  WeakEvolution (fun _ x i => particleDrift b x i) P ∧ Exchangeable (P 0)

/-- Embed a one-particle law in the one-coordinate configuration space. -/
def singletonLaw {d : ℕ} (μ : Measure (Position d)) : Measure (Configuration d 1) :=
  Measure.map (fun x (_ : Fin 1) => x) μ

def IsLimitEvolution {d : ℕ} (b : Position d → Position d → Position d)
    (μ : ℝ → Measure (Position d)) : Prop :=
  (∀ t, 0 ≤ t → IsProbabilityMeasure (μ t)) ∧
  WeakEvolution (fun t x i => nonlinearDrift b (μ t) (x i)) (fun t => singletonLaw (μ t))

def InitialHierarchy {d : ℕ} (C₀ : ℝ) (μ : Measure (Position d))
    (P : (N : ℕ) → Measure (Configuration d N)) : Prop :=
  ∀ N, 1 ≤ N → ∀ k, 1 ≤ k → ∀ hk : k ≤ N,
    wassersteinSq (marginal hk (P N)) (tensorLaw μ k) ≤
      ENNReal.ofReal (C₀ * (k : ℝ) ^ 2 / (N : ℝ) ^ 2)

def PropagatedHierarchy {d : ℕ} (C T : ℝ) (μ : ℝ → Measure (Position d))
    (P : (N : ℕ) → ℝ → Measure (Configuration d N)) : Prop :=
  ∀ N, 1 ≤ N → ∀ k, 1 ≤ k → ∀ hk : k ≤ N, ∀ t ∈ Icc 0 T,
    wassersteinSq (marginal hk (P N t)) (tensorLaw (μ t) k) ≤
      ENNReal.ofReal (C * (k : ℝ) ^ 2 / (N : ℝ) ^ 2)

/-- OPEN TARGET. This declaration only specifies a proposition. It does not
assert its truth. Constants are outside the quantifiers over all initial laws
and all particle numbers, as required in the manuscript. -/
def MainTheorem : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∀ C₀ T M L₁ L₂ : ℝ,
    0 ≤ C₀ → 0 < T → 0 ≤ M → 0 ≤ L₁ → 0 ≤ L₂ →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (b : Position d → Position d → Position d)
        (μ : ℝ → Measure (Position d))
        (P : (N : ℕ) → ℝ → Measure (Configuration d N)),
        BoundedSmoothKernel b → KernelBounds b M L₁ L₂ →
        IsLimitEvolution b μ →
        (∀ N, 1 ≤ N → IsParticleEvolution b (P N)) →
        InitialHierarchy C₀ (μ 0) (fun N => P N 0) →
        PropagatedHierarchy C T μ P

end SharpWasserstein
