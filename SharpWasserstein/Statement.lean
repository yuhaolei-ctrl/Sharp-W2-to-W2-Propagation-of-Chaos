/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Independence.Basic

/-!
# Definitions of the public statement

The definitions used by the statement in `Challenge.lean`, copied verbatim (this file is generated
by `scripts/sync-statement.py`). The development and `Solution.lean` use these declarations, so
that Comparator finds the same definitions in the Challenge and Solution environments.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace SharpChaos

/-- **Assumption A.** The one-body drift `a` is `L_a`-Lipschitz, the interaction `K` is bounded by
`M`, and `|K(x,y) - K(x',y')| ≤ L₁|x - x'| + L₂|y - y'|`, for constants `L_a, L₁, L₂, M ≥ 0`.
All norms are Euclidean. -/
structure AssumptionA {d : ℕ} (a : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (La L₁ L₂ M : ℝ) : Prop where
  La_nonneg : 0 ≤ La
  L₁_nonneg : 0 ≤ L₁
  L₂_nonneg : 0 ≤ L₂
  M_nonneg : 0 ≤ M
  lipschitz_a : ∀ x x', ‖a x - a x'‖ ≤ La * ‖x - x'‖
  norm_K_le : ∀ x y, ‖K x y‖ ≤ M
  lipschitz_K : ∀ x x' y y', ‖K x y - K x' y'‖ ≤ L₁ * ‖x - x'‖ + L₂ * ‖y - y'‖

/-- The unnormalized squared Euclidean distance `∑ᵢ ‖xᵢ - yᵢ‖²` between two configurations of `k`
particles in `ℝᵈ`. -/
def sqDist {d k : ℕ} (x y : Fin k → EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i, ‖x i - y i‖ ^ 2

/-- `π` is a coupling of `μ` and `ν`: a probability measure on the product with marginals `μ`
and `ν`. (For probability measures `μ` and `ν` the first condition follows from the others.) -/
def IsCoupling {α : Type*} [MeasurableSpace α] (μ ν : Measure α) (π : Measure (α × α)) :
    Prop :=
  IsProbabilityMeasure π ∧ π.map Prod.fst = μ ∧ π.map Prod.snd = ν

/-- The squared quadratic Wasserstein distance between two laws of `k` particles in `ℝᵈ`:
`W₂²(μ, ν) = inf_π ∫ ∑ᵢ ‖xᵢ - yᵢ‖² dπ(x, y)` over all couplings `π` of `μ` and `ν`. -/
def wassersteinSq {d k : ℕ} (μ ν : Measure (Fin k → EuclideanSpace ℝ (Fin d))) : ℝ≥0∞ :=
  ⨅ (π : Measure ((Fin k → EuclideanSpace ℝ (Fin d)) × (Fin k → EuclideanSpace ℝ (Fin d))))
    (_ : IsCoupling μ ν π), ∫⁻ z, ENNReal.ofReal (sqDist z.1 z.2) ∂π

/-- The joint law `P^{(k)}` of the first `k` particles under a law `P` of `N ≥ k` particles. -/
def marginal {d k N : ℕ} (hk : k ≤ N) (P : Measure (Fin N → EuclideanSpace ℝ (Fin d))) :
    Measure (Fin k → EuclideanSpace ℝ (Fin d)) :=
  P.map fun x i => x (Fin.castLE hk i)

/-- A law of `N` particles is exchangeable if it is invariant under permutations of the
particles. -/
def Exchangeable {d N : ℕ} (P : Measure (Fin N → EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ σ : Equiv.Perm (Fin N), P.map (fun x i => x (σ i)) = P

/-- `B` is a standard Brownian motion in `ℝᵈ`: its `d` coordinates are independent standard real
Brownian motions with almost surely continuous paths. -/
def IsStandardBrownian {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (P : Measure Ω) : Prop :=
  (∀ c : Fin d, IsBrownianReal (fun t ω => B t ω c) P) ∧
    iIndepFun (fun (c : Fin d) (ω : Ω) (t : ℝ≥0) => B t ω c) P

/-- The drift of the particle system (1.1): `b_N(x)ᵢ = a(xᵢ) + N⁻¹ ∑ⱼ K(xᵢ, xⱼ)`. The diagonal
term `j = i` is included. -/
def particleDrift {d N : ℕ} (a : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (x : Fin N → EuclideanSpace ℝ (Fin d)) : Fin N → EuclideanSpace ℝ (Fin d) :=
  fun i => a (x i) + (N : ℝ)⁻¹ • ∑ j, K (x i) (x j)

/-- `X` is a strong solution of the particle system (1.1) driven by the Brownian motions
`W₁, …, W_N`: the `Wᵢ` are independent standard Brownian motions in `ℝᵈ`, independent of the
initial configuration `X(0)`; each `X(t)`, `t ≥ 0`, is a random variable; and almost surely the path
`t ↦ X(t)` is continuous on `[0, ∞)` and satisfies, for all `t ≥ 0`,
`X(t) = X(0) + ∫₀ᵗ b_N(X(s)) ds + √2 W(t)`. -/
structure IsParticleSolution {Ω : Type*} [MeasurableSpace Ω] {d N : ℕ}
    (a : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (X : ℝ → Ω → Fin N → EuclideanSpace ℝ (Fin d))
    (W : Fin N → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (P : Measure Ω) : Prop where
  aemeasurable : ∀ t, 0 ≤ t → AEMeasurable (X t) P
  brownian : ∀ i, IsStandardBrownian (W i) P
  iIndepFun_brownian : iIndepFun (fun (i : Fin N) (ω : Ω) (t : ℝ≥0) => W i t ω) P
  indepFun_initial : IndepFun (X 0) (fun (ω : Ω) (i : Fin N) (t : ℝ≥0) => W i t ω) P
  solves : ∀ᵐ ω ∂P, ContinuousOn (fun t => X t ω) (Ici 0) ∧
    ∀ t : ℝ, 0 ≤ t → X t ω =
      X 0 ω + (∫ s in (0 : ℝ)..t, particleDrift a K (X s ω)) +
        fun i => Real.sqrt 2 • W i t.toNNReal ω

/-- The drift of the McKean–Vlasov equation (1.2) for a law `μ`:
`B(x) = a(x) + ∫ K(x, y) μ(dy)`. -/
def mcKeanVlasovDrift {d : ℕ} (a : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (μ : Measure (EuclideanSpace ℝ (Fin d))) (x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  a x + ∫ y, K x y ∂μ

/-- `Y` is a strong solution of the McKean–Vlasov equation (1.2) driven by the Brownian motion
`B`: `B` is a standard Brownian motion in `ℝᵈ` independent of `Y(0)`; each `Y(t)`, `t ≥ 0`, is a
random variable; and almost surely the path `t ↦ Y(t)` is continuous on `[0, ∞)` and satisfies,
for all `t ≥ 0`, `Y(t) = Y(0) + ∫₀ᵗ (a(Y(s)) + ∫ K(Y(s), y) μ_s(dy)) ds + √2 B(t)` with
`μ_s = Law(Y(s))`. -/
structure IsMcKeanVlasovSolution {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (a : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (Y : ℝ → Ω → EuclideanSpace ℝ (Fin d)) (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (P : Measure Ω) : Prop where
  aemeasurable : ∀ t, 0 ≤ t → AEMeasurable (Y t) P
  brownian : IsStandardBrownian B P
  indepFun_initial : IndepFun (Y 0) (fun (ω : Ω) (t : ℝ≥0) => B t ω) P
  solves : ∀ᵐ ω ∂P, ContinuousOn (fun t => Y t ω) (Ici 0) ∧
    ∀ t : ℝ, 0 ≤ t → Y t ω =
      Y 0 ω + (∫ s in (0 : ℝ)..t, mcKeanVlasovDrift a K (P.map (Y s)) (Y s ω)) +
        Real.sqrt 2 • B t.toNNReal ω

/-- The explicit constant `C_T` of (2.6)–(2.9):
`L = L_a + L₁`, `Λ = L_a + L₁ + L₂`, `L_c = 2L₁ + L₂`, `G = 2L₁² + L₂² + 2M²`, `λ = 2G`,
`D = 2Λ + 2L₁ + 1`, `ω = D + 3λ`, `D_T = (1 + LT + L²T²/3)/4`, `A₀ = 2M + L_c e^{LT} √C₀`,
`A₁ = √8 M √(C₀ D_T)` and `C_T = (e^{LT} √C₀ + e^{ωT/2} (A₀ T + 2 A₁ √T))²`. -/
def sharpConstant (C₀ T La L₁ L₂ M : ℝ) : ℝ :=
  let L := La + L₁
  let Λ := La + L₁ + L₂
  let Lc := 2 * L₁ + L₂
  let G := 2 * L₁ ^ 2 + L₂ ^ 2 + 2 * M ^ 2
  let lam := 2 * G
  let D := 2 * Λ + 2 * L₁ + 1
  let omega := D + 3 * lam
  let DT := (1 + L * T + L ^ 2 * T ^ 2 / 3) / 4
  let A₀ := 2 * M + Lc * Real.exp (L * T) * Real.sqrt C₀
  let A₁ := Real.sqrt 8 * M * Real.sqrt (C₀ * DT)
  (Real.exp (L * T) * Real.sqrt C₀ + Real.exp (omega * T / 2) * (A₀ * T + 2 * A₁ * Real.sqrt T)) ^ 2

end SharpChaos
