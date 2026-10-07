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
# Sharp Wasserstein propagation of chaos from correlated initial data

This file states Theorem 2.1 of Y. Lei, *Sharp Wasserstein propagation of chaos from correlated
initial data*. Consider `N` particles in `ℝᵈ` solving

`dXᵢ(t) = (a(Xᵢ(t)) + N⁻¹ ∑ⱼ K(Xᵢ(t), Xⱼ(t))) dt + √2 dWᵢ(t)`,    `1 ≤ i ≤ N`,      (1.1)

with independent Brownian motions `W₁, …, W_N` and an exchangeable initial law `P_{N,0}`, and the
McKean–Vlasov equation

`dX(t) = (a(X(t)) + ∫ K(X(t), y) μ_t(dy)) dt + √2 dW(t)`,    `μ_t = Law(X(t))`.          (1.2)

Assume that `a` is `L_a`-Lipschitz, that `|K| ≤ M` and that
`|K(x,y) - K(x',y')| ≤ L₁|x - x'| + L₂|y - y'|` (Assumption A, (2.1)–(2.3)), all norms being
Euclidean. If the `k`-particle marginals of the initial law satisfy
`W₂²(P^{(k)}_{N,0}, μ₀^{⊗k}) ≤ C₀ k²/N²` for `1 ≤ k ≤ N` (2.4), then for every `T > 0`
`W₂²(P^{(k)}_{N,t}, μ_t^{⊗k}) ≤ C_T k²/N²` for `0 ≤ t ≤ T` and `1 ≤ k ≤ N` (2.5), with the
explicit constant `C_T` defined by the displayed formulas (2.6)–(2.9) after Theorem 2.1, which
depends neither on `N` nor on `d`. Equation numbers refer to the LaTeX source of the paper.

`P_{N,t}` is the law of `X(t)` and `μ_t` the law of the McKean–Vlasov process at time `t`.

## Conventions

* Positions live in `EuclideanSpace ℝ (Fin d)`, so `‖·‖` is the Euclidean norm. A configuration of
  `k` particles is a function `Fin k → EuclideanSpace ℝ (Fin d)`; its transport cost is the
  unnormalized squared distance `∑ᵢ ‖xᵢ - yᵢ‖²`, as in the paper.
* `wassersteinSq μ ν` is the squared quadratic Wasserstein distance, the infimum of the transport
  cost over all couplings, with values in `[0, ∞]`. Finite second moments (`𝒫₂`) are expressed by
  `MemLp _ 2`, which does not depend on the choice of norm.
* The solution processes `X`, `Y` are indexed by `t : ℝ`; only times `t ≥ 0` are constrained. The
  Brownian motions are indexed by `ℝ≥0`, and `t.toNNReal` converts. The driving noise consists of
  independent standard Brownian motions in the sense of Mathlib's
  `ProbabilityTheory.IsBrownianReal`, independent of the initial condition.
* Solutions are strong solutions: random variables with almost surely continuous paths satisfying
  the integral form of the equation for all `t ≥ 0`, almost surely. No filtration is mentioned:
  since the noise is additive and the drifts are Lipschitz, almost every path is the unique
  continuous solution of a deterministic integral equation driven by the initial value and the
  Brownian path, so a solution is automatically a functional of these and its laws are determined
  (Lemma 3.1 of the paper).
* The particle system and the McKean–Vlasov process may live on different probability spaces.
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

/-- **Theorem 2.1.** Under Assumption A, let `X` solve the particle system (1.1) with an
exchangeable initial law `P_{N,0} ∈ 𝒫₂((ℝᵈ)ᴺ)`, and let `Y` solve the McKean–Vlasov equation (1.2)
with `μ₀ = Law(Y(0)) ∈ 𝒫₂(ℝᵈ)`. If `W₂²(P^{(k)}_{N,0}, μ₀^{⊗k}) ≤ C₀ k²/N²` for `1 ≤ k ≤ N`, then
for every `T > 0`, all `0 ≤ t ≤ T` and `1 ≤ k ≤ N`,
`W₂²(P^{(k)}_{N,t}, μ_t^{⊗k}) ≤ C_T k²/N²` (2.5), where `C_T = sharpConstant C₀ T L_a L₁ L₂ M`. -/
theorem sharp_propagation_of_chaos {d N : ℕ} (hN : 1 ≤ N)
    {a : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {La L₁ L₂ M : ℝ} (hA : AssumptionA a K La L₁ L₂ M)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℝ → Ω → Fin N → EuclideanSpace ℝ (Fin d)}
    {W : Fin N → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hX : IsParticleSolution a K X W P)
    (hX₀ : MemLp (X 0) 2 P) (hexch : Exchangeable (P.map (X 0)))
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : ℝ → Ω' → EuclideanSpace ℝ (Fin d)} {B : ℝ≥0 → Ω' → EuclideanSpace ℝ (Fin d)}
    (hY : IsMcKeanVlasovSolution a K Y B P') (hY₀ : MemLp (Y 0) 2 P')
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hinit : ∀ k (hk : k ≤ N), 1 ≤ k →
      wassersteinSq (marginal hk (P.map (X 0))) (Measure.pi fun _ : Fin k => P'.map (Y 0)) ≤
        ENNReal.ofReal (C₀ * k ^ 2 / N ^ 2))
    {T : ℝ} (hT : 0 < T) :
    ∀ t ∈ Icc 0 T, ∀ k (hk : k ≤ N), 1 ≤ k →
      wassersteinSq (marginal hk (P.map (X t))) (Measure.pi fun _ : Fin k => P'.map (Y t)) ≤
        ENNReal.ofReal (sharpConstant C₀ T La L₁ L₂ M * k ^ 2 / N ^ 2) := by
  sorry

end SharpChaos
