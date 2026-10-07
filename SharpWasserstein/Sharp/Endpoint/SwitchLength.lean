/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import SharpWasserstein.PrescribedSwitchLengthFromAction
public import SharpWasserstein.RoughFiniteAction
public import SharpWasserstein.Sharp.EndpointLength

/-!
# The length of the interpolating curve with the sharp speed

This file carries out the central step of the proof of the smooth case of Theorem 2.1
(Section 3.4, `sec:proof-main`): the bound on the transport length of the marginal
interpolating curve `s ↦ ν^{N,t,(k)}_s = (S^{N,*}_{t-s} R^N_s)^{(k)}` of `eq:switch`,
```
W(P^{(k)}_{N,t}, R^{(k)}_t) ≤ ∫₀ᵗ g(s) ds = c (A₀ t + 2 A₁ √t) k/N,
g(s) = c (A₀ + A₁/√s) k/N,
```
from a bound `E(s) ≤ g(s)²` on the tangent energy `E(s)` of the derivative of the curve
(Lemma 3.8, `lem:switch`, and Lemma 3.2, `lem:energy`). The constants `c, A₀, A₁ ≥ 0` are
arbitrary here; in Section 3.4, `c = e^{ωt/2}`.

As in the development, the switch time is called `T` in this file, and the curve is
`PrescribedSwitchCurve.law … hT P s`, `0 ≤ s ≤ T`. The proof of the length lemma
(Lemma 3.4, `lem:length`) is split in two parts, exactly as in the paper:
* on an interval `[a, b] ⊆ (0, T]`, the energy is at most `(c (A₀ + A₁/√a))² (k/N)²`, since
  `g` is antitone, and the uniform finite-action transport theorem
  `RoughEulerianTransport.uniform_finite_action_transport` gives
  `W(ν_a, ν_b) ≤ (b - a) c (A₀ + A₁/√a) k/N`;
* `SharpWasserstein.Sharp.endpoint_of_sqrt_action_mul` sums these bounds and uses the
  continuity of the curve at `0` to get `W(ν_0, ν_T) ≤ c (A₀ T + 2 A₁ √T) k/N`.

This replaces the old chain `prescribedMetricCurve_length_of_finiteAction` /
`prescribed_switch_length_of_finiteAction`, whose energy bound `C (1 + 1/a) k²/N²` gave the
non-sharp length `√C (T + 3√T) k/N`.

## Main statements

* `prescribedMetricCurve_length_sharp`: the length bound, assuming the energy bound for the
  marginal curve and its source.
* `prescribed_switch_length_sharp`: the same bound for the Wasserstein distance between the
  marginals of the interpolating curve at `0` and at `T`, assuming the energy bound in the
  form of `BrownianEnergyPeriodization.prefixEnergy` (the form of the old
  `RegularizedBrownianSource.prefixEnergy_le`).
* `prescribed_switch_length_exp`: the case `E(s) ≤ (A₀ + A₁/√s)² e^{ω(T-s)} k²/N²` of
  Section 3.4, with `c = e^{ωT/2}`.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory

namespace SharpWasserstein.Sharp.Endpoint

open WeightedTangent RegularizedBrownianSource RoughEulerianTransport SwitchSourceDerivative
open InitialSourcePermutation

variable {d N k : ℕ} {b : Position d → Position d → Position d} {Mb Lb₁ Lb₂ : ℝ}
  (hN : 0 < N) (hb : BoundedSmoothKernel b) (hbound : KernelBounds b Mb Lb₁ Lb₂)
  (hMb : 0 ≤ Mb) (hLb₁ : 0 ≤ Lb₁) (hLb₂ : 0 ≤ Lb₂)
  {μ : ℝ → Measure (Position d)} (hμ : IsLimitEvolution b μ)
  {T : ℝ} (hT : 0 ≤ T) (P : Measure (Configuration d N)) [IsProbabilityMeasure P]
  (hP : HasSecondMoment P) (hk : k ≤ N) {c A₀ A₁ : ℝ}

/-- On an interval `[a, T]` with `a > 0`, every test objective of the marginal source is bounded
by the energy bound at the left endpoint `a`, because `s ↦ (c (A₀ + A₁/√s))²` is antitone. -/
theorem prescribedMarginalCurve_testObjective_le_sharp (hc : 0 ≤ c) (hA₀ : 0 ≤ A₀)
    (hA₁ : 0 ≤ A₁)
    (henergy : ∀ s, 0 < s → s ≤ T →
      energy (prescribedMarginalCurve hN hb hbound hMb hLb₁ hLb₂ hμ hT P hk s : Measure _)
          (prescribedMarginalSource hN hb hbound hMb hLb₁ hLb₂ hμ hT P hk s) ≤
        (c * (A₀ + A₁ / Real.sqrt s)) ^ 2 * ((k : ℝ) / N) ^ 2)
    {a s : ℝ} (ha : 0 < a) (has : a ≤ s) (hsT : s ≤ T) (φ : Test (k * d)) :
    testObjective (prescribedMarginalCurve hN hb hbound hMb hLb₁ hLb₂ hμ hT P hk s : Measure _)
        (prescribedMarginalSource hN hb hbound hMb hLb₁ hLb₂ hμ hT P hk s) φ ≤
      (c * (A₀ + A₁ / Real.sqrt a)) ^ 2 * ((k : ℝ) / N) ^ 2 := by
  have hs := ha.trans_le has
  have hfin := prescribedMarginalSource_finite hN hb hbound hMb hLb₁ hLb₂ hμ hT P hk ⟨hs.le, hsT⟩
  refine (le_csSup hfin (mem_range_self φ)).trans ((henergy s hs hsT).trans ?_)
  have hsa : Real.sqrt a ≤ Real.sqrt s := Real.sqrt_le_sqrt has
  have hsa' : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  gcongr

/-- **Sharp length of the marginal interpolating curve.** If, for `0 < s ≤ T`, the tangent
energy of the marginal source is at most `(c (A₀ + A₁/√s))² (k/N)²`, then the Wasserstein
distance between the marginal laws at `0` and at `T` is at most `c (A₀ T + 2 A₁ √T) k/N`. -/
theorem prescribedMetricCurve_length_sharp (hc : 0 ≤ c) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (henergy : ∀ s, 0 < s → s ≤ T →
      energy (prescribedMarginalCurve hN hb hbound hMb hLb₁ hLb₂ hμ hT P hk s : Measure _)
          (prescribedMarginalSource hN hb hbound hMb hLb₁ hLb₂ hμ hT P hk s) ≤
        (c * (A₀ + A₁ / Real.sqrt s)) ^ 2 * ((k : ℝ) / N) ^ 2) :
    dist (prescribedMarginalMetricCurve hN hb hbound hMb hLb₁ hLb₂ hμ hT P hP hk 0)
        (prescribedMarginalMetricCurve hN hb hbound hMb hLb₁ hLb₂ hμ hT P hP hk T) ≤
      c * (A₀ * T + 2 * A₁ * Real.sqrt T) * ((k : ℝ) / N) := by
  rcases eq_or_lt_of_le hT with hzero | hpos
  · subst T
    simp
  have hr : 0 ≤ (k : ℝ) / N := by positivity
  refine (endpoint_of_sqrt_action_mul (c := c * ((k : ℝ) / N)) hpos (mul_nonneg hc hr) hA₀ hA₁
    (prescribedMarginalMetricCurve_continuous hN hb hbound hMb hLb₁ hLb₂ hμ hT P hP
      hk).continuousAt.continuousWithinAt ?_).trans_eq (by ring)
  intro s₁ s₂ hs₁ hs₁₂ hs₂T
  have hE : 0 ≤ (c * (A₀ + A₁ / Real.sqrt s₁)) ^ 2 * ((k : ℝ) / N) ^ 2 := by positivity
  have hcont := (prescribed_marginal_compactDistributionContinuity hN hb hbound hMb hLb₁ hLb₂ hμ
    hT P hk).translate hs₁.le hs₂T
  have ht := uniform_finite_action_transport d k
    (fun r => prescribedMarginalCurve hN hb hbound hMb hLb₁ hLb₂ hμ hT P hk (s₁ + r))
    (fun r => prescribedMarginalSource hN hb hbound hMb hLb₁ hLb₂ hμ hT P hk (s₁ + r))
    (s₂ - s₁) _ (sub_nonneg.mpr hs₁₂) hE hcont
    ⟨(prescribedMarginalCommonLabel hN hb hbound hMb hLb₁ hLb₂ hμ hT P hP hk).translate s₁⟩
    (fun r _ => prescribedMarginalCurve_secondMoment hN hb hbound hMb hLb₁ hLb₂ hμ hT P hP hk
      (s₁ + r))
    (fun r hr φ => prescribedMarginalCurve_testObjective_le_sharp hN hb hbound hMb hLb₁ hLb₂ hμ
      hT P hk hc hA₀ hA₁ henergy hs₁ (by linarith [hr.1]) (by linarith [hr.2]) φ)
  simp only [add_zero, add_sub_cancel] at ht
  rw [prescribedMarginalCurve_map_configuration hN hb hbound hMb hLb₁ hLb₂ hμ hT P hP hk s₁,
    prescribedMarginalCurve_map_configuration hN hb hbound hMb hLb₁ hLb₂ hμ hT P hP hk s₂] at ht
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top ht
  rw [ENNReal.toReal_ofReal (mul_nonneg (sq_nonneg _) hE)] at hreal
  have hX : 0 ≤ (s₂ - s₁) * (c * ((k : ℝ) / N) * (A₀ + A₁ / Real.sqrt s₁)) := by
    have := sub_nonneg.mpr hs₁₂
    positivity
  rw [quadraticProbability_dist_eq]
  calc Real.sqrt _ ≤ Real.sqrt (((s₂ - s₁) * (c * ((k : ℝ) / N) * (A₀ + A₁ / Real.sqrt s₁))) ^ 2) :=
        Real.sqrt_le_sqrt (hreal.trans_eq (by ring))
    _ = _ := Real.sqrt_sq hX

/-- The tangent energy of the marginal interpolating curve at a switch time `0 ≤ s ≤ T` is the
propagated prefix energy of the reference law `R^N_s` and of the current `U_s`, transported for
the remaining time `T - s` (`RegularizedBrownianSource.prescribed_marginal_energy_eq_prefix`). -/
theorem prescribedMarginalCurve_energy_eq_prefixEnergy {s : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T) :
    letI : IsProbabilityMeasure (PrescribedReference.law hb hbound hMb hLb₁ hμ N P s) :=
      law_probability hb hbound hMb hLb₁ hμ P hP hs
    energy (prescribedMarginalCurve hN hb hbound hMb hLb₁ hLb₂ hμ hT P hk s : Measure _)
        (prescribedMarginalSource hN hb hbound hMb hLb₁ hLb₂ hμ hT P hk s) =
      BrownianEnergyPeriodization.prefixEnergy hN hb hbound hMb hLb₁ hLb₂ hT
        (euclideanLaw (PrescribedReference.law hb hbound hMb hLb₁ hμ N P s)) hk
        (euclideanFlux (initialCurrent b (μ s))) (current_memLp hb hbound hMb hLb₁ hμ P hP hN hs)
        (T - s) := by
  have : IsProbabilityMeasure (PrescribedSwitchCurve.law hN hb hbound hMb hLb₁ hLb₂ hμ hT P s) :=
    SwitchCurve.law_probability hN hb hbound hMb hLb₁ hLb₂ _ _ _ hT P ⟨hs, hsT⟩
  rw [prescribedMarginalCurve_coe hN hb hbound hMb hLb₁ hLb₂ hμ hT P hk ⟨hs, hsT⟩,
    prescribedMarginalSource_eq hN hb hbound hMb hLb₁ hLb₂ hμ hT P hk ⟨hs, hsT⟩]
  exact prescribed_marginal_energy_eq_prefix hN hb hbound hMb hLb₁ hLb₂ hμ hT P hP ⟨hs, hsT⟩ hk

/-- **Sharp switch length.** Assume that, for every `0 < s ≤ T`, the propagated prefix energy
of the source at switch time `s` (the tangent energy of the derivative of the marginal
interpolating curve, in the form of the old `RegularizedBrownianSource.prefixEnergy_le`) is at
most `(c (A₀ + A₁/√s))² (k/N)²`. Then
`√W²(ν^{(k)}_0, ν^{(k)}_T) ≤ c (A₀ T + 2 A₁ √T) k/N` for the interpolating curve `ν`. -/
theorem prescribed_switch_length_sharp (hc : 0 ≤ c) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (henergy : ∀ s (hs : 0 < s), s ≤ T →
      letI : IsProbabilityMeasure (PrescribedReference.law hb hbound hMb hLb₁ hμ N P s) :=
        law_probability hb hbound hMb hLb₁ hμ P hP hs.le
      BrownianEnergyPeriodization.prefixEnergy hN hb hbound hMb hLb₁ hLb₂ hT
          (euclideanLaw (PrescribedReference.law hb hbound hMb hLb₁ hμ N P s)) hk
          (euclideanFlux (initialCurrent b (μ s)))
          (current_memLp hb hbound hMb hLb₁ hμ P hP hN hs.le) (T - s) ≤
        (c * (A₀ + A₁ / Real.sqrt s)) ^ 2 * ((k : ℝ) / N) ^ 2) :
    Real.sqrt (wassersteinSq
        (marginal hk (PrescribedSwitchCurve.law hN hb hbound hMb hLb₁ hLb₂ hμ hT P 0))
        (marginal hk (PrescribedSwitchCurve.law hN hb hbound hMb hLb₁ hLb₂ hμ hT P T))).toReal ≤
      c * (A₀ * T + 2 * A₁ * Real.sqrt T) * ((k : ℝ) / N) := by
  have he := prescribedMetricCurve_length_sharp hN hb hbound hMb hLb₁ hLb₂ hμ hT P hP hk hc hA₀ hA₁
    fun s hs hsT => (prescribedMarginalCurve_energy_eq_prefixEnergy hN hb hbound hMb hLb₁ hLb₂ hμ
      hT P hP hk hs.le hsT).trans_le (henergy s hs hsT)
  rw [quadraticProbability_dist_eq] at he
  simpa only [prescribedMarginalMetricCurve,
    projIcc_of_mem _ (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩),
    projIcc_of_mem _ (show T ∈ Icc 0 T from ⟨hT, le_rfl⟩)] using he

/-- `A² e^{ω(T-s)} r² ≤ (e^{ωT/2} A)² r²` for `ω ≥ 0` and `s ≥ 0`; it is used with
`A = A₀ + A₁/√s`. -/
theorem sq_mul_exp_le {ω A r s : ℝ} (hω : 0 ≤ ω) (hs : 0 ≤ s) :
    A ^ 2 * Real.exp (ω * (T - s)) * r ^ 2 ≤ (Real.exp (ω * T / 2) * A) ^ 2 * r ^ 2 := by
  have hexp : Real.exp (ω * T / 2) ^ 2 = Real.exp (ω * T) := by
    rw [sq, ← Real.exp_add]
    ring_nf
  have hle : Real.exp (ω * (T - s)) ≤ Real.exp (ω * T) :=
    Real.exp_le_exp.2 (by nlinarith)
  rw [mul_pow, hexp]
  have := sq_nonneg A
  have := sq_nonneg r
  calc A ^ 2 * Real.exp (ω * (T - s)) * r ^ 2 ≤ A ^ 2 * Real.exp (ω * T) * r ^ 2 := by gcongr
    _ = _ := by ring

/-- **Sharp switch length, in the form of Section 3.4.** If the propagated prefix energy at
switch time `0 < s ≤ T` is at most `(A₀ + A₁/√s)² e^{ω(T-s)} k²/N²` with `ω ≥ 0`
(Propositions 3.6 and 3.7), then `√W²(ν^{(k)}_0, ν^{(k)}_T) ≤ e^{ωT/2} (A₀ T + 2 A₁ √T) k/N`. -/
theorem prescribed_switch_length_exp {ω : ℝ} (hω : 0 ≤ ω) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (henergy : ∀ s (hs : 0 < s), s ≤ T →
      letI : IsProbabilityMeasure (PrescribedReference.law hb hbound hMb hLb₁ hμ N P s) :=
        law_probability hb hbound hMb hLb₁ hμ P hP hs.le
      BrownianEnergyPeriodization.prefixEnergy hN hb hbound hMb hLb₁ hLb₂ hT
          (euclideanLaw (PrescribedReference.law hb hbound hMb hLb₁ hμ N P s)) hk
          (euclideanFlux (initialCurrent b (μ s)))
          (current_memLp hb hbound hMb hLb₁ hμ P hP hN hs.le) (T - s) ≤
        (A₀ + A₁ / Real.sqrt s) ^ 2 * Real.exp (ω * (T - s)) * (k : ℝ) ^ 2 / (N : ℝ) ^ 2) :
    Real.sqrt (wassersteinSq
        (marginal hk (PrescribedSwitchCurve.law hN hb hbound hMb hLb₁ hLb₂ hμ hT P 0))
        (marginal hk (PrescribedSwitchCurve.law hN hb hbound hMb hLb₁ hLb₂ hμ hT P T))).toReal ≤
      Real.exp (ω * T / 2) * (A₀ * T + 2 * A₁ * Real.sqrt T) * ((k : ℝ) / N) := by
  refine prescribed_switch_length_sharp hN hb hbound hMb hLb₁ hLb₂ hμ hT P hP hk
    (Real.exp_pos _).le hA₀ hA₁ fun s hs hsT => (henergy s hs hsT).trans ?_
  rw [mul_div_assoc, ← div_pow]
  exact sq_mul_exp_le hω hs.le

end SharpWasserstein.Sharp.Endpoint
