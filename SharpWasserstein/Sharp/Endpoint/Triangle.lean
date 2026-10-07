/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import SharpWasserstein.TransportTriangle

/-!
# The sharp triangle inequality for `W²`

The last step of the proof of the smooth case of Theorem 2.1 (Section 3.4, `sec:proof-main`)
adds the bound `W(P^{(k)}_{N,t}, R^{(k)}_t) ≤ S k/N` on the length of the interpolating curve
and the bound `W(R^{(k)}_t, μ_t^{⊗k}) ≤ D k/N` of Lemma 3.5 (`lem:reference-W`), and squares:
`W²(P^{(k)}_{N,t}, μ_t^{⊗k}) ≤ (S + D)² k²/N²`. This file proves this step for the squared
Wasserstein cost `wassersteinSq` of the development, from the triangle inequality
`wassersteinSq_sqrt_triangle`, without the factor `2` of the old
`WassersteinEndpoint.transport_triangle_bound` (which gave `2 (S² + D) r²`).

## Main statements

* `wassersteinSq_le_of_sqrt_le`: from `√W²(μ, ν) ≤ S r` and `√W²(ν, ρ) ≤ D r`,
  `W²(μ, ρ) ≤ (S + D)² r²`.
* `sqrt_wassersteinSq_le_of_le_sq`: from `W²(μ, ν) ≤ Y²` with `Y ≥ 0`, `√W²(μ, ν) ≤ Y`.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace SharpWasserstein.Sharp.Endpoint

variable {d k : ℕ}

/-- A bound `W²(μ, ν) ≤ Y²` with `Y ≥ 0` gives `√W²(μ, ν) ≤ Y` for the real square root of the
real part of the cost. -/
theorem sqrt_wassersteinSq_le_of_le_sq {μ ν : Measure (Configuration d k)} {Y : ℝ} (hY : 0 ≤ Y)
    (h : wassersteinSq μ ν ≤ ENNReal.ofReal (Y ^ 2)) :
    Real.sqrt (wassersteinSq μ ν).toReal ≤ Y := by
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [ENNReal.toReal_ofReal (sq_nonneg Y)] at hreal
  calc Real.sqrt (wassersteinSq μ ν).toReal ≤ Real.sqrt (Y ^ 2) := Real.sqrt_le_sqrt hreal
    _ = Y := Real.sqrt_sq hY

/-- **Sharp triangle inequality.** For probability laws with second moments, the bounds
`√W²(μ, ν) ≤ S r` and `√W²(ν, ρ) ≤ D r` give `W²(μ, ρ) ≤ (S + D)² r²`. -/
theorem wassersteinSq_le_of_sqrt_le (μ ν ρ : Measure (Configuration d k))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (hμ : HasSecondMoment μ) (hν : HasSecondMoment ν) (hρ : HasSecondMoment ρ) {S D r : ℝ}
    (hleft : Real.sqrt (wassersteinSq μ ν).toReal ≤ S * r)
    (hright : Real.sqrt (wassersteinSq ν ρ).toReal ≤ D * r) :
    wassersteinSq μ ρ ≤ ENNReal.ofReal ((S + D) ^ 2 * r ^ 2) := by
  have hsum : Real.sqrt (wassersteinSq μ ρ).toReal ≤ (S + D) * r := by
    linarith [wassersteinSq_sqrt_triangle μ ν ρ hμ hν hρ]
  have hsq : (wassersteinSq μ ρ).toReal ≤ ((S + D) * r) ^ 2 :=
    calc (wassersteinSq μ ρ).toReal = Real.sqrt (wassersteinSq μ ρ).toReal ^ 2 :=
          (Real.sq_sqrt ENNReal.toReal_nonneg).symm
      _ ≤ ((S + D) * r) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsum 2
  rw [← ENNReal.ofReal_toReal (wassersteinSq_lt_top μ ρ hμ hρ).ne]
  exact ENNReal.ofReal_le_ofReal (hsq.trans_eq (by ring))

end SharpWasserstein.Sharp.Endpoint
