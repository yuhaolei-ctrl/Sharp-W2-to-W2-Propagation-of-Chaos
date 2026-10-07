/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import SharpWasserstein.PrescribedSwitchEndpoint
public import SharpWasserstein.ReferenceTensorIdentification
public import SharpWasserstein.Sharp.Endpoint.Hypotheses
public import SharpWasserstein.Sharp.Endpoint.SwitchLength
public import SharpWasserstein.Sharp.Endpoint.Triangle

/-!
# The smooth case of Theorem 2.1, with the constant `C_T`

This file proves the smooth case of Theorem 2.1 (`thm:main`), following the first paragraph of
Section 3.4 (`sec:proof-main`) of the paper, with the exact constant
`C_T = (e^{LT} √C₀ + e^{ωT/2} (A₀ T + 2 A₁ √T))²` of `eq:CT` (`SharpWasserstein.Sharp.sharpC`),
over the two quantitative estimates stated in `SharpWasserstein.Sharp.Endpoint.Hypotheses`:
* `SharpSourceEnergyBound`: Propositions 3.6 and 3.7 combined,
  `E^{[s]}_k(t - s) ≤ (A₀ + A₁/√s)² e^{ω(t-s)} k²/N²`;
* `SharpReferenceBound`: Lemma 3.5, `W²(R^{(k)}_t, μ_t^{⊗k}) ≤ e^{2Lt} C₀ k²/N²`.

The proof is the one of the paper. Fix `0 < t ≤ T` and `1 ≤ k ≤ N`.
1. The interpolating curve `ν^{N,t}_s = S^{N,*}_{t-s} R^N_s` (`PrescribedSwitchCurve.law`)
   starts at `ν^{N,t}_0 = P_{N,t}` (`WassersteinEndpoint.switch_zero_eq_supplied`, by weak
   uniqueness for smooth coefficients) and ends at `ν^{N,t}_t = R^N_t`
   (`PrescribedSwitchCurve.law_terminal`).
2. By the energy bound with `e^{ω(t-s)} ≤ e^{ωt}`, the length lemma gives
   `W(P^{(k)}_{N,t}, R^{(k)}_t) ≤ e^{ωt/2} (A₀ t + 2 A₁ √t) k/N`
   (`prescribed_switch_length_exp`).
3. Lemma 3.5 gives `W(R^{(k)}_t, μ_t^{⊗k}) ≤ e^{Lt} √C₀ k/N`, and the triangle inequality
   (`wassersteinSq_le_of_sqrt_le`) together with `add_le_sqrt_sharpC` gives
   `W²(P^{(k)}_{N,t}, μ_t^{⊗k}) ≤ C_T k²/N²`.
For `t = 0` the bound is the initial hierarchy (`eq:initial`), since `C₀ ≤ C_T` (`le_sharpC`).

The coefficients are smooth (`IsSmoothCoefficients a K La L₁ L₂ M`) and the dynamics of the
development are driven by the kernel `kernelOf a K`; the qualitative sup-norm bounds of that
kernel, needed to build the interpolating curve, are provided by
`IsSmoothCoefficients.exists_kernelBounds` and do not enter the estimate.

## Main statements

* `smooth_case`: the smooth case of Theorem 2.1 over the hypotheses `SharpSourceEnergyBound`
  and `SharpReferenceBound`.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory

namespace SharpWasserstein.Sharp.Endpoint

/-- **Theorem 2.1, smooth case, with the constant `C_T` of `eq:CT`.** Let `a`, `K` be smooth
coefficients satisfying Assumption A with the Euclidean constants `L_a, L₁, L₂, M`, let `N ≥ 1`,
let `μ` be the limit evolution and `P` the particle evolution driven by `kernelOf a K`, and let
the initial hierarchy `W²(P^{(k)}_0, μ_0^{⊗k}) ≤ C₀ k²/N²` hold for `1 ≤ k ≤ N`. Assume the
source and profile estimate `SharpSourceEnergyBound` (Propositions 3.6 and 3.7) and the
reference estimate `SharpReferenceBound` (Lemma 3.5) on the horizon `T > 0`. Then
`W²(P^{(k)}_t, μ_t^{⊗k}) ≤ C_T k²/N²` for all `0 ≤ t ≤ T` and `1 ≤ k ≤ N`. -/
theorem smooth_case {d N : ℕ} {a : Position d → Position d}
    {K : Position d → Position d → Position d} {La L₁ L₂ M : ℝ}
    (hS : IsSmoothCoefficients a K La L₁ L₂ M) (hN : 1 ≤ N)
    {μ : ℝ → Measure (Position d)} (hμ : IsLimitEvolution (kernelOf a K) μ)
    {P : ℝ → Measure (Configuration d N)} (hP : IsParticleEvolution (kernelOf a K) P)
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hinit : ∀ k (hk : k ≤ N), 1 ≤ k →
      wassersteinSq (marginal hk (P 0)) (tensorLaw (μ 0) k) ≤
        ENNReal.ofReal (C₀ * (k : ℝ) ^ 2 / (N : ℝ) ^ 2))
    {T : ℝ} (hT : 0 < T)
    (henergy : SharpSourceEnergyBound a K La L₁ L₂ M C₀ T μ (P 0))
    (href : SharpReferenceBound a K La L₁ C₀ T μ (P 0)) :
    ∀ t ∈ Icc 0 T, ∀ k (hk : k ≤ N), 1 ≤ k →
      wassersteinSq (marginal hk (P t)) (tensorLaw (μ t) k) ≤
        ENNReal.ofReal (sharpC C₀ T La L₁ L₂ M * (k : ℝ) ^ 2 / (N : ℝ) ^ 2) := by
  intro t ht k hk hkpos
  have hLa := hS.assumptionA.La_nonneg
  have hL₁ := hS.assumptionA.L₁_nonneg
  have hL₂ := hS.assumptionA.L₂_nonneg
  have hM := hS.assumptionA.M_nonneg
  rcases eq_or_lt_of_le ht.1 with h0 | htpos
  · -- At `t = 0` the bound is the initial hierarchy, since `C₀ ≤ C_T`.
    subst h0
    refine (hinit k hk hkpos).trans (ENNReal.ofReal_le_ofReal ?_)
    have := le_sharpC (C₀ := C₀) (L₂ := L₂) hT.le hLa hL₁ hL₂ hM
    gcongr
  have hNpos : 0 < N := hN
  have hb := hS.boundedSmoothKernel
  obtain ⟨Mb, Lb₁, Lb₂, hMb, hLb₁, hLb₂, hbound⟩ := hS.exists_kernelBounds
  have := hP.1.probability 0 le_rfl
  have := hP.1.probability t ht.1
  have := hμ.1 t ht.1
  have hP₀ : HasSecondMoment (P 0) := hP.1.secondMoment 0 le_rfl
  have hA₀ := sourceA₀_nonneg (C₀ := C₀) (T := T) (La := La) hL₁ hL₂ hM
  have hA₁ := sourceA₁_nonneg (C₀ := C₀) (T := T) (La := La) (L₁ := L₁) hM
  have hr : 0 ≤ (k : ℝ) / N := by positivity
  -- Step 1: the length of the interpolating curve from `P_t = ν_0` to `R_t = ν_t`.
  have hswitch := prescribed_switch_length_exp hNpos hb hbound hMb hLb₁ hLb₂ hμ ht.1 (P 0) hP₀ hk
    (omega_nonneg hLa hL₁ hL₂ M) hA₀ hA₁ fun s hs hst =>
      henergy hNpos hb Mb Lb₁ Lb₂ hbound hMb hLb₁ hLb₂ hμ inferInstance hP₀ t htpos ht.2 s hs hst
        k hk hkpos
  rw [WassersteinEndpoint.switch_zero_eq_supplied hNpos hb hbound hMb hLb₁ hLb₂ hμ hP ht.1,
    PrescribedSwitchCurve.law_terminal] at hswitch
  -- Step 2: Lemma 3.5 at time `t`.
  have hR := PrescribedReference.law_weakEvolution hb hbound hMb hLb₁ hμ N (P 0) hP₀
  have : IsProbabilityMeasure (PrescribedReference.law hb hbound hMb hLb₁ hμ N (P 0) t) :=
    hR.probability t ht.1
  have hD : 0 ≤ Real.exp (lipL La L₁ * t) * Real.sqrt C₀ := by positivity
  have hRt := sqrt_wassersteinSq_le_of_le_sq (mul_nonneg hD hr)
    ((href hb Mb Lb₁ Lb₂ hbound hMb hLb₁ hμ t htpos ht.2 k hk hkpos).trans_eq (by
      congr 1
      rw [mul_pow, mul_pow, Real.sq_sqrt hC₀, div_pow]
      ring))
  -- Step 3: the triangle inequality and the final constant.
  have htri := wassersteinSq_le_of_sqrt_le (marginal hk (P t))
    (marginal hk (PrescribedReference.law hb hbound hMb hLb₁ hμ N (P 0) t)) (tensorLaw (μ t) k)
    (hasSecondMoment_marginal hk (hP.1.secondMoment t ht.1))
    (hasSecondMoment_marginal hk (hR.secondMoment t ht.1))
    ((PrescribedReference.supplied_tensor_weakEvolution hb hbound hMb hLb₁ hμ k).secondMoment t
      ht.1) hswitch hRt
  refine htri.trans (ENNReal.ofReal_le_ofReal ?_)
  have hsum := add_le_sqrt_sharpC (C₀ := C₀) ht.1 ht.2 hLa hL₁ hL₂ hM
  have hS₀ : 0 ≤ Real.exp (omega La L₁ L₂ M * t / 2) *
      (sourceA₀ C₀ T La L₁ L₂ M * t + 2 * sourceA₁ C₀ T La L₁ M * Real.sqrt t) := by
    have := ht.1
    positivity
  have hsq : (Real.exp (omega La L₁ L₂ M * t / 2) *
      (sourceA₀ C₀ T La L₁ L₂ M * t + 2 * sourceA₁ C₀ T La L₁ M * Real.sqrt t) +
        Real.exp (lipL La L₁ * t) * Real.sqrt C₀) ^ 2 ≤ sharpC C₀ T La L₁ L₂ M := by
    calc _ ≤ Real.sqrt (sharpC C₀ T La L₁ L₂ M) ^ 2 :=
          pow_le_pow_left₀ (add_nonneg hS₀ hD) (by linarith) 2
      _ = _ := Real.sq_sqrt (sharpC_nonneg _ _ _ _ _ _)
  rw [div_pow, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hsq (sq_nonneg _))
    (sq_nonneg _)

end SharpWasserstein.Sharp.Endpoint
