/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import SharpWasserstein.Statement
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# Continuous modifications of the driving noise

The stability Lemma 7.2 (`lem:stability`) of the paper compares solutions of stochastic
differential equations path by path, with the noise frozen. The public statement only asks the
driving Brownian motions to have almost surely continuous paths and almost everywhere measurable
time sections. To apply the pathwise estimates of `SharpWasserstein.Sharp.PathwiseEstimates` and
the existence results of `SharpWasserstein.Sharp.McKeanVlasovPicard`, which need a forcing with
continuous paths for *every* `ω` and measurable time sections, we replace the noise by a
continuous modification.

* `exists_continuous_modification`: a process indexed by a separable first countable space, with
  almost everywhere measurable sections and almost surely continuous paths, has a modification
  with measurable sections and continuous paths for every `ω` that almost surely coincides with it
  at all times simultaneously. The modification is the process itself outside a measurable null
  set and `0` on it; its sections are measurable because they are pointwise limits of the sections
  at the points of a countable dense set, where the process agrees with measurable versions.
* For a standard Brownian motion `B` in `ℝᵈ` (`SharpChaos.IsStandardBrownian`), the time sections
  are almost everywhere measurable, the paths are almost surely continuous, and
  `E ‖B t‖² = d t`, since each coordinate has law `gaussianReal 0 t`.
* `IsRegularForcing w C P`: `w` has continuous paths for every `ω`, measurable sections, and
  `E ‖w t‖² ≤ C t` for `t ≥ 0`. For such a forcing, `ω ↦ ∫₀ᵀ ‖w s ω‖² ds` is integrable (by
  Tonelli's theorem, without any supremum of the Brownian motion).
* `exists_particle_forcing`, `exists_mcKeanVlasov_forcing`: regular versions of the forcings
  `t ↦ √2 W(t)` of the particle system and `t ↦ √2 B(t)` of the McKean–Vlasov equation, indexed
  by real times; `SharpChaos.IsParticleSolution.exists_versions` and
  `SharpChaos.IsMcKeanVlasovSolution.exists_versions` add a measurable version of the initial
  value.

## Main statements

* `exists_continuous_modification`
* `SharpChaos.IsStandardBrownian.integral_norm_sq`: `E ‖B t‖² = d t`.
* `IsRegularForcing.integrable_intervalIntegral_norm_sq`
* `exists_particle_forcing`, `exists_mcKeanVlasov_forcing`
* `SharpChaos.IsParticleSolution.exists_versions`,
  `SharpChaos.IsMcKeanVlasovSolution.exists_versions`
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Function
open scoped NNReal

/-! ### Standard Brownian motion in `ℝᵈ` -/

namespace SharpChaos.IsStandardBrownian

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {d : ℕ}
  {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}

/-- The coordinates of a standard Brownian motion have almost everywhere measurable sections. -/
theorem aemeasurable_apply (hB : SharpChaos.IsStandardBrownian B P) (t : ℝ≥0) (c : Fin d) :
    AEMeasurable (fun ω => B t ω c) P :=
  (hB.1 c).aemeasurable t

/-- A standard Brownian motion has almost everywhere measurable sections. -/
theorem aemeasurable (hB : SharpChaos.IsStandardBrownian B P) (t : ℝ≥0) :
    AEMeasurable (B t) P :=
  (WithLp.measurable_toLp 2 _).comp_aemeasurable
    (AEMeasurable.of_eval fun c => aemeasurable_apply hB t c)

/-- A standard Brownian motion has almost surely continuous paths. -/
theorem ae_continuous (hB : SharpChaos.IsStandardBrownian B P) :
    ∀ᵐ ω ∂P, Continuous fun t => B t ω := by
  have : ∀ᵐ ω ∂P, ∀ c, Continuous fun t => B t ω c := ae_all_iff.2 fun c => (hB.1 c).cont
  filter_upwards [this] with ω hω
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi hω)

/-- The coordinates of a standard Brownian motion are square integrable. -/
theorem memLp_two_apply (hB : SharpChaos.IsStandardBrownian B P) (t : ℝ≥0) (c : Fin d) :
    MemLp (fun ω => B t ω c) 2 P :=
  ((hB.1 c).hasLaw_eval t).memLp (memLp_id_gaussianReal 2)

/-- The second moment of a coordinate of a standard Brownian motion: `E (B t)_c² = t`. -/
theorem integral_sq_apply (hB : SharpChaos.IsStandardBrownian B P) (t : ℝ≥0) (c : Fin d) :
    ∫ ω, B t ω c ^ 2 ∂P = t := by
  have hpre := (hB.1 c).toIsPreBrownianReal
  rw [← variance_of_integral_eq_zero (hpre.aemeasurable t) (hpre.integral_eval t),
    (hpre.hasLaw_eval t).variance_eq, variance_id_gaussianReal]

/-- The squared norm of a point of `ℝᵈ` is the sum of the squares of its coordinates. -/
private theorem norm_sq_eq_sum (x : EuclideanSpace ℝ (Fin d)) : ‖x‖ ^ 2 = ∑ c, x c ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Real.norm_eq_abs, sq_abs]

/-- The squared norm of a standard Brownian motion is integrable. -/
theorem integrable_norm_sq (hB : SharpChaos.IsStandardBrownian B P) (t : ℝ≥0) :
    Integrable (fun ω => ‖B t ω‖ ^ 2) P := by
  simp_rw [norm_sq_eq_sum]
  exact integrable_finsetSum _ fun c _ => (memLp_two_apply hB t c).integrable_sq

/-- **Second moment of a standard Brownian motion in `ℝᵈ`**: `E ‖B t‖² = d t`. -/
theorem integral_norm_sq (hB : SharpChaos.IsStandardBrownian B P) (t : ℝ≥0) :
    ∫ ω, ‖B t ω‖ ^ 2 ∂P = d * t := by
  simp_rw [norm_sq_eq_sum]
  rw [integral_finsetSum _ fun c _ => (memLp_two_apply hB t c).integrable_sq]
  simp [integral_sq_apply hB]

end SharpChaos.IsStandardBrownian

namespace SharpWasserstein.Sharp

/-! ### Continuous modifications -/

section Modification

variable {ι Ω E : Type*} [TopologicalSpace ι] [TopologicalSpace.SeparableSpace ι]
  [FirstCountableTopology ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω} [TopologicalSpace E]
  [TopologicalSpace.PseudoMetrizableSpace E] [MeasurableSpace E] [BorelSpace E] [Zero E]

/-- **Continuous modification** of a process with almost surely continuous paths. Let
`X : ι → Ω → E` be a process indexed by a separable first countable space, with almost everywhere
measurable sections and almost surely continuous paths. Then there is a process `Y` with
measurable sections and continuous paths for every `ω`, which almost surely coincides with `X`
at all times simultaneously.

The process `Y` is `X` outside a measurable null set `N` and `0` on `N`. The set `N` contains the
discontinuous paths and the `ω` for which `X q ω` differs from a measurable version of `X q` for
some `q` in a countable dense set `D`. Each `Y t` is the pointwise limit of the measurable
functions `Y qₙ`, where `qₙ ∈ D` tends to `t`. -/
theorem exists_continuous_modification {X : ι → Ω → E} (hXm : ∀ t, AEMeasurable (X t) P)
    (hXc : ∀ᵐ ω ∂P, Continuous fun t => X t ω) :
    ∃ Y : ι → Ω → E, (∀ t, Measurable (Y t)) ∧ (∀ ω, Continuous fun t => Y t ω) ∧
      ∀ᵐ ω ∂P, ∀ t, Y t ω = X t ω := by
  classical
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ι
  set bad : Set Ω := {ω | ¬Continuous fun t => X t ω} ∪
    ⋃ q ∈ D, {ω | X q ω ≠ (hXm q).mk _ ω} with hbad_def
  have hbad : P bad = 0 :=
    measure_union_null (ae_iff.1 hXc)
      ((measure_biUnion_null_iff hDc).2 fun q _ => ae_iff.1 (hXm q).ae_eq_mk)
  set N := toMeasurable P bad
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hgood : ∀ ω ∉ N, (Continuous fun t => X t ω) ∧ ∀ q ∈ D, X q ω = (hXm q).mk _ ω := by
    intro ω hω
    have h : ω ∉ bad := fun h => hω (subset_toMeasurable _ _ h)
    simp only [hbad_def, mem_union, mem_iUnion, not_or, not_exists] at h
    exact ⟨not_not.1 h.1, fun q hq => not_not.1 (h.2 q hq)⟩
  refine ⟨fun t ω => if ω ∈ N then 0 else X t ω, fun t => ?_, fun ω => ?_, ?_⟩
  · obtain ⟨u, huD, hu⟩ := mem_closure_iff_seq_limit.1 (hDd t)
    refine measurable_of_tendsto_metrizable (f := fun n ω => if ω ∈ N then 0 else X (u n) ω)
      (fun n => ?_) (tendsto_pi_nhds.2 fun ω => ?_)
    · have : (fun ω => if ω ∈ N then (0 : E) else X (u n) ω) =
          fun ω => if ω ∈ N then 0 else (hXm (u n)).mk _ ω := by
        funext ω
        split_ifs with h
        · rfl
        · exact (hgood ω h).2 _ (huD n)
      rw [this]
      exact Measurable.ite hNm measurable_const (hXm _).measurable_mk
    · by_cases h : ω ∈ N
      · simp only [h, ↓reduceIte]
        exact tendsto_const_nhds
      · simp only [h, ↓reduceIte]
        exact ((hgood ω h).1.tendsto t).comp hu
  · by_cases h : ω ∈ N
    · simp only [h, ↓reduceIte]
      exact continuous_const
    · simp only [h, ↓reduceIte]
      exact (hgood ω h).1
  · have : ∀ᵐ ω ∂P, ω ∉ N :=
      measure_eq_zero_iff_ae_notMem.1 (by rw [measure_toMeasurable]; exact hbad)
    filter_upwards [this] with ω hω t
    simp only [hω, ↓reduceIte]

end Modification


/-! ### Regular forcings -/

/-- In the sup norm on `Fin N → V`, `‖v‖² ≤ ∑ᵢ ‖vᵢ‖²`. -/
theorem norm_sq_le_sum_norm_sq {V : Type*} [SeminormedAddCommGroup V] {N : ℕ} (v : Fin N → V) :
    ‖v‖ ^ 2 ≤ ∑ i, ‖v i‖ ^ 2 := by
  have h : ‖v‖ ≤ Real.sqrt (∑ i, ‖v i‖ ^ 2) :=
    (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i =>
      Real.le_sqrt_of_sq_le (Finset.single_le_sum (f := fun i => ‖v i‖ ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ i))
  calc ‖v‖ ^ 2 ≤ Real.sqrt (∑ i, ‖v i‖ ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = ∑ i, ‖v i‖ ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)

/-- In the sup norm on `Fin N → V`, `∑ᵢ ‖vᵢ‖² ≤ N ‖v‖²`. -/
theorem sum_norm_sq_le_mul_norm_sq {V : Type*} [SeminormedAddCommGroup V] {N : ℕ}
    (v : Fin N → V) : ∑ i, ‖v i‖ ^ 2 ≤ N * ‖v‖ ^ 2 := by
  calc ∑ i, ‖v i‖ ^ 2 ≤ ∑ _i : Fin N, ‖v‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm v i) 2
    _ = N * ‖v‖ ^ 2 := by simp

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {V : Type*} [NormedAddCommGroup V] [MeasurableSpace V]

/-- `IsRegularForcing w C P`: the forcing `w : ℝ → Ω → V` has continuous paths for every `ω`,
measurable time sections, and square integrable sections with `E ‖w t‖² ≤ C t` for `t ≥ 0`.

For the particle system, `w = √2 W` with `C = 2 N d`; for the McKean–Vlasov equation, `w = √2 B`
with `C = 2 d`; see `exists_particle_forcing` and `exists_mcKeanVlasov_forcing`. -/
structure IsRegularForcing (w : ℝ → Ω → V) (C : ℝ) (P : Measure Ω) : Prop where
  /-- Every path is continuous. -/
  continuous : ∀ ω, Continuous fun t => w t ω
  /-- Every time section is measurable. -/
  measurable : ∀ t, Measurable (w t)
  /-- The squared norm is integrable at nonnegative times. -/
  integrable_norm_sq : ∀ t, 0 ≤ t → Integrable (fun ω => ‖w t ω‖ ^ 2) P
  /-- The second moment grows at most linearly: `E ‖w t‖² ≤ C t`. -/
  integral_norm_sq_le : ∀ t, 0 ≤ t → ∫ ω, ‖w t ω‖ ^ 2 ∂P ≤ C * t

namespace IsRegularForcing

variable [OpensMeasurableSpace V] {w : ℝ → Ω → V} {C : ℝ}

/-- The squared norm of a regular forcing is jointly strongly measurable in `(t, ω)`. -/
theorem stronglyMeasurable_uncurry_norm_sq (hw : IsRegularForcing w C P) :
    StronglyMeasurable (uncurry fun t ω => ‖w t ω‖ ^ 2) :=
  stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
    (fun ω => (hw.continuous ω).norm.pow 2)
    (fun t => ((hw.measurable t).norm.pow_const 2).stronglyMeasurable)

/-- The time integral `ω ↦ ∫₀ᵀ ‖w s ω‖² ds` of a regular forcing is measurable. -/
theorem measurable_intervalIntegral_norm_sq (hw : IsRegularForcing w C P) (T : ℝ) :
    Measurable fun ω => ∫ s in (0 : ℝ)..T, ‖w s ω‖ ^ 2 := by
  simp only [intervalIntegral]
  exact ((hw.stronglyMeasurable_uncurry_norm_sq.integral_prod_left (μ := volume.restrict
    (Ioc 0 T))).sub (hw.stronglyMeasurable_uncurry_norm_sq.integral_prod_left
      (μ := volume.restrict (Ioc T 0)))).measurable

/-- **Integrability of the time integral of the squared forcing**, by Tonelli's theorem:
`ω ↦ ∫₀ᵀ ‖w s ω‖² ds` is integrable for `T ≥ 0`. -/
theorem integrable_intervalIntegral_norm_sq [SFinite P] (hw : IsRegularForcing w C P) {T : ℝ}
    (hT : 0 ≤ T) : Integrable (fun ω => ∫ s in (0 : ℝ)..T, ‖w s ω‖ ^ 2) P := by
  set f : ℝ → Ω → ℝ := fun s ω => ‖w s ω‖ ^ 2 with hf_def
  have hf : StronglyMeasurable (uncurry f) := hw.stronglyMeasurable_uncurry_norm_sq
  have hfn : StronglyMeasurable (uncurry fun s ω => ‖f s ω‖) := hf.norm
  have hint : Integrable (uncurry f) ((volume.restrict (Ioc 0 T)).prod P) := by
    rw [integrable_prod_iff hf.aestronglyMeasurable]
    refine ⟨(ae_restrict_iff' measurableSet_Ioc).2
      (Eventually.of_forall fun s hs => hw.integrable_norm_sq s hs.1.le), ?_⟩
    refine Integrable.of_bound (hfn.integral_prod_right (ν := P)).aestronglyMeasurable
      (|C| * T) ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun s hs => ?_))
    have h0 : 0 ≤ ∫ ω, ‖f s ω‖ ∂P := integral_nonneg fun ω => norm_nonneg _
    have heq : ∫ ω, ‖f s ω‖ ∂P = ∫ ω, ‖w s ω‖ ^ 2 ∂P :=
      integral_congr_ae (Eventually.of_forall fun ω => by simp [hf_def])
    show ‖∫ ω, ‖f s ω‖ ∂P‖ ≤ |C| * T
    rw [Real.norm_eq_abs, abs_of_nonneg h0, heq]
    calc ∫ ω, ‖w s ω‖ ^ 2 ∂P ≤ C * s := hw.integral_norm_sq_le s hs.1.le
      _ ≤ |C| * s := mul_le_mul_of_nonneg_right (le_abs_self C) hs.1.le
      _ ≤ |C| * T := mul_le_mul_of_nonneg_left hs.2 (abs_nonneg C)
  have := hint.integral_prod_right
  simp only [uncurry_apply_pair] at this
  refine this.congr (Eventually.of_forall fun ω => ?_)
  simp only [hf_def, intervalIntegral.integral_of_le hT]

end IsRegularForcing

variable [BorelSpace V]

/-- A process with almost everywhere measurable sections, almost surely continuous paths and
`E ‖Z t‖² ≤ C t` has a regular version `w` (`IsRegularForcing`) that almost surely coincides with
it at all times. -/
theorem exists_isRegularForcing {Z : ℝ → Ω → V} {C : ℝ} (hZm : ∀ t, AEMeasurable (Z t) P)
    (hZc : ∀ᵐ ω ∂P, Continuous fun t => Z t ω)
    (hZi : ∀ t, 0 ≤ t → Integrable (fun ω => ‖Z t ω‖ ^ 2) P)
    (hZb : ∀ t, 0 ≤ t → ∫ ω, ‖Z t ω‖ ^ 2 ∂P ≤ C * t) :
    ∃ w : ℝ → Ω → V, IsRegularForcing w C P ∧ ∀ᵐ ω ∂P, ∀ t, w t ω = Z t ω := by
  obtain ⟨w, hwm, hwc, hwZ⟩ := exists_continuous_modification hZm hZc
  have hae : ∀ t, (fun ω => ‖w t ω‖ ^ 2) =ᵐ[P] fun ω => ‖Z t ω‖ ^ 2 := fun t => by
    filter_upwards [hwZ] with ω hω
    rw [hω t]
  refine ⟨w, ⟨hwc, hwm, fun t ht => (hZi t ht).congr (hae t).symm, fun t ht => ?_⟩, hwZ⟩
  rw [integral_congr_ae (hae t)]
  exact hZb t ht

variable {d N : ℕ}

/-- **The forcing of the particle system.** If `W₁, …, W_N` are standard Brownian motions in
`ℝᵈ`, then there is a regular forcing `w` on real times with `E ‖w t‖² ≤ 2 N d t` (sup norm on
`(ℝᵈ)ᴺ`) which almost surely equals `t ↦ (√2 Wᵢ(t⁺))ᵢ` at all times. -/
theorem exists_particle_forcing {W : Fin N → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : ∀ i, SharpChaos.IsStandardBrownian (W i) P) :
    ∃ w : ℝ → Ω → (Fin N → EuclideanSpace ℝ (Fin d)), IsRegularForcing w (2 * N * d) P ∧
      ∀ᵐ ω ∂P, ∀ t, w t ω = fun i => Real.sqrt 2 • W i t.toNNReal ω := by
  set Z : ℝ → Ω → (Fin N → EuclideanSpace ℝ (Fin d)) :=
    fun t ω i => Real.sqrt 2 • W i t.toNNReal ω with hZ
  have hZm : ∀ t, AEMeasurable (Z t) P := fun t =>
    AEMeasurable.of_eval fun i =>
      (continuous_const_smul (Real.sqrt 2)).measurable.comp_aemeasurable ((hW i).aemeasurable _)
  have hZc : ∀ᵐ ω ∂P, Continuous fun t => Z t ω := by
    have : ∀ᵐ ω ∂P, ∀ i, Continuous fun t => W i t ω :=
      ae_all_iff.2 fun i => (hW i).ae_continuous
    filter_upwards [this] with ω hω
    exact continuous_pi fun i =>
      (continuous_const_smul _).comp ((hω i).comp continuous_real_toNNReal)
  have hbound : ∀ t ω, ‖Z t ω‖ ^ 2 ≤ 2 * ∑ i, ‖W i t.toNNReal ω‖ ^ 2 := fun t ω => by
    refine (norm_sq_le_sum_norm_sq _).trans (le_of_eq ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hZ, norm_smul, mul_pow, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2),
      Real.sq_sqrt zero_le_two]
  have hint : ∀ t : ℝ, Integrable (fun ω => 2 * ∑ i, ‖W i t.toNNReal ω‖ ^ 2) P := fun t =>
    (integrable_finsetSum _ fun i _ => (hW i).integrable_norm_sq _).const_mul 2
  have hZi : ∀ t, Integrable (fun ω => ‖Z t ω‖ ^ 2) P := fun t =>
    (hint t).mono' ((hZm t).norm.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hbound t ω)
  refine exists_isRegularForcing hZm hZc (fun t _ => hZi t) fun t ht => ?_
  calc ∫ ω, ‖Z t ω‖ ^ 2 ∂P ≤ ∫ ω, 2 * ∑ i, ‖W i t.toNNReal ω‖ ^ 2 ∂P :=
        integral_mono (hZi t) (hint t) fun ω => hbound t ω
    _ = 2 * N * d * t := by
        rw [integral_const_mul,
          integral_finsetSum _ fun i _ => (hW i).integrable_norm_sq _]
        simp only [fun i => (hW i).integral_norm_sq, Real.coe_toNNReal t ht, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **The forcing of the McKean–Vlasov equation.** If `B` is a standard Brownian motion in `ℝᵈ`,
then there is a regular forcing `w` on real times with `E ‖w t‖² ≤ 2 d t` which almost surely
equals `t ↦ √2 B(t⁺)` at all times. -/
theorem exists_mcKeanVlasov_forcing {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hB : SharpChaos.IsStandardBrownian B P) :
    ∃ w : ℝ → Ω → EuclideanSpace ℝ (Fin d), IsRegularForcing w (2 * d) P ∧
      ∀ᵐ ω ∂P, ∀ t, w t ω = Real.sqrt 2 • B t.toNNReal ω := by
  have hnorm : ∀ (t : ℝ) ω, ‖Real.sqrt 2 • B t.toNNReal ω‖ ^ 2 = 2 * ‖B t.toNNReal ω‖ ^ 2 :=
    fun t ω => by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2),
        Real.sq_sqrt zero_le_two]
  refine exists_isRegularForcing (Z := fun (t : ℝ) ω => Real.sqrt 2 • B t.toNNReal ω)
    (fun t => (continuous_const_smul (Real.sqrt 2)).measurable.comp_aemeasurable
      (hB.aemeasurable _)) ?_
    (fun t _ => by simpa only [hnorm] using (hB.integrable_norm_sq _).const_mul 2)
    fun t ht => ?_
  · filter_upwards [hB.ae_continuous] with ω hω
    exact (continuous_const_smul _).comp (hω.comp continuous_real_toNNReal)
  · simp only [hnorm, integral_const_mul, hB.integral_norm_sq, Real.coe_toNNReal t ht]
    ring_nf
    exact le_rfl

/-! ### Versions of the initial values and of the noise -/

/-- **Versions of the data of the particle system.** For a solution `X` of the particle system
driven by `W`, there are a measurable version `ξ` of `X(0)` and a regular forcing `w` with
`E ‖w t‖² ≤ 2 N d t` (`IsRegularForcing`) which almost surely equals `t ↦ (√2 Wᵢ(t⁺))ᵢ` at all
times. -/
theorem _root_.SharpChaos.IsParticleSolution.exists_versions
    {a : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {X : ℝ → Ω → Fin N → EuclideanSpace ℝ (Fin d)}
    {W : Fin N → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hX : SharpChaos.IsParticleSolution a K X W P) :
    ∃ (ξ : Ω → Fin N → EuclideanSpace ℝ (Fin d)) (w : ℝ → Ω → Fin N → EuclideanSpace ℝ (Fin d)),
      Measurable ξ ∧ ξ =ᵐ[P] X 0 ∧ IsRegularForcing w (2 * N * d) P ∧
      ∀ᵐ ω ∂P, ∀ t, w t ω = fun i => Real.sqrt 2 • W i t.toNNReal ω := by
  obtain ⟨w, hw, hwW⟩ := exists_particle_forcing hX.brownian
  have h0 := hX.aemeasurable 0 le_rfl
  exact ⟨h0.mk _, w, h0.measurable_mk, h0.ae_eq_mk.symm, hw, hwW⟩

/-- **Versions of the data of the McKean–Vlasov equation.** For a solution `Y` of the
McKean–Vlasov equation driven by `B`, there are a measurable version `ζ` of `Y(0)` and a regular
forcing `w` with `E ‖w t‖² ≤ 2 d t` (`IsRegularForcing`) which almost surely equals
`t ↦ √2 B(t⁺)` at all times. -/
theorem _root_.SharpChaos.IsMcKeanVlasovSolution.exists_versions
    {a : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {Y : ℝ → Ω → EuclideanSpace ℝ (Fin d)} {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hY : SharpChaos.IsMcKeanVlasovSolution a K Y B P) :
    ∃ (ζ : Ω → EuclideanSpace ℝ (Fin d)) (w : ℝ → Ω → EuclideanSpace ℝ (Fin d)),
      Measurable ζ ∧ ζ =ᵐ[P] Y 0 ∧ IsRegularForcing w (2 * d) P ∧
      ∀ᵐ ω ∂P, ∀ t, w t ω = Real.sqrt 2 • B t.toNNReal ω := by
  obtain ⟨w, hw, hwB⟩ := exists_mcKeanVlasov_forcing hY.brownian
  have h0 := hY.aemeasurable 0 le_rfl
  exact ⟨h0.mk _, w, h0.measurable_mk, h0.ae_eq_mk.symm, hw, hwB⟩

end SharpWasserstein.Sharp
