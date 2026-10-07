/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import SharpWasserstein.Sharp.Hierarchy.SplitGenerator

/-!
# The finite Galerkin hierarchy inequality (Lemma 5.3)

Let `ε_{m,j}` be the regularized Galerkin energy of level `m` (Appendix A, `eq:galerkin`), with
optimizer `f`. Lemma 5.3 (`lem:gal-ode`) states
`ε'_{m,j} ≤ D ε_{m,j} + q_m (E_{m+1} - ε_{m,j}) + C_m (E_m - ε_{m,j})` for `m < N` and
`ε'_{N,j} ≤ D ε_{N,j} + C_N (E_N - ε_{N,j})`, with `D = 2Λ + 2L₁ + 1`,
`q_m = λ m α_m = 2 m G (1 - m/N)` and a constant `C_m` that may depend on `‖a‖_∞`.

This file proves the static form of this inequality (the right side of the derivative identity
evaluated at the frozen optimizer) and then the inequality along the Brownian flow of the
development. It follows the corresponding files of the development
(`PhysicalFourierTrialHierarchy`, `PeriodicMarginalCoefficientEvolutionEstimate`,
`PeriodicMarginalCoefficientEvolutionHierarchy`), with the generator split of the paper
(`SplitGenerator`) and the sharp constants of Lemma 5.2 (`ExternalEnergy`, `SplitDrift`):
the internal estimate uses `‖Db^{[m]}‖ ≤ Λ`, and the external one `2L₁` and `mG`.
The energies are the periodic tangent energies of the development; the passage to the full
energies is done later, as in the development.

## Main definitions

* `splitAmplitude`: a bound for `|b^{[m]}|` (it only enters `C_m`).
* `gapConstant`: the constant `C_m = 4(Λ² + |b^{[m]}|²_∞)`.

## Main statements

* `finite_hierarchy_le_sharp`, `finite_splitHierarchy_le_sharp`,
  `finite_terminal_splitHierarchy_le_sharp`: the static inequality.
* `brownian_trialEnergy_derivative_le_sharp`, `brownian_trialEnergy_terminal_derivative_le_sharp`:
  Lemma 5.3 along the flow.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace NNReal BigOperators

namespace SharpWasserstein.Sharp.Hierarchy

open WeightedTangent NoiseAverage PropagatedSourceEquation WeightedMarginal
open PeriodicParticleTangentLimit WeightedPeriodicCoefficientEvolution
open ExternalInteractionPeriodic ExternalInteractionSymmetry PropagatedSourcePermutation
open ExternalInteraction PeriodicMarginalCoefficientEvolution BochnerIdentity
open FiniteGradientTrial WeightedPeriodicFourierPhysical RegularizedTrialConvergencePhysical
open PeriodicFourierTests

variable {d m N : ℕ} {a : Position d → Position d} {K : Position d → Position d → Position d}
  {La L₁ L₂ M : ℝ}

/-- A bound for `|b^{[m]}|`, chosen once and for all from the qualitative bounds. It enters only
the constant `C_m`, which disappears in the limit `j → ∞`. -/
def splitAmplitude (N : ℕ) (h : SplitKernel a K La L₁ L₂ M) (hm : 0 < m) : ℝ :=
  Classical.choose (splitDrift_allDerivativesBounded (m := m) h N hm).bounded

theorem splitAmplitude_nonneg (N : ℕ) (h : SplitKernel a K La L₁ L₂ M) (hm : 0 < m) :
    0 ≤ splitAmplitude N h hm :=
  (Classical.choose_spec (splitDrift_allDerivativesBounded (m := m) h N hm).bounded).1

theorem splitAmplitude_bound (N : ℕ) (h : SplitKernel a K La L₁ L₂ M) (hm : 0 < m)
    (x : Point (m*d)) : ‖splitDrift N a K x‖ ≤ splitAmplitude N h hm :=
  (Classical.choose_spec (splitDrift_allDerivativesBounded (m := m) h N hm).bounded).2 x

/-- The constant `C_m = 4(Λ² + Ā_m²)` of Lemma 5.3 (zero for `m = 0`). -/
def gapConstant (N : ℕ) (h : SplitKernel a K La L₁ L₂ M) (m : ℕ) : ℝ :=
  if hm : 0 < m then
    4 * (lipΛ La L₁ L₂ ^ 2 + splitAmplitude (d := d) (m := m) N h hm ^ 2) else 0

/-! ### The static inequality -/

section Static

variable [MeasurableSpace (Point (m*d))] [BorelSpace (Point (m*d))]
  [MeasurableSpace (Point (m*d+d))] [BorelSpace (Point (m*d+d))]
  (P : ℝ) (μ : Measure (Point (m*d+d))) [IsFiniteMeasure μ]

/-- The external term `III` at a finite Galerkin optimizer: the fluctuation is the next periodic
energy minus the current regularized energy. -/
theorem integral_external_trial_le_sharp (σ : Test (m*d+d) →ₗ[ℝ] ℝ)
    (s : Finset ((Fin (m*d) → ℤ) × Bool)) {δ : ℝ} (hδ : 0 < δ)
    (h : SplitKernel a K La L₁ L₂ M) (hm : 1 ≤ m) {ε : ℝ} (hε : 0 < ε) :
    let T := trial P (marginalLaw μ) s
    let U := (WeightedPeriodicTangentPhysical.representative P (marginalLaw μ)
      (marginalDistribution μ σ)).val.val
    let V := (WeightedPeriodicTangentPhysical.representative P μ σ).val.val
    let c := RegularizedTrialEnergy.solution T δ U
    let f := potential (fun p : s => physicalPotential P (atom p.val)) c
    2 * (∫ z, ⟪V z, gradient (interaction K f) z⟫_ℝ ∂μ) -
      (∫ z, ⟪liftedForce K z,
        gradient (fun q => ‖gradient f (prefixProjection (m*d) d q)‖ ^ 2) z⟫_ℝ ∂μ) ≤
      (2 * L₁ + ε) * RegularizedTrialEnergy.energy T δ U +
      ε * (∫ x, HierarchyAlgebra.frobeniusSq (hessian f x) ∂marginalLaw μ) +
      (gConst L₁ L₂ M * (m : ℝ) / ε) *
        (WeightedPeriodicTangentPhysical.energy P μ σ - RegularizedTrialEnergy.energy T δ U) := by
  dsimp only
  let a' := fun p : s => physicalPotential P (atom p.val)
  have ha : ∀ p, ContDiff ℝ ∞ (a' p) := fun p => physicalPotential_smooth P (smooth_atom p.val)
  have hBa : ∀ p, NoiseAverage.AllDerivativesBounded (a' p) := fun p =>
    physicalPotential_allDerivativesBounded P (smooth_atom p.val) (periodic_atom p.val)
  have hGa : ∀ p, ∃ B : ℝ, ∀ x, ‖gradient (a' p) x‖ ≤ B := fun p =>
    physicalPotential_gradient_bound P _ (smooth_atom p.val) (periodic_atom p.val)
  let T := trial P (marginalLaw μ) s
  let U := (WeightedPeriodicTangentPhysical.representative P (marginalLaw μ)
    (marginalDistribution μ σ)).val.val
  let V := (WeightedPeriodicTangentPhysical.representative P μ σ).val.val
  let c := RegularizedTrialEnergy.solution T δ U
  let f := potential a' c
  have hf := potential_smooth a' ha c
  have hBf := potential_allDerivativesBounded a' ha hBa c
  have hg : MemLp (gradient f) 2 (marginalLaw μ) := by
    obtain ⟨B, _, hBg⟩ := (gradient_allDerivativesBounded hf hBf).bounded
    exact bounded_smooth_gradient_memLp _ _ hf ⟨B, hBg⟩
  have hgp := hg.comp_measurePreserving (measurePreserving_prefix μ)
  have hH := hessian_square_integrable (marginalLaw μ) hf hBf
  have hHp := (measurePreserving_prefix μ).integrable_comp hH.aestronglyMeasurable |>.mpr hH
  have hext := integral_external_le_sharp μ h hm hf hgp hHp (Lp.memLp V) hε
  have hmapG : (∫ z, ‖gradient f (prefixProjection (m*d) d z)‖ ^ 2 ∂μ) =
      ∫ x, ‖gradient f x‖ ^ 2 ∂marginalLaw μ :=
    (integral_map (prefixProjection (m*d) d).continuous.measurable.aemeasurable
      (((smooth_gradient hf).continuous.norm.pow 2).aestronglyMeasurable)).symm
  have hmapH : (∫ z, HierarchyAlgebra.frobeniusSq (hessian f (prefixProjection (m*d) d z)) ∂μ) =
      ∫ x, HierarchyAlgebra.frobeniusSq (hessian f x) ∂marginalLaw μ :=
    (integral_map (prefixProjection (m*d) d).continuous.measurable.aemeasurable
      hH.aestronglyMeasurable).symm
  have hgap := PhysicalFourierTrialMarginal.trial_fluctuation_integral P μ σ s hδ
  have hE := RegularizedTrialEnergy.energy_eq_penalized_norm T δ hδ U
  rw [show T = gradientMap (marginalLaw μ) a' ha hGa from rfl, gradientMap_norm_sq] at hE
  have hEg : (∫ x, ‖gradient f x‖ ^ 2 ∂marginalLaw μ) ≤ RegularizedTrialEnergy.energy T δ U := by
    change RegularizedTrialEnergy.energy T δ U =
      (∫ x, ‖gradient f x‖ ^ 2 ∂marginalLaw μ) + δ * ‖c‖ ^ 2 at hE
    have := mul_nonneg hδ.le (sq_nonneg ‖c‖)
    linarith
  have hCg : 0 ≤ 2 * L₁ + ε := by have := h.L₁_nonneg; positivity
  have hCf : 0 ≤ gConst L₁ L₂ M * (m : ℝ) / ε :=
    div_nonneg (mul_nonneg (gConst_nonneg _ _ _) (Nat.cast_nonneg _)) hε.le
  have hpen : 0 ≤ δ * ‖c‖ ^ 2 := mul_nonneg hδ.le (sq_nonneg _)
  have hGle := mul_le_mul_of_nonneg_left hEg hCg
  dsimp only at hgap
  change (∫ z, ‖V z - prefixEmbedding (m*d) d (gradient f (prefixProjection (m*d) d z))‖ ^ 2
    ∂μ) = WeightedPeriodicTangentPhysical.energy P μ σ - RegularizedTrialEnergy.energy T δ U -
      δ * ‖c‖ ^ 2 at hgap
  rw [hmapG, hmapH, hgap] at hext
  have hFle := mul_le_mul_of_nonneg_left (show
    WeightedPeriodicTangentPhysical.energy P μ σ - RegularizedTrialEnergy.energy T δ U -
      δ * ‖c‖ ^ 2 ≤
    WeightedPeriodicTangentPhysical.energy P μ σ - RegularizedTrialEnergy.energy T δ U by
      linarith) hCf
  change 2 * (∫ z, ⟪V z, gradient (interaction K f) z⟫_ℝ ∂μ) - _ ≤ _
  linarith

/-- **Static form of Lemma 5.3** for `m < N`: at the frozen optimizer `f`, the internal term
`I + II` with a drift `B` (`‖DB‖ ≤ L`, `|B| ≤ A`) plus `θ` times the external term `III` is at
most `(2L + 2L₁ + 1 - q) ε + q E_{m+1} + 4(L² + A²)(E_m - ε)`, with `q = 2θ G m`. -/
theorem finite_hierarchy_le_sharp (σ : Test (m*d+d) →ₗ[ℝ] ℝ)
    (s : Finset ((Fin (m*d) → ℤ) × Bool)) {δ : ℝ} (hδ : 0 < δ)
    (h : SplitKernel a K La L₁ L₂ M) (hm : 1 ≤ m)
    {B : Point (m*d) → Point (m*d)} (hB : ContDiff ℝ ∞ B)
    (hBB : AllDerivativesBounded B) {L A : ℝ} (hL : 0 ≤ L) (hA : 0 ≤ A)
    (hBL : ∀ x, ‖fderiv ℝ B x‖ ≤ L) (hBA : ∀ x, ‖B x‖ ≤ A)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    let T := trial P (marginalLaw μ) s
    let U := (WeightedPeriodicTangentPhysical.representative P (marginalLaw μ)
      (marginalDistribution μ σ)).val.val
    let V := (WeightedPeriodicTangentPhysical.representative P μ σ).val.val
    let c := RegularizedTrialEnergy.solution T δ U
    let f := potential (fun p : s => physicalPotential P (atom p.val)) c
    let e := RegularizedTrialEnergy.energy T δ U
    let q := 2 * θ * gConst L₁ L₂ M * (m : ℝ)
    (2 * (∫ x, ⟪gradient (FiniteGeneratorCalculus.generator B f) x, U x⟫_ℝ ∂marginalLaw μ) -
      (∫ x, FiniteGeneratorCalculus.generator B (fun y => ‖gradient f y‖ ^ 2) x
        ∂marginalLaw μ)) +
      θ * (2 * (∫ z, ⟪V z, gradient (interaction K f) z⟫_ℝ ∂μ) -
        (∫ z, ⟪liftedForce K z,
          gradient (fun w => ‖gradient f (prefixProjection (m*d) d w)‖ ^ 2) z⟫_ℝ ∂μ)) ≤
      (2 * L + 2 * L₁ + 1 - q) * e + q * WeightedPeriodicTangentPhysical.energy P μ σ +
      4 * (L ^ 2 + A ^ 2) * (WeightedPeriodicTangentPhysical.energy P (marginalLaw μ)
        (marginalDistribution μ σ) - e) := by
  dsimp only
  let a' := fun p : s => physicalPotential P (atom p.val)
  have ha : ∀ p, ContDiff ℝ ∞ (a' p) := fun p => physicalPotential_smooth P (smooth_atom p.val)
  have hBa : ∀ p, AllDerivativesBounded (a' p) := fun p =>
    physicalPotential_allDerivativesBounded P (smooth_atom p.val) (periodic_atom p.val)
  have hGa : ∀ p, ∃ C : ℝ, ∀ x, ‖gradient (a' p) x‖ ≤ C := fun p =>
    physicalPotential_gradient_bound P _ (smooth_atom p.val) (periodic_atom p.val)
  let T := trial P (marginalLaw μ) s
  let U := (WeightedPeriodicTangentPhysical.representative P (marginalLaw μ)
    (marginalDistribution μ σ)).val.val
  let V := (WeightedPeriodicTangentPhysical.representative P μ σ).val.val
  let c := RegularizedTrialEnergy.solution T δ U
  let f := potential a' c
  let e := RegularizedTrialEnergy.energy T δ U
  let H := ∫ x, HierarchyAlgebra.frobeniusSq (hessian f x) ∂marginalLaw μ
  have hi := solution_generator_le (marginalLaw μ) a' ha hGa δ hδ U hBa
    (fun p => eigenvalue p.val.1 / P ^ 2) (fun p x => physicalAtom_laplacian P p.val x)
    (fun p => physicalAtom_eigenvalue_nonneg P p.val) hB hBB hL hA hBL hBA
    (show (0 : ℝ) < 1 / 2 by norm_num)
  have he := integral_external_trial_le_sharp P μ σ s hδ h hm (show (0 : ℝ) < 1 / 2 by norm_num)
  have heθ := mul_le_mul_of_nonneg_left he hθ
  have hEn : 0 ≤ e := RegularizedTrialEnergy.energy_nonneg T δ hδ U
  have hHn : 0 ≤ H := integral_nonneg (fun _ => HierarchyAlgebra.frobeniusSq_nonneg _)
  have hco : 0 ≤ 2 * L₁ + (1 : ℝ) / 2 := by have := h.L₁_nonneg; positivity
  have hc := mul_le_mul_of_nonneg_right hθ1 (mul_nonneg hco hEn)
  have hh := mul_le_mul_of_nonneg_right hθ1 hHn
  have hUn : ‖U‖ ^ 2 = WeightedPeriodicTangentPhysical.energy P (marginalLaw μ)
      (marginalDistribution μ σ) := by
    rw [WeightedPeriodicTangentPhysical.energy_eq_norm_sq]
    rfl
  dsimp only at hi heθ
  change 2 * (∫ x, ⟪gradient (FiniteGeneratorCalculus.generator B f) x, U x⟫_ℝ
      ∂marginalLaw μ) -
    (∫ x, FiniteGeneratorCalculus.generator B (fun y => ‖gradient f y‖ ^ 2) x ∂marginalLaw μ) ≤
    (2 * L + 1 / 2) * e - (2 - 1 / 2) * H + (2 * (L ^ 2 + A ^ 2) / (1 / 2)) * (‖U‖ ^ 2 - e) at hi
  rw [hUn] at hi
  change θ * (2 * (∫ z, ⟪V z, gradient (interaction K f) z⟫_ℝ ∂μ) -
    (∫ z, ⟪liftedForce K z, gradient (fun w => ‖gradient f (prefixProjection (m*d) d w)‖ ^ 2) z⟫_ℝ
      ∂μ)) ≤
    θ * ((2 * L₁ + 1 / 2) * e + (1 / 2) * H +
      (gConst L₁ L₂ M * (m : ℝ) / (1 / 2)) * (WeightedPeriodicTangentPhysical.energy P μ σ - e))
    at heθ
  change _ ≤ (2 * L + 2 * L₁ + 1 - 2 * θ * gConst L₁ L₂ M * (m : ℝ)) * e +
    (2 * θ * gConst L₁ L₂ M * (m : ℝ)) * WeightedPeriodicTangentPhysical.energy P μ σ +
    4 * (L ^ 2 + A ^ 2) * (WeightedPeriodicTangentPhysical.energy P (marginalLaw μ)
      (marginalDistribution μ σ) - e)
  nlinarith

end Static

/-! ### The static inequality for the actual marginal sources -/

section Marginal

variable [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  [MeasurableSpace (Point (m*d))] [BorelSpace (Point (m*d))]
  [MeasurableSpace (Point (m*d+d))] [BorelSpace (Point (m*d+d))]

/-- `q_m = 2 m G (N - m)/N` is the jump rate `λ m (1 - m/N)`. -/
theorem jumpRate_eq (L₁ L₂ M : ℝ) {N m : ℕ} (hN : 0 < N) :
    2 * (((N : ℝ) - m) / N) * gConst L₁ L₂ M * (m : ℝ) = jumpRate L₁ L₂ M N m := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  unfold jumpRate birthRate
  field_simp

/-- **Lemma 5.3, static form, for the marginal sources of an exchangeable law** (`m < N`): the
derivative expression `2σ(𝓛ψ) - ρ(𝓛|∇f|²)` at the Galerkin optimizer is at most
`D ε + q_m (E_{m+1} - ε) + C_m (E_m - ε)`. -/
theorem finite_splitHierarchy_le_sharp {P : ℝ} (hP : 0 < P) (hm : m < N) (hmpos : 1 ≤ m)
    (μ : Measure (Point (N*d))) [IsFiniteMeasure μ]
    (hμ : ∀ e : Equiv.Perm (Fin N), μ.map (euclideanPermutation e) = μ)
    (σ : Test (N*d) →ₗ[ℝ] ℝ) (hσE : FiniteEnergy μ σ)
    (hσ : ∀ e : Equiv.Perm (Fin N), ∀ φ : Test (N*d),
      σ (pullTest (euclideanPermutation e) φ) = σ φ)
    (h : SplitKernel a K La L₁ L₂ M)
    (ha : ∀ i x, a (x + Pi.single i P) = a x)
    (hx : ∀ i x y, K (x + Pi.single i P) y = K x y)
    (hy : ∀ i x y, K x (y + Pi.single i P) = K x y)
    (s : Finset ((Fin (m*d) → ℤ) × Bool)) {δ : ℝ} (hδ : 0 < δ) :
    let T := trial P (μ.map (marginalProjection hm.le)) s
    let U := periodicPrefixField P hm.le μ σ
    let c := RegularizedTrialEnergy.solution T δ U
    let f := potential (fun p : s => physicalPotential P (atom p.val)) c
    let e := RegularizedTrialEnergy.energy T δ U
    2 * pairing μ (WeightedTangent.representative μ σ).val (sharpSplitGenerator hm.le a K f) -
      (∫ x, sharpSplitGenerator hm.le a K (fun y => ‖gradient f y‖ ^ 2) x ∂μ) ≤
    driftRate La L₁ L₂ * e +
      jumpRate L₁ L₂ M N m * (WeightedPeriodicTangentPhysical.energy P
        (μ.map (observation hm.le ⟨m, hm⟩))
        (observedSource hm.le ⟨m, hm⟩ μ (WeightedTangent.representative μ σ).val) - e) +
      gapConstant N h m * (WeightedPeriodicTangentPhysical.energy P
        (μ.map (marginalProjection hm.le))
        (prefixSource hm.le μ (WeightedTangent.representative μ σ).val) - e) := by
  have hm0 : 0 < m := lt_of_lt_of_le Nat.zero_lt_one hmpos
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le m) hm
  let ν := μ.map (observation hm.le ⟨m, hm⟩)
  let σn := observedSource hm.le ⟨m, hm⟩ μ (WeightedTangent.representative μ σ).val
  let a' := fun p : s => physicalPotential P (atom p.val)
  let T := trial P (μ.map (marginalProjection hm.le)) s
  let U := periodicPrefixField P hm.le μ σ
  let c := RegularizedTrialEnergy.solution T δ U
  let f := potential a' c
  let L := lipΛ La L₁ L₂
  let A := splitAmplitude N h hm0
  let θ := ((N : ℝ) - m) / N
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hθ : 0 ≤ θ := div_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr hm.le)) hNr.le
  have hθ1 : θ ≤ 1 := (div_le_one hNr).mpr (by linarith [Nat.cast_nonneg (α := ℝ) m])
  have ha' (p : s) := physicalPotential_smooth P (smooth_atom p.val)
  have hpa (p : s) := physicalPotential_periodic hP.ne' (periodic_atom p.val)
  have hi := finite_hierarchy_le_sharp P ν σn s hδ h hmpos (splitDrift_smooth h N)
    (splitDrift_allDerivativesBounded h N hm0)
    (lipΛ_nonneg h.La_nonneg h.L₁_nonneg h.L₂_nonneg) (splitAmplitude_nonneg N h hm0)
    (norm_fderiv_splitDrift_le h hm.le) (splitAmplitude_bound N h hm0) hθ hθ1
  have hc := observed_solution_eq_prefix P hm.le ⟨m, hm⟩ μ σ s δ
  have he := observed_trialEnergy_eq_prefix P hm.le ⟨m, hm⟩ μ σ a' ha'
    (fun p => physicalPotential_gradient_bound P _ (smooth_atom p.val) (periodic_atom p.val)) δ
  change RegularizedTrialEnergy.energy (trial P (marginalLaw ν) s) δ
    (WeightedPeriodicTangentPhysical.representative P (marginalLaw ν)
      (marginalDistribution ν σn)).val.val = RegularizedTrialEnergy.energy T δ U at he
  have hE := periodic_marginalEnergy_observedSource P hm.le ⟨m, hm⟩ μ
    (WeightedTangent.representative μ σ).val
  dsimp only at hi
  change localEnergyTerm P (marginalLaw ν) (marginalDistribution ν σn) (splitDrift N a K)
    (potential a' (RegularizedTrialEnergy.solution (trial P (marginalLaw ν) s) δ
      (WeightedPeriodicTangentPhysical.representative P (marginalLaw ν)
        (marginalDistribution ν σn)).val.val)) +
    θ * externalEnergyTerm P ν σn K
      (potential a' (RegularizedTrialEnergy.solution (trial P (marginalLaw ν) s) δ
        (WeightedPeriodicTangentPhysical.representative P (marginalLaw ν)
          (marginalDistribution ν σn)).val.val)) ≤ _ at hi
  rw [hc, localEnergyTerm_observation, he, hE] at hi
  have hd := sharpSplitEnergyDerivative_eq hP hm hm0 μ hμ σ hσE hσ h ha hx hy
    (potential_smooth a' ha' c) (potential_periodic a' hpa c)
  dsimp only at hd ⊢
  rw [hd]
  refine hi.trans (le_of_eq ?_)
  have hq := jumpRate_eq L₁ L₂ M (m := m) hN
  simp only [gapConstant, hm0, ↓reduceDIte, driftRate, ← hq]
  ring

/-- **Lemma 5.3, static form, top level** `m = N`: no external term. -/
theorem finite_terminal_splitHierarchy_le_sharp {P : ℝ} (hP : 0 < P) (hN : 1 ≤ N)
    (μ : Measure (Point (N*d))) [IsFiniteMeasure μ] (σ : Test (N*d) →ₗ[ℝ] ℝ)
    (h : SplitKernel a K La L₁ L₂ M)
    (ha : ∀ i x, a (x + Pi.single i P) = a x)
    (hx : ∀ i x y, K (x + Pi.single i P) y = K x y)
    (hy : ∀ i x y, K x (y + Pi.single i P) = K x y)
    (s : Finset ((Fin (N*d) → ℤ) × Bool)) {δ : ℝ} (hδ : 0 < δ) :
    let T := trial P (μ.map (marginalProjection (k := N) le_rfl)) s
    let U := periodicPrefixField P le_rfl μ σ
    let c := RegularizedTrialEnergy.solution T δ U
    let f := potential (fun p : s => physicalPotential P (atom p.val)) c
    let e := RegularizedTrialEnergy.energy T δ U
    2 * pairing μ (WeightedTangent.representative μ σ).val
        (sharpSplitGenerator (m := N) le_rfl a K f) -
      (∫ x, sharpSplitGenerator (m := N) le_rfl a K (fun y => ‖gradient f y‖ ^ 2) x ∂μ) ≤
    driftRate La L₁ L₂ * e +
      gapConstant N h N * (WeightedPeriodicTangentPhysical.energy P
        (μ.map (marginalProjection (k := N) le_rfl))
        (prefixSource le_rfl μ (WeightedTangent.representative μ σ).val) - e) := by
  have hN0 : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
  let ρ := μ.map (marginalProjection (k := N) le_rfl)
  let τ := prefixSource le_rfl μ (WeightedTangent.representative μ σ).val
  let a' := fun p : s => physicalPotential P (atom p.val)
  let T := trial P ρ s
  let U := periodicPrefixField P le_rfl μ σ
  let c := RegularizedTrialEnergy.solution T δ U
  have ha' (p : s) := physicalPotential_smooth P (smooth_atom p.val)
  have hpa (p : s) := physicalPotential_periodic hP.ne' (periodic_atom p.val)
  have hi := PhysicalFourierTrialHierarchy.finite_terminal_le P ρ τ s hδ
    (splitDrift_smooth h N) (splitDrift_allDerivativesBounded h N hN0)
    (lipΛ_nonneg h.La_nonneg h.L₁_nonneg h.L₂_nonneg) (splitAmplitude_nonneg N h hN0)
    (norm_fderiv_splitDrift_le h le_rfl) (splitAmplitude_bound N h hN0)
  have he := RegularizedTrialEnergy.energy_nonneg T δ hδ U
  have hext : 0 ≤ 2 * L₁ * RegularizedTrialEnergy.energy T δ U := by
    have := h.L₁_nonneg; positivity
  have hd := terminal_sharpSplitEnergyDerivative_eq hP hN0 μ σ h ha hx hy
    (potential_smooth a' ha' c) (potential_periodic a' hpa c)
  dsimp only at hi hd ⊢
  rw [hd]
  change localEnergyTerm P ρ τ (splitDrift N a K) (potential a' c) ≤ _ at hi
  simp only [gapConstant, hN0, ↓reduceDIte, driftRate]
  dsimp only [ρ, τ, T, U, c, a', periodicPrefixField] at hext hi ⊢
  linarith

end Marginal

/-! ### Lemma 5.3 along the Brownian flow -/

section Brownian

variable [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))] {M₀ K₀ M' K' : ℝ≥0}
  (hv : Continuous (Function.uncurry
    (fun _ : ℝ => (particleDrift (kernelOf a K) : Configuration d N → _))))
  (hb : ∀ _ : ℝ, ∀ x : Configuration d N, ‖particleDrift (kernelOf a K) x‖ ≤ M₀)
  (hl : ∀ _ : ℝ, LipschitzWith K₀ (particleDrift (kernelOf a K) : Configuration d N → _))
  (hv' : Continuous (Function.uncurry
    (fun _ : ℝ => equivDrift (configurationEuclidean d N) (particleDrift (kernelOf a K)))))
  (hb' : ∀ _ : ℝ, ∀ y,
    ‖equivDrift (configurationEuclidean d N) (particleDrift (kernelOf a K)) y‖ ≤ M')
  (hl' : ∀ _ : ℝ,
    LipschitzWith K' (equivDrift (configurationEuclidean d N) (particleDrift (kernelOf a K))))
  {T : ℝ} (hT : 0 ≤ T) (hbs : BoundedSmoothKernel (kernelOf a K))
  (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ] (hμ : HasSecondMoment μ)
  {u : Point (N*d) → Point (N*d)} (hu : MemLp u 2 (μ.map (configurationEuclidean d N)))
include hv hb hl hbs hμ hu

/-- **Lemma 5.3** (`m < N`): along the Brownian flow of the particle system, the regularized
Galerkin energy of level `m` has a derivative on `[0, T]` bounded by
`D ε + q_m (E_{m+1} - ε) + C_m (E_m - ε)`, where `E_m`, `E_{m+1}` are the periodic marginal
energies of the propagated source. -/
theorem brownian_trialEnergy_derivative_le_sharp
    {m : ℕ} [MeasurableSpace (Point (m*d))] [BorelSpace (Point (m*d))]
    [MeasurableSpace (Point (m*d+d))] [BorelSpace (Point (m*d+d))]
    {P : ℝ} (hP : 0 < P) (hm : m < N) (hmpos : 1 ≤ m) (hex : Exchangeable μ)
    (hue : ∀ e : Equiv.Perm (Fin N), ∀ᵐ x ∂μ.map (configurationEuclidean d N),
      u (euclideanPermutation e x) = euclideanPermutation e (u x))
    (h : SplitKernel a K La L₁ L₂ M)
    (ha : ∀ i x, a (x + Pi.single i P) = a x)
    (hx : ∀ i x y, K (x + Pi.single i P) y = K x y)
    (hy : ∀ i x y, K x (y + Pi.single i P) = K x y)
    (s : Finset ((Fin (m*d) → ℤ) × Bool)) {δ : ℝ} (hδ : 0 < δ)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    let ν := fun r => Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) r
    let σ := fun r => Brownian.sourceAt hv' hb' hl' hT (particleDrift_smooth hbs)
      (particleDrift_allDerivativesBounded hbs) (μ.map (configurationEuclidean d N)) u hu r
    let e := fun r => RegularizedTrialEnergy.energy
      (trial P ((ν r).map (marginalProjection hm.le)) s) δ
        (periodicPrefixField P hm.le (ν r) (σ r))
    let E := WeightedPeriodicTangentPhysical.energy P ((ν t).map (marginalProjection hm.le))
      (prefixSource hm.le (ν t) (WeightedTangent.representative (ν t) (σ t)).val)
    let E_next := WeightedPeriodicTangentPhysical.energy P
      ((ν t).map (observation hm.le ⟨m, hm⟩))
      (observedSource hm.le ⟨m, hm⟩ (ν t) (WeightedTangent.representative (ν t) (σ t)).val)
    ∃ e', HasDerivWithinAt e e' (Icc 0 T) t ∧
      e' ≤ driftRate La L₁ L₂ * e t + jumpRate L₁ L₂ M N m * (E_next - e t) +
        gapConstant N h m * (E - e t) := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le m) hm
  let ν := Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) t
  let σ := Brownian.sourceAt hv' hb' hl' hT (particleDrift_smooth hbs)
    (particleDrift_allDerivativesBounded hbs) (μ.map (configurationEuclidean d N)) u hu t
  let a' := fun p : s => physicalPotential P (atom p.val)
  have ha' (p : s) := physicalPotential_smooth P (smooth_atom p.val)
  have hpa (p : s) := physicalPotential_periodic hP.ne' (periodic_atom p.val)
  have hν (e : Equiv.Perm (Fin N)) : ν.map (euclideanPermutation e) = ν :=
    brownian_lawAt_permutation hv' hb' hl' hT _ e (euclideanLaw_permutation μ hex e) t
  have hσ (e : Equiv.Perm (Fin N)) (φ : Test (N*d)) :
      σ (pullTest (euclideanPermutation e) φ) = σ φ :=
    particle_sourceAt_invariant hbs hv' hb' hl' hT _ e (euclideanLaw_permutation μ hex e)
      u hu (hue e) t φ
  have hσE : FiniteEnergy ν σ :=
    (Brownian.sourceAt_finiteEnergy_and_energy_le hv' hb' hl' hT
      (particleDrift_smooth hbs) (particleDrift_allDerivativesBounded hbs)
      (μ.map (configurationEuclidean d N)) u hu ht).1
  have hd := brownian_periodic_trialEnergy_splitGenerator hv hb hl hv' hb' hl' hT hbs μ hμ
    a' ha' hu hP hm.le hpa hδ ht
  have hi := finite_splitHierarchy_le_sharp hP hm hmpos ν hν σ hσE hσ h ha hx hy s hδ
  dsimp only at hd hi ⊢
  rw [splitGenerator_kernelOf hN, splitGenerator_kernelOf hN] at hd
  exact ⟨_, hd, hi⟩

/-- **Lemma 5.3** at the top level `m = N`. -/
theorem brownian_trialEnergy_terminal_derivative_le_sharp
    {P : ℝ} (hP : 0 < P) (hN : 1 ≤ N)
    (h : SplitKernel a K La L₁ L₂ M)
    (ha : ∀ i x, a (x + Pi.single i P) = a x)
    (hx : ∀ i x y, K (x + Pi.single i P) y = K x y)
    (hy : ∀ i x y, K x (y + Pi.single i P) = K x y)
    (s : Finset ((Fin (N*d) → ℤ) × Bool)) {δ : ℝ} (hδ : 0 < δ)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    let ν := fun r => Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) r
    let σ := fun r => Brownian.sourceAt hv' hb' hl' hT (particleDrift_smooth hbs)
      (particleDrift_allDerivativesBounded hbs) (μ.map (configurationEuclidean d N)) u hu r
    let e := fun r => RegularizedTrialEnergy.energy
      (trial P ((ν r).map (marginalProjection (k := N) le_rfl)) s) δ
      (periodicPrefixField P le_rfl (ν r) (σ r))
    let E := WeightedPeriodicTangentPhysical.energy P
      ((ν t).map (marginalProjection (k := N) le_rfl))
      (prefixSource le_rfl (ν t) (WeightedTangent.representative (ν t) (σ t)).val)
    ∃ e', HasDerivWithinAt e e' (Icc 0 T) t ∧
      e' ≤ driftRate La L₁ L₂ * e t + gapConstant N h N * (E - e t) := by
  have hN0 : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
  let ν := Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) t
  let σ := Brownian.sourceAt hv' hb' hl' hT (particleDrift_smooth hbs)
    (particleDrift_allDerivativesBounded hbs) (μ.map (configurationEuclidean d N)) u hu t
  let a' := fun p : s => physicalPotential P (atom p.val)
  have ha' (p : s) := physicalPotential_smooth P (smooth_atom p.val)
  have hpa (p : s) := physicalPotential_periodic hP.ne' (periodic_atom p.val)
  have hd := brownian_periodic_trialEnergy_splitGenerator hv hb hl hv' hb' hl' hT hbs μ hμ
    a' ha' hu hP le_rfl hpa hδ ht
  have hi := finite_terminal_splitHierarchy_le_sharp hP hN ν σ h ha hx hy s hδ
  dsimp only at hd hi ⊢
  rw [splitGenerator_kernelOf hN0, splitGenerator_kernelOf hN0] at hd
  exact ⟨_, hd, hi⟩

end Brownian

end SharpWasserstein.Sharp.Hierarchy
