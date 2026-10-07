/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import SharpWasserstein.Sharp.Hierarchy.ExternalEnergy
public import SharpWasserstein.PeriodicMarginalCoefficientEvolutionHierarchy

/-!
# The generator split of the marginal equations with the drift in the level generator

In the proof of Lemma 5.1 (`lem:propagated`) the particle generator `𝓛_N = Δ + b_N · ∇` is
applied to a function `ψ` of the first `m` particles and split as
`𝓛_N ψ = 𝓛_m ψ + N⁻¹ ∑_{j > m} Φψ(x_{1:m}, x_j)`, with
`𝓛_m = Δ + b^{[m]} · ∇` and `Φψ(x, y) = ∑ᵢ K(xᵢ, y) · ∇ᵢψ(x)` (`eq:Bm-Phi`). The whole
one-body drift `a` belongs to `𝓛_m`; only `K` enters `Φ`.

The development drives the particles by the single kernel `b(x, y) = a(x) + K(x, y)`
(`kernelOf a K`) and splits the generator as `PeriodicMarginalCoefficientEvolution.splitGenerator`,
with `b` in both parts. This file proves that, for `b = kernelOf a K`, this split equals the split
of the paper (`splitGenerator_kernelOf`), and then redoes the exact decomposition of the energy
derivative of the development (`splitEnergyDerivative_eq`) for the paper's split: the derivative
is the internal term `I + II` of the proof of Lemma 5.3 (`lem:gal-ode`) with the drift
`b^{[m]}` plus `α_m` times the external term `III` with the interaction `K`
(`sharpSplitEnergyDerivative_eq`). The exchangeable averaging over the external particles is
that of the development.

## Main definitions

* `splitInternalGenerator N a K`: the level generator `𝓛_m`.
* `sharpSplitGenerator hm a K`: the split `𝓛_m ψ + N⁻¹ ∑_{j > m} Φψ(·, x_j)` on cylinders.

## Main statements

* `splitGenerator_kernelOf`.
* `sharpSplitEnergyDerivative_eq`, `terminal_sharpSplitEnergyDerivative_eq`.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace BigOperators

namespace SharpWasserstein.Sharp.Hierarchy

open WeightedTangent NoiseAverage PropagatedSourceEquation PeriodicSourceConvolution
open PeriodicParticleTangentLimit WeightedPeriodicCoefficientEvolution WeightedMarginal
open ExternalInteractionPeriodic ExternalInteractionSymmetry PropagatedSourcePermutation
open ExternalInteraction PeriodicMarginalCoefficientEvolution
open WeightedPeriodicFourierScale (PeriodicOf)

variable {d m N : ℕ}

/-- The level generator `𝓛_m f = Δf + b^{[m]} · ∇f` (`eq:Bm-Phi`). -/
def splitInternalGenerator (N : ℕ) (a : Position d → Position d)
    (K : Position d → Position d → Position d) (f : Point (m*d) → ℝ) (x : Point (m*d)) : ℝ :=
  PDEPairings.laplacian f x + ⟪splitDrift N a K x, gradient f x⟫_ℝ

/-- The split `𝓛_N ψ = 𝓛_m ψ + N⁻¹ ∑_{j > m} Φψ(x_{1:m}, x_j)` of the particle generator on a
cylinder function `ψ` of the first `m` particles (proof of Lemma 5.1). -/
def sharpSplitGenerator (hm : m ≤ N) (a : Position d → Position d)
    (K : Position d → Position d → Position d) (f : Point (m*d) → ℝ) (x : Point (N*d)) : ℝ :=
  cylinder hm (splitInternalGenerator N a K f) x +
    (N : ℝ)⁻¹ * ∑ j : Fin N with m ≤ j.val, particleInteraction hm j K f x

/-- The level generator is the finite generator of the development with drift `b^{[m]}`. -/
theorem splitInternalGenerator_eq_generator (N : ℕ) (a : Position d → Position d)
    (K : Position d → Position d → Position d) (f : Point (m*d) → ℝ) :
    splitInternalGenerator N a K f = FiniteGeneratorCalculus.generator (splitDrift N a K) f :=
  rfl

/-- The external force of the combined kernel is the one-body drift of the visible particles plus
the external force of `K`. -/
theorem force_kernelOf (a : Position d → Position d) (K : Position d → Position d → Position d)
    (z : Point (m*d+d)) :
    force (kernelOf a K) z = oneBody a (prefixProjection (m*d) d z) + force K z := by
  simp only [force, oneBody, kernelOf]
  rw [← map_add]
  rfl

/-- The external interaction of the combined kernel splits into the drift part and `Φ`. -/
theorem interaction_kernelOf (a : Position d → Position d)
    (K : Position d → Position d → Position d) (f : Point (m*d) → ℝ) (z : Point (m*d+d)) :
    interaction (kernelOf a K) f z =
      ⟪oneBody a (prefixProjection (m*d) d z), gradient f (prefixProjection (m*d) d z)⟫_ℝ +
        interaction K f z := by
  rw [interaction, force_kernelOf, inner_add_left]
  rfl

/-- The number of external labels `j > m` is `N - m`. -/
theorem card_external (hm : m ≤ N) :
    ((Finset.univ.filter (fun j : Fin N => m ≤ j.val)).card : ℝ) = (N : ℝ) - m := by
  rcases hm.lt_or_eq with hlt | heq
  · rw [external_card hlt, Nat.cast_sub hm]
  · subst heq
    have hempty : Finset.univ.filter (fun j : Fin m => m ≤ j.val) = ∅ := by
      ext j
      simp [Nat.not_le.mpr j.isLt]
    rw [hempty, Finset.card_empty, Nat.cast_zero, sub_self]

/-- **The generator split of the paper.** For the combined kernel `b = a(x) + K(x, y)`, the split
of the development equals `𝓛_m ψ + N⁻¹ ∑_{j > m} Φψ(·, x_j)`, with all of `a` in `𝓛_m`. -/
theorem splitGenerator_kernelOf (hN : 0 < N) (hm : m ≤ N) (a : Position d → Position d)
    (K : Position d → Position d → Position d) (f : Point (m*d) → ℝ) :
    splitGenerator hm (kernelOf a K) f = sharpSplitGenerator hm a K f := by
  funext x
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  set px := marginalProjection hm x
  have hext (j : Fin N) : particleInteraction hm j (kernelOf a K) f x =
      ⟪oneBody a px, gradient f px⟫_ℝ + particleInteraction hm j K f x := by
    simp only [particleInteraction, Function.comp_apply]
    rw [interaction_kernelOf, prefix_observation]
  simp only [splitGenerator, sharpSplitGenerator, PeriodicMarginalCoefficientEvolution.cylinder,
    Function.comp_apply, splitInternalGenerator]
  rw [Finset.sum_congr rfl (fun j _ => hext j), Finset.sum_add_distrib, Finset.sum_const,
    nsmul_eq_mul, card_external hm, ← internalDrift_kernelOf_add hN a K px, inner_add_left,
    inner_smul_left]
  simp only [RCLike.conj_to_real]
  field_simp
  ring

/-! ### Smoothness and periodicity of the level generator -/

variable {a : Position d → Position d} {K : Position d → Position d → Position d}
  {La L₁ L₂ M : ℝ}

theorem splitInternalGenerator_smooth (h : SplitKernel a K La L₁ L₂ M) (N : ℕ)
    {f : Point (m*d) → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (splitInternalGenerator N a K f) :=
  (BochnerIdentity.smooth_laplacian hf).add
    ((splitDrift_smooth h N).inner ℝ (BochnerIdentity.smooth_gradient hf))

theorem splitInternalGenerator_periodic {P : ℝ} (hm : 0 < m)
    (ha : ∀ i x, a (x + Pi.single i P) = a x)
    (hx : ∀ i x y, K (x + Pi.single i P) y = K x y)
    (hy : ∀ i x y, K x (y + Pi.single i P) = K x y)
    (N : ℕ) {f : Point (m*d) → ℝ}
    (hp : PeriodicOf P (f ∘ (PeriodicBochner.coordinateEquiv (m*d)).symm)) :
    PeriodicOf P (splitInternalGenerator N a K f ∘ (PeriodicBochner.coordinateEquiv (m*d)).symm) :=
  fun i => (euclidean_laplacian_periodic hp i).add
    (of_euclidean_lattice_periodic (F := fun x => ⟪splitDrift N a K x, gradient f x⟫_ℝ)
      (fun k x => by rw [splitDrift_lattice hm ha hx hy, gradient_lattice_periodic hp]) i)

/-- Periodicity of the combined kernel. -/
theorem kernelOf_periodic_first {P : ℝ} (ha : ∀ i x, a (x + Pi.single i P) = a x)
    (hx : ∀ i x y, K (x + Pi.single i P) y = K x y) (i : Fin d) (x y : Position d) :
    kernelOf a K (x + Pi.single i P) y = kernelOf a K x y := by
  simp only [kernelOf, ha, hx]

theorem kernelOf_periodic_second {P : ℝ} (hy : ∀ i x y, K x (y + Pi.single i P) = K x y)
    (i : Fin d) (x y : Position d) :
    kernelOf a K x (y + Pi.single i P) = kernelOf a K x y := by
  simp only [kernelOf, hy]

/-! ### Exact decomposition of the energy derivative -/

variable [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  [MeasurableSpace (Point (m*d))] [BorelSpace (Point (m*d))]
  [MeasurableSpace (Point (m*d+d))] [BorelSpace (Point (m*d+d))]

/-- The source marginal equation (`eq:sigma-eq`) on periodic tests, for the split of the paper:
the internal part is represented at level `m` and the averaged external part at level `m + 1`. -/
theorem sharpSplitGenerator_periodic_pairing {P : ℝ} (hP : 0 < P) (hm : m < N) (hmpos : 0 < m)
    (μ : Measure (Point (N*d))) [IsFiniteMeasure μ]
    (hμ : ∀ e : Equiv.Perm (Fin N), μ.map (euclideanPermutation e) = μ)
    (U : Lp (Point (N*d)) 2 μ)
    (hU : ∀ e : Equiv.Perm (Fin N), ∀ᵐ x ∂μ,
      U (euclideanPermutation e x) = euclideanPermutation e (U x))
    (h : SplitKernel a K La L₁ L₂ M)
    (ha : ∀ i x, a (x + Pi.single i P) = a x)
    (hx : ∀ i x y, K (x + Pi.single i P) y = K x y)
    (hy : ∀ i x y, K x (y + Pi.single i P) = K x y)
    {f : Point (m*d) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : PeriodicOf P (f ∘ (PeriodicBochner.coordinateEquiv (m*d)).symm)) :
    pairing μ U (sharpSplitGenerator hm.le a K f) =
      (∫ y, ⟪gradient (splitInternalGenerator N a K f) y,
        ((WeightedPeriodicTangentPhysical.representative P (μ.map (marginalProjection hm.le))
          (prefixSource hm.le μ U) : gradientClosure (μ.map (marginalProjection hm.le))) :
          Lp (Point (m*d)) 2 (μ.map (marginalProjection hm.le))) y⟫_ℝ
          ∂μ.map (marginalProjection hm.le)) +
      (((N : ℝ) - m) / N) * (∫ y, ⟪gradient (interaction K f) y,
        ((WeightedPeriodicTangentPhysical.representative P (μ.map (observation hm.le ⟨m, hm⟩))
          (observedSource hm.le ⟨m, hm⟩ μ U) :
            gradientClosure (μ.map (observation hm.le ⟨m, hm⟩))) :
          Lp (Point (m*d+d)) 2 (μ.map (observation hm.le ⟨m, hm⟩))) y⟫_ℝ
          ∂μ.map (observation hm.le ⟨m, hm⟩)) := by
  have hi := splitInternalGenerator_smooth h N hf
  have hpi := splitInternalGenerator_periodic hmpos ha hx hy N hp
  have hbi := physical_allDerivativesBounded hP hi hpi
  have he := interaction_smooth h.smooth_K hf
  have hpe := interaction_periodic hx hy hp
  have hbe := physical_allDerivativesBounded hP he hpe
  have hsplit : pairing μ U (sharpSplitGenerator hm.le a K f) =
      pairing μ U (cylinder hm.le (splitInternalGenerator N a K f)) +
        (N : ℝ)⁻¹ * ∑ j : Fin N with m ≤ j.val, pairing μ U (particleInteraction hm.le j K f) :=
    pairing_add_sum μ U (Finset.univ.filter (fun j : Fin N => m ≤ j.val))
      (cylinder_smooth hm.le hi) (cylinder_allDerivativesBounded hm.le hi hbi)
      (fun j => particleInteraction hm.le j K f)
      (fun j => he.comp (observation hm.le j).contDiff)
      (fun j => hbe.comp_linear he (observation hm.le j)) _
  rw [hsplit, prefixSource_periodic_pairing hm.le μ U hP hi hpi,
    external_interaction_meanField_periodic hP hm μ hμ U hU h.smooth_K hx hy hf hp]

/-- The same pairing for the canonical representative of an exchangeable source. -/
theorem canonical_sharpSplitGenerator_periodic_pairing {P : ℝ} (hP : 0 < P) (hm : m < N)
    (hmpos : 0 < m) (μ : Measure (Point (N*d))) [IsFiniteMeasure μ]
    (hμ : ∀ e : Equiv.Perm (Fin N), μ.map (euclideanPermutation e) = μ)
    (σ : Test (N*d) →ₗ[ℝ] ℝ) (hσE : FiniteEnergy μ σ)
    (hσ : ∀ e : Equiv.Perm (Fin N), ∀ φ : Test (N*d),
      σ (pullTest (euclideanPermutation e) φ) = σ φ)
    (h : SplitKernel a K La L₁ L₂ M)
    (ha : ∀ i x, a (x + Pi.single i P) = a x)
    (hx : ∀ i x y, K (x + Pi.single i P) y = K x y)
    (hy : ∀ i x y, K x (y + Pi.single i P) = K x y)
    {f : Point (m*d) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : PeriodicOf P (f ∘ (PeriodicBochner.coordinateEquiv (m*d)).symm)) :
    let U := (WeightedTangent.representative μ σ).val
    pairing μ U (sharpSplitGenerator hm.le a K f) =
      (∫ y, ⟪gradient (splitInternalGenerator N a K f) y,
        ((WeightedPeriodicTangentPhysical.representative P (μ.map (marginalProjection hm.le))
          (prefixSource hm.le μ U) : gradientClosure (μ.map (marginalProjection hm.le))) :
          Lp (Point (m*d)) 2 (μ.map (marginalProjection hm.le))) y⟫_ℝ
          ∂μ.map (marginalProjection hm.le)) +
      (((N : ℝ) - m) / N) * (∫ y, ⟪gradient (interaction K f) y,
        ((WeightedPeriodicTangentPhysical.representative P (μ.map (observation hm.le ⟨m, hm⟩))
          (observedSource hm.le ⟨m, hm⟩ μ U) :
            gradientClosure (μ.map (observation hm.le ⟨m, hm⟩))) :
          Lp (Point (m*d+d)) 2 (μ.map (observation hm.le ⟨m, hm⟩))) y⟫_ℝ
          ∂μ.map (observation hm.le ⟨m, hm⟩)) := by
  apply sharpSplitGenerator_periodic_pairing hP hm hmpos μ hμ _ _ h ha hx hy hf hp
  intro e
  exact WeightedSourceSymmetry.representative_equivariant μ (euclideanPermutationIsometry e)
    (hμ e) σ hσE (hσ e)

/-- The law marginal equation (`eq:rho-eq`) on periodic tests, for the split of the paper. -/
theorem sharpSplitGenerator_integral {P : ℝ} (hP : 0 < P) (hm : m < N) (hmpos : 0 < m)
    (μ : Measure (Point (N*d))) [IsFiniteMeasure μ]
    (hμ : ∀ e : Equiv.Perm (Fin N), μ.map (euclideanPermutation e) = μ)
    (h : SplitKernel a K La L₁ L₂ M)
    (ha : ∀ i x, a (x + Pi.single i P) = a x)
    (hx : ∀ i x y, K (x + Pi.single i P) y = K x y)
    (hy : ∀ i x y, K x (y + Pi.single i P) = K x y)
    {f : Point (m*d) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : PeriodicOf P (f ∘ (PeriodicBochner.coordinateEquiv (m*d)).symm)) :
    (∫ x, sharpSplitGenerator hm.le a K f x ∂μ) =
      (∫ y, splitInternalGenerator N a K f y ∂μ.map (marginalProjection hm.le)) +
      (((N : ℝ) - m) / N) * (∫ y, interaction K f y ∂μ.map (observation hm.le ⟨m, hm⟩)) := by
  have hi := splitInternalGenerator_smooth h N hf
  obtain ⟨A, _, hA⟩ := (physical_allDerivativesBounded hP hi
    (splitInternalGenerator_periodic hmpos ha hx hy N hp)).bounded
  have hI : Integrable (cylinder hm.le (splitInternalGenerator N a K f)) μ :=
    Integrable.of_bound (cylinder_smooth hm.le hi).continuous.aestronglyMeasurable A
      (Eventually.of_forall fun x => hA (marginalProjection hm.le x))
  have he := interaction_smooth h.smooth_K hf
  obtain ⟨B, _, hB⟩ :=
    (physical_allDerivativesBounded hP he (interaction_periodic hx hy hp)).bounded
  have hE (j : Fin N) : Integrable (particleInteraction hm.le j K f) μ :=
    Integrable.of_bound (he.continuous.comp (observation hm.le j).continuous).aestronglyMeasurable
      B (Eventually.of_forall fun x => hB (observation hm.le j x))
  change (∫ x, cylinder hm.le (splitInternalGenerator N a K f) x +
    (N : ℝ)⁻¹ * ∑ j : Fin N with m ≤ j.val, particleInteraction hm.le j K f x ∂μ) = _
  rw [integral_add hI ((integrable_finsetSum _ (fun j _ => hE j)).const_mul _),
    integral_const_mul, integral_finsetSum _ (fun j _ => hE j)]
  rw [show (∫ x, cylinder hm.le (splitInternalGenerator N a K f) x ∂μ) =
      ∫ y, splitInternalGenerator N a K f y ∂μ.map (marginalProjection hm.le) from
    (integral_map (marginalProjection hm.le).continuous.measurable.aemeasurable
      hi.continuous.aestronglyMeasurable).symm]
  congr 1
  exact external_integral_meanField hm μ hμ he.continuous

/-- **Exact decomposition of the energy derivative** (proof of Lemma 5.3): for an exchangeable
law and source, `2σ(𝓛ψ) - ρ(𝓛|∇f|²)` on the cylinder of `f` equals the level-`m` term `I + II`
with drift `b^{[m]}` plus `α_m` times the external term `III` with interaction `K`. -/
theorem sharpSplitEnergyDerivative_eq {P : ℝ} (hP : 0 < P) (hm : m < N) (hmpos : 0 < m)
    (μ : Measure (Point (N*d))) [IsFiniteMeasure μ]
    (hμ : ∀ e : Equiv.Perm (Fin N), μ.map (euclideanPermutation e) = μ)
    (σ : Test (N*d) →ₗ[ℝ] ℝ) (hσE : FiniteEnergy μ σ)
    (hσ : ∀ e : Equiv.Perm (Fin N), ∀ φ : Test (N*d),
      σ (pullTest (euclideanPermutation e) φ) = σ φ)
    (h : SplitKernel a K La L₁ L₂ M)
    (ha : ∀ i x, a (x + Pi.single i P) = a x)
    (hx : ∀ i x y, K (x + Pi.single i P) y = K x y)
    (hy : ∀ i x y, K x (y + Pi.single i P) = K x y)
    {f : Point (m*d) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : PeriodicOf P (f ∘ (PeriodicBochner.coordinateEquiv (m*d)).symm)) :
    2 * pairing μ (WeightedTangent.representative μ σ).val (sharpSplitGenerator hm.le a K f) -
      (∫ x, sharpSplitGenerator hm.le a K (fun y => ‖gradient f y‖ ^ 2) x ∂μ) =
    localEnergyTerm P (μ.map (marginalProjection hm.le))
      (prefixSource hm.le μ (WeightedTangent.representative μ σ).val) (splitDrift N a K) f +
      (((N : ℝ) - m) / N) * externalEnergyTerm P (μ.map (observation hm.le ⟨m, hm⟩))
        (observedSource hm.le ⟨m, hm⟩ μ (WeightedTangent.representative μ σ).val) K f := by
  have hf2 := BochnerIdentity.smooth_gradient_norm_sq hf
  have hp2 : PeriodicOf P ((fun y => ‖gradient f y‖ ^ 2) ∘
      (PeriodicBochner.coordinateEquiv (m*d)).symm) := by
    have he : (fun y => ‖gradient f y‖ ^ 2) = gramTest f f := by
      funext y
      exact (real_inner_self_eq_norm_sq _).symm
    rw [he]
    exact gramTest_periodic hp hp
  rw [canonical_sharpSplitGenerator_periodic_pairing hP hm hmpos μ hμ σ hσE hσ h ha hx hy hf hp,
    sharpSplitGenerator_integral hP hm hmpos μ hμ h ha hx hy hf2 hp2]
  have hext : interaction K (fun y => ‖gradient f y‖ ^ 2) =
      fun z => ⟪liftedForce K z,
        gradient (fun w => ‖gradient f (prefixProjection (m*d) d w)‖ ^ 2) z⟫_ℝ :=
    (lifted_interaction_eq hf2).symm
  rw [hext, splitInternalGenerator_eq_generator, splitInternalGenerator_eq_generator]
  dsimp only [localEnergyTerm, externalEnergyTerm, FiniteGeneratorCalculus.generator]
  simp only [real_inner_comm]
  ring

omit [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))] in
/-- At the top level the external sum is empty and the split generator is `𝓛_N` on the full
configuration. -/
theorem sharpSplitGenerator_terminal (a : Position d → Position d)
    (K : Position d → Position d → Position d) (f : Point (N*d) → ℝ) :
    sharpSplitGenerator (m := N) le_rfl a K f =
      cylinder le_rfl (splitInternalGenerator N a K f) := by
  funext x
  change _ + _ = _
  have hempty : Finset.univ.filter (fun j : Fin N => N ≤ j.val) = ∅ := by
    ext j
    simp [Nat.not_le.mpr j.isLt]
  rw [hempty, Finset.sum_empty, mul_zero, add_zero]

/-- The exact energy derivative decomposition at the top level `m = N`. -/
theorem terminal_sharpSplitEnergyDerivative_eq {P : ℝ} (hP : 0 < P) (hN : 0 < N)
    (μ : Measure (Point (N*d))) [IsFiniteMeasure μ] (σ : Test (N*d) →ₗ[ℝ] ℝ)
    (h : SplitKernel a K La L₁ L₂ M)
    (ha : ∀ i x, a (x + Pi.single i P) = a x)
    (hx : ∀ i x y, K (x + Pi.single i P) y = K x y)
    (hy : ∀ i x y, K x (y + Pi.single i P) = K x y)
    {f : Point (N*d) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : PeriodicOf P (f ∘ (PeriodicBochner.coordinateEquiv (N*d)).symm)) :
    2 * pairing μ (WeightedTangent.representative μ σ).val
        (sharpSplitGenerator (m := N) le_rfl a K f) -
      (∫ x, sharpSplitGenerator (m := N) le_rfl a K (fun y => ‖gradient f y‖ ^ 2) x ∂μ) =
    localEnergyTerm P (μ.map (marginalProjection (k := N) le_rfl))
      (prefixSource le_rfl μ (WeightedTangent.representative μ σ).val) (splitDrift N a K) f := by
  rw [sharpSplitGenerator_terminal, sharpSplitGenerator_terminal,
    prefixSource_periodic_pairing le_rfl μ (WeightedTangent.representative μ σ).val hP
      (splitInternalGenerator_smooth h N hf) (splitInternalGenerator_periodic hN ha hx hy N hp)]
  have hs := splitInternalGenerator_smooth h N (BochnerIdentity.smooth_gradient_norm_sq hf)
  rw [show (∫ x, cylinder (m := N) le_rfl
      (splitInternalGenerator N a K (fun y => ‖gradient f y‖ ^ 2)) x ∂μ) =
      ∫ y, splitInternalGenerator N a K (fun y => ‖gradient f y‖ ^ 2) y
        ∂μ.map (marginalProjection (k := N) le_rfl) from
    (integral_map (marginalProjection (k := N) le_rfl).continuous.measurable.aemeasurable
      hs.continuous.aestronglyMeasurable).symm]
  rfl

end SharpWasserstein.Sharp.Hierarchy
