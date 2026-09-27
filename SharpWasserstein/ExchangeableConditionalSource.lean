import SharpWasserstein.ExchangeableEntropy

/-!
# Conditional source bounds for actual exchangeable marginals

The next-particle conditional law is obtained by disintegrating the actual
(m+1)-particle marginal. The chain rule identifies its integrated KL with the
finite marginal entropy increment. Vector-valued Pinsker and finite summation
then give the external drift source bound used in the hierarchy.
-/

noncomputable section

open MeasureTheory InformationTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace SharpWasserstein

/-- The (m+1)-particle marginal, presented as prefix times next particle. -/
def nextParticleJoint {d m N : ℕ} (hm : m < N)
    (P : Measure (Configuration d N)) : Measure (Configuration d m × Position d) :=
  (marginal (Nat.succ_le_of_lt hm) P).map (splitLastParticle d m)

instance nextParticleJoint_isProbabilityMeasure {d m N : ℕ} (hm : m < N)
    (P : Measure (Configuration d N)) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (nextParticleJoint hm P) :=
  Measure.isProbabilityMeasure_map (splitLastParticle d m).measurable.aemeasurable

theorem nextParticleJoint_fst {d m N : ℕ} (hm : m < N)
    (P : Measure (Configuration d N)) :
    (nextParticleJoint hm P).fst = marginal hm.le P := by
  unfold nextParticleJoint
  rw [Measure.fst, Measure.map_map measurable_fst (splitLastParticle d m).measurable]
  have hfun : Prod.fst ∘ splitLastParticle d m = restrictCoordinates (Nat.le_succ m) := by
    funext x
    exact congrArg Prod.fst (splitLastParticle_apply x)
  rw [hfun]
  exact marginal_marginal (Nat.le_succ m) (Nat.succ_le_of_lt hm) P

theorem nextParticleJoint_klDiv {d m N : ℕ} (hm : m < N)
    (P : Measure (Configuration d N)) [IsProbabilityMeasure P]
    (r : Measure (Position d)) [IsProbabilityMeasure r] :
    klDiv (nextParticleJoint hm P) ((tensorLaw r m).prod r) =
      klDiv (marginal (Nat.succ_le_of_lt hm) P) (tensorLaw r (m + 1)) := by
  unfold nextParticleJoint
  rw [← map_tensorLaw_splitLastParticle r]
  exact klDiv_map_measurableEquiv _

theorem nextParticleJoint_klDiv_ne_top {d m N : ℕ} (hm : m < N)
    {P : Measure (Configuration d N)} [IsProbabilityMeasure P]
    {r : Measure (Position d)} [IsProbabilityMeasure r]
    (hfinite : klDiv P (tensorLaw r N) ≠ ∞) :
    klDiv ((nextParticleJoint hm P).fst ⊗ₘ (nextParticleJoint hm P).condKernel)
      (tensorLaw r m ⊗ₘ Kernel.const (Configuration d m) r) ≠ ∞ := by
  rw [(nextParticleJoint hm P).disintegrate (nextParticleJoint hm P).condKernel,
    Measure.compProd_const, nextParticleJoint_klDiv]
  exact marginal_klDiv_ne_top (Nat.succ_le_of_lt hm) hfinite

/-- The actual next-particle conditional KL integral is the marginal entropy
increment. This identity requires no exchangeability assumption. -/
theorem conditional_klDiv_eq_marginal_entropy_increment {d m N : ℕ} (hm : m < N)
    {P : Measure (Configuration d N)} [IsProbabilityMeasure P]
    {r : Measure (Position d)} [IsProbabilityMeasure r]
    (hfinite : klDiv P (tensorLaw r N) ≠ ∞) :
    ∫ x, (klDiv ((nextParticleJoint hm P).condKernel x) r).toReal ∂marginal hm.le P =
      entropyIncrement (marginalEntropy P r) m := by
  have h := integral_kernel_klDiv_eq_entropy_increment (nextParticleJoint_klDiv_ne_top hm hfinite)
  rw [(nextParticleJoint hm P).disintegrate (nextParticleJoint hm P).condKernel,
    Measure.compProd_const, nextParticleJoint_klDiv, nextParticleJoint_fst] at h
  simp only [Kernel.const_apply] at h
  rw [entropyIncrement, marginalEntropy_eq (Nat.succ_le_of_lt hm), marginalEntropy_eq hm.le]
  exact h

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Square-integrability of a bounded conditional expectation discrepancy,
proved using the finite conditional KL integral. -/
theorem integrable_conditional_discrepancy_sq {d m N : ℕ} (hm : m < N)
    {P : Measure (Configuration d N)} [IsProbabilityMeasure P]
    {r : Measure (Position d)} [IsProbabilityMeasure r]
    (hfinite : klDiv P (tensorLaw r N) ≠ ∞)
    {F : Configuration d m → Position d → E} {M : ℝ} (hM : 0 ≤ M)
    (hF : StronglyMeasurable (Function.uncurry F))
    (hbound : ∀ᵐ x ∂marginal hm.le P, ∀ᵐ y ∂r, ‖F x y‖ ≤ M) :
    Integrable (fun x ↦ ‖(∫ y, F x y ∂(nextParticleJoint hm P).condKernel x)
      - ∫ y, F x y ∂r‖ ^ 2) (marginal hm.le P) := by
  let Q := nextParticleJoint hm P
  have hcond := conditional_joint_klDiv_ne_top (nextParticleJoint_klDiv_ne_top hm hfinite)
  have hbound' : ∀ᵐ x ∂Q.fst, ∀ᵐ y ∂(Kernel.const (Configuration d m) r) x,
      ‖F x y‖ ≤ M := by
    simpa only [Q, nextParticleJoint_fst, Kernel.const_apply] using hbound
  have hpoint := kernel_norm_integral_difference_sq_le_klDiv hM
    (ae_kernel_klDiv_ne_top hcond)
    (Filter.Eventually.of_forall fun x ↦
      (hF.comp_measurable measurable_prodMk_left).aestronglyMeasurable) hbound'
  have hmeas : StronglyMeasurable (fun x ↦
      ‖(∫ y, F x y ∂Q.condKernel x) - ∫ y, F x y ∂(Kernel.const (Configuration d m) r) x‖ ^ 2) :=
    ((hF.integral_kernel_prod_right (κ := Q.condKernel)).sub
      (hF.integral_kernel_prod_right (κ := Kernel.const (Configuration d m) r))).norm.pow 2
  have hright := (integrable_kernel_klDiv_toReal hcond).const_mul (2 * M ^ 2)
  have hleft := hright.mono_nonneg hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _) hpoint
  simpa only [Q, nextParticleJoint_fst, Kernel.const_apply, Pi.pow_apply, Pi.sub_apply] using hleft

/-- Actual vector conditional Pinsker with the entropy increment of the
concrete marginal sequence. -/
theorem conditional_discrepancy_sq_le_marginal_entropy_increment {d m N : ℕ} (hm : m < N)
    {P : Measure (Configuration d N)} [IsProbabilityMeasure P]
    {r : Measure (Position d)} [IsProbabilityMeasure r]
    (hfinite : klDiv P (tensorLaw r N) ≠ ∞)
    {F : Configuration d m → Position d → E} {M : ℝ} (hM : 0 ≤ M)
    (hF : StronglyMeasurable (Function.uncurry F))
    (hbound : ∀ᵐ x ∂marginal hm.le P, ∀ᵐ y ∂r, ‖F x y‖ ≤ M) :
    ∫ x, ‖(∫ y, F x y ∂(nextParticleJoint hm P).condKernel x)
        - ∫ y, F x y ∂r‖ ^ 2 ∂marginal hm.le P
      ≤ 2 * M ^ 2 * entropyIncrement (marginalEntropy P r) m := by
  have h := integrated_kernel_norm_difference_sq_le_entropy_increment
    (nextParticleJoint_klDiv_ne_top hm hfinite) hM hF (by
      simpa only [nextParticleJoint_fst, Kernel.const_apply] using hbound)
  rw [(nextParticleJoint hm P).disintegrate (nextParticleJoint hm P).condKernel,
    Measure.compProd_const, nextParticleJoint_klDiv, nextParticleJoint_fst] at h
  simp only [Kernel.const_apply] at h
  rw [entropyIncrement, marginalEntropy_eq (Nat.succ_le_of_lt hm), marginalEntropy_eq hm.le]
  exact h

/-- Summing the genuine conditional discrepancies of the m tagged particles
produces the external source factor m times the next entropy increment. -/
theorem conditional_discrepancy_sum_le_entropy_increment {d m N : ℕ} (hm : m < N)
    {P : Measure (Configuration d N)} [IsProbabilityMeasure P]
    {r : Measure (Position d)} [IsProbabilityMeasure r]
    (hfinite : klDiv P (tensorLaw r N) ≠ ∞)
    {F : Fin m → Configuration d m → Position d → E} {M : ℝ} (hM : 0 ≤ M)
    (hF : ∀ i, StronglyMeasurable (Function.uncurry (F i)))
    (hbound : ∀ i, ∀ᵐ x ∂marginal hm.le P, ∀ᵐ y ∂r, ‖F i x y‖ ≤ M) :
    ∫ x, ∑ i : Fin m, ‖(∫ y, F i x y ∂(nextParticleJoint hm P).condKernel x)
        - ∫ y, F i x y ∂r‖ ^ 2 ∂marginal hm.le P
      ≤ 2 * M ^ 2 * m * entropyIncrement (marginalEntropy P r) m := by
  rw [integral_finsetSum _ (fun i _ ↦
    integrable_conditional_discrepancy_sq hm hfinite hM (hF i) (hbound i))]
  calc
    _ ≤ ∑ _i : Fin m, 2 * M ^ 2 * entropyIncrement (marginalEntropy P r) m :=
      Finset.sum_le_sum (fun i _ ↦
        conditional_discrepancy_sq_le_marginal_entropy_increment hm hfinite hM (hF i) (hbound i))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- The external source energy has the sharp quadratic particle profile.
Its entropy and conditional Pinsker inputs are all derived from actual laws. -/
theorem exchangeable_conditional_source_quadratic_bound {d m N : ℕ} {A M : ℝ}
    (hm0 : 0 < m) (hm : m < N)
    {P : Measure (Configuration d N)} [IsProbabilityMeasure P]
    {r : Measure (Position d)} [IsProbabilityMeasure r]
    (hex : Exchangeable P) (hfinite : klDiv P (tensorLaw r N) ≠ ∞)
    (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hprofile : ∀ j, j ≤ N → marginalEntropy P r j ≤ A * (j : ℝ) ^ 2 / (N : ℝ) ^ 2)
    {F : Fin m → Configuration d m → Position d → E}
    (hF : ∀ i, StronglyMeasurable (Function.uncurry (F i)))
    (hbound : ∀ i, ∀ᵐ x ∂marginal hm.le P, ∀ᵐ y ∂r, ‖F i x y‖ ≤ M) :
    (((N : ℝ) - m) / N) ^ 2 *
      (∫ x, ∑ i : Fin m, ‖(∫ y, F i x y ∂(nextParticleJoint hm P).condKernel x)
        - ∫ y, F i x y ∂r‖ ^ 2 ∂marginal hm.le P)
      ≤ 8 * M ^ 2 * A * (m : ℝ) ^ 2 / (N : ℝ) ^ 2 := by
  have hsum := conditional_discrepancy_sum_le_entropy_increment hm hfinite hM hF hbound
  have hsource := exchangeable_entropy_external_source_bound hex hfinite
    (by omega : 0 < N) hm0 hm.le hA hprofile
  have h1 := mul_le_mul_of_nonneg_left hsum (sq_nonneg (((N : ℝ) - m) / N))
  have h2 := mul_le_mul_of_nonneg_left hsource (by positivity : 0 ≤ 2 * M ^ 2)
  calc
    _ ≤ _ := h1
    _ = 2 * M ^ 2 * ((((N : ℝ) - m) / N) ^ 2 * m *
        entropyIncrement (marginalEntropy P r) m) := by ring
    _ ≤ _ := h2
    _ = _ := by ring

end Hilbert

end SharpWasserstein
