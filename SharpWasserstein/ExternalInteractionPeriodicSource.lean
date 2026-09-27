import SharpWasserstein.ExternalInteractionPeriodic

/-! Exact external source averaging against the actual physical-period
representative. Full Euclidean source action is restricted through genuine
periodic tests; no full-space energy is substituted for a periodic energy. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace BigOperators
namespace SharpWasserstein.ExternalInteractionPeriodic
open WeightedTangent WeightedMarginal PeriodicIntegrationByParts PeriodicBochner
open ExternalInteraction ExternalInteractionSymmetry PropagatedSourcePermutation
open WeightedPeriodicFourierScale (PeriodicOf)
open WeightedPeriodicFourierPhysical (physicalPotential)
open PeriodicSmoothGradient (SmoothPeriodicTest)
variable {n d m N : ℕ}

/-- Every actual smooth physical-period Euclidean test belongs to the
constructed normalized test family, with exact equality as a function. -/
theorem exists_physical_test {P : ℝ} (hP : 0 < P) (F : Point n → ℝ)
    (hF : ContDiff ℝ ∞ F) (hp : PeriodicOf P (F ∘ (coordinateEquiv n).symm)) :
    ∃ g : SmoothPeriodicTest n, physicalPotential P g.val = F := by
  obtain ⟨g,hg⟩ := WeightedPeriodicFourierPhysical.exists_normalized_test hP
    (F ∘ (coordinateEquiv n).symm) (hF.comp (coordinateEquiv n).symm.contDiff) hp
  refine ⟨g,hg.trans ?_⟩
  funext x
  simp only [pullback,Function.comp_apply,ContinuousLinearEquiv.symm_apply_apply]

theorem physical_test_bounds {P : ℝ} (hP : 0 < P) (F : Point n → ℝ)
    (hF : ContDiff ℝ ∞ F) (hp : PeriodicOf P (F ∘ (coordinateEquiv n).symm)) :
    (∃ A : ℝ, ∀ x, |F x| ≤ A) ∧ (∃ B : ℝ, ∀ x, ‖gradient F x‖ ≤ B) := by
  obtain ⟨g,rfl⟩ := exists_physical_test hP F hF hp
  exact ⟨WeightedPeriodicFourierPhysical.physicalPotential_value_bound P g.val g.property.1 g.property.2,
    WeightedPeriodicFourierPhysical.physicalPotential_gradient_bound P g.val g.property.1 g.property.2⟩

/-- The full and periodic representatives have exactly the same literal
pairing with every genuine smooth physical-period scalar test. -/
theorem periodic_representative_pairing
    [MeasurableSpace (Point n)] [BorelSpace (Point n)]
    {P : ℝ} (hP : 0 < P) (μ : Measure (Point n)) [IsFiniteMeasure μ]
    (σ : Test n →ₗ[ℝ] ℝ) (F : Point n → ℝ) (hF : ContDiff ℝ ∞ F)
    (hp : PeriodicOf P (F ∘ (coordinateEquiv n).symm)) :
    (∫ x,⟪gradient F x,(WeightedTangent.representative μ σ : Lp (Point n) 2 μ) x⟫_ℝ ∂μ) =
      ∫ x,⟪gradient F x,
        ((WeightedPeriodicTangentPhysical.representative P μ σ : gradientClosure μ) :
          Lp (Point n) 2 μ) x⟫_ℝ ∂μ := by
  obtain ⟨g,rfl⟩ := exists_physical_test hP F hF hp
  rw [← WeightedPeriodicTangentPhysical.gradientVector_pairing,
    real_inner_comm,← WeightedPeriodicTangentPhysical.source_eq_full_pairing,
    WeightedPeriodicTangentPhysical.representative_divergence]

/-- The actual observed source action on a physical-period test is represented
by its physical-period tangent, obtained from the genuine random observation. -/
theorem observedSource_periodic_pairing
    [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
    [MeasurableSpace (Point (m*d+d))] [BorelSpace (Point (m*d+d))]
    {P : ℝ} (hP : 0 < P) (hm : m ≤ N) (j : Fin N)
    (μ : Measure (Point (N*d))) [IsFiniteMeasure μ] (U : Lp (Point (N*d)) 2 μ)
    (F : Point (m*d+d) → ℝ) (hF : ContDiff ℝ ∞ F)
    (hp : PeriodicOf P (F ∘ (coordinateEquiv (m*d+d)).symm)) :
    pairing μ U (F ∘ observation hm j) =
      ∫ y,⟪gradient F y,
        ((WeightedPeriodicTangentPhysical.representative P (μ.map (observation hm j))
          (observedSource hm j μ U) : gradientClosure (μ.map (observation hm j))) :
          Lp (Point (m*d+d)) 2 (μ.map (observation hm j))) y⟫_ℝ ∂μ.map (observation hm j) := by
  obtain ⟨hA,hB⟩ := physical_test_bounds hP F hF hp
  rw [observedSource_bounded_pairing hm j μ U F hF hA hB]
  exact periodic_representative_pairing hP _ _ F hF hp

/-- Exact finite-N averaging with a literal physical periodic representative
at the next coordinate; the coefficient is (N−m)/N. -/
theorem external_pairing_meanField_periodic
    [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
    [MeasurableSpace (Point (m*d+d))] [BorelSpace (Point (m*d+d))]
    {P : ℝ} (hP : 0 < P) (hm : m < N)
    (μ : Measure (Point (N*d))) [IsFiniteMeasure μ]
    (hμ : ∀ e : Equiv.Perm (Fin N), μ.map (euclideanPermutation e) = μ)
    (U : Lp (Point (N*d)) 2 μ)
    (hU : ∀ e : Equiv.Perm (Fin N), ∀ᵐ x ∂μ,
      U (euclideanPermutation e x) = euclideanPermutation e (U x))
    (F : Point (m*d+d) → ℝ) (hF : ContDiff ℝ ∞ F)
    (hp : PeriodicOf P (F ∘ (coordinateEquiv (m*d+d)).symm)) :
    (N:ℝ)⁻¹*(∑ j : Fin N with m ≤ j.val,pairing μ U (F ∘ observation hm.le j)) =
      (((N:ℝ)-m)/N)*∫ y,⟪gradient F y,
        ((WeightedPeriodicTangentPhysical.representative P (μ.map (observation hm.le ⟨m,hm⟩))
          (observedSource hm.le ⟨m,hm⟩ μ U) : gradientClosure (μ.map (observation hm.le ⟨m,hm⟩))) :
          Lp (Point (m*d+d)) 2 (μ.map (observation hm.le ⟨m,hm⟩))) y⟫_ℝ
          ∂μ.map (observation hm.le ⟨m,hm⟩) := by
  rw [external_pairing_meanField hm μ hμ U hU,observedSource_periodic_pairing hP hm.le ⟨m,hm⟩ μ U F hF hp]

/-- Apply exact periodic source averaging to the actual external interaction.
Kernel periodicity supplies test admissibility; it is not an assumed pairing. -/
theorem external_interaction_meanField_periodic
    [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
    [MeasurableSpace (Point (m*d+d))] [BorelSpace (Point (m*d+d))]
    {P : ℝ} (hP : 0 < P) (hm : m < N)
    (μ : Measure (Point (N*d))) [IsFiniteMeasure μ]
    (hμ : ∀ e : Equiv.Perm (Fin N), μ.map (euclideanPermutation e) = μ)
    (U : Lp (Point (N*d)) 2 μ)
    (hU : ∀ e : Equiv.Perm (Fin N), ∀ᵐ x ∂μ,
      U (euclideanPermutation e x) = euclideanPermutation e (U x))
    {b : Position d → Position d → Position d} (hb : BoundedSmoothKernel b)
    (hx : ∀ a x y, b (x+Pi.single a P) y = b x y)
    (hy : ∀ a x y, b x (y+Pi.single a P) = b x y)
    {f : Point (m*d) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : PeriodicOf P (f ∘ (coordinateEquiv (m*d)).symm)) :
    (N:ℝ)⁻¹*(∑ j : Fin N with m ≤ j.val,pairing μ U (particleInteraction hm.le j b f)) =
      (((N:ℝ)-m)/N)*∫ y,⟪gradient (interaction b f) y,
        ((WeightedPeriodicTangentPhysical.representative P (μ.map (observation hm.le ⟨m,hm⟩))
          (observedSource hm.le ⟨m,hm⟩ μ U) : gradientClosure (μ.map (observation hm.le ⟨m,hm⟩))) :
          Lp (Point (m*d+d)) 2 (μ.map (observation hm.le ⟨m,hm⟩))) y⟫_ℝ
          ∂μ.map (observation hm.le ⟨m,hm⟩) :=
  external_pairing_meanField_periodic hP hm μ hμ U hU _ (interaction_smooth hb hf)
    (interaction_periodic hx hy hp)

/-- Scalar source exchangeability is sufficient for the genuine external
periodic identity: equivariance of the initial full representative is derived. -/
theorem canonical_external_interaction_meanField_periodic
    [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
    [MeasurableSpace (Point (m*d+d))] [BorelSpace (Point (m*d+d))]
    {P : ℝ} (hP : 0 < P) (hm : m < N)
    (μ : Measure (Point (N*d))) [IsFiniteMeasure μ]
    (hμ : ∀ e : Equiv.Perm (Fin N), μ.map (euclideanPermutation e) = μ)
    (σ : Test (N*d) →ₗ[ℝ] ℝ) (hσE : FiniteEnergy μ σ)
    (hσ : ∀ e : Equiv.Perm (Fin N), ∀ φ : Test (N*d),
      σ (pullTest (euclideanPermutation e) φ) = σ φ)
    {b : Position d → Position d → Position d} (hb : BoundedSmoothKernel b)
    (hx : ∀ a x y, b (x+Pi.single a P) y = b x y)
    (hy : ∀ a x y, b x (y+Pi.single a P) = b x y)
    {f : Point (m*d) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : PeriodicOf P (f ∘ (coordinateEquiv (m*d)).symm)) :
    (N:ℝ)⁻¹*(∑ j : Fin N with m ≤ j.val,pairing μ
      (WeightedTangent.representative μ σ : Lp (Point (N*d)) 2 μ) (particleInteraction hm.le j b f)) =
      (((N:ℝ)-m)/N)*∫ y,⟪gradient (interaction b f) y,
        ((WeightedPeriodicTangentPhysical.representative P (μ.map (observation hm.le ⟨m,hm⟩))
          (observedSource hm.le ⟨m,hm⟩ μ (WeightedTangent.representative μ σ).val) :
          gradientClosure (μ.map (observation hm.le ⟨m,hm⟩))) :
          Lp (Point (m*d+d)) 2 (μ.map (observation hm.le ⟨m,hm⟩))) y⟫_ℝ
          ∂μ.map (observation hm.le ⟨m,hm⟩) := by
  apply external_interaction_meanField_periodic hP hm μ hμ _ _ hb hx hy hf hp
  intro e
  exact WeightedSourceSymmetry.representative_equivariant μ (euclideanPermutationIsometry e)
    (hμ e) σ hσE (hσ e)

/-- The internal drift contribution also pairs with the actual periodic
representative, with its genuine full-N normalization and self-terms. -/
theorem internalDrift_periodic_representative_pairing
    [MeasurableSpace (Point (m*d))] [BorelSpace (Point (m*d))]
    {P : ℝ} (hP : 0 < P) (μ : Measure (Point (m*d))) [IsFiniteMeasure μ]
    (σ : Test (m*d) →ₗ[ℝ] ℝ) (N : ℕ)
    {b : Position d → Position d → Position d} (hb : BoundedSmoothKernel b)
    (hx : ∀ a x y, b (x+Pi.single a P) y = b x y)
    (hy : ∀ a x y, b x (y+Pi.single a P) = b x y)
    {f : Point (m*d) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : PeriodicOf P (f ∘ (coordinateEquiv (m*d)).symm)) :
    (∫ x,⟪gradient (fun y => ⟪internalDrift N b y,gradient f y⟫_ℝ) x,
      (WeightedTangent.representative μ σ : Lp (Point (m*d)) 2 μ) x⟫_ℝ ∂μ) =
    ∫ x,⟪gradient (fun y => ⟪internalDrift N b y,gradient f y⟫_ℝ) x,
      ((WeightedPeriodicTangentPhysical.representative P μ σ : gradientClosure μ) :
        Lp (Point (m*d)) 2 μ) x⟫_ℝ ∂μ :=
  periodic_representative_pairing hP μ σ _ (internalDrift_pairing_smooth hb N hf)
    (internalDrift_pairing_periodic hx hy N hp)

end SharpWasserstein.ExternalInteractionPeriodic
