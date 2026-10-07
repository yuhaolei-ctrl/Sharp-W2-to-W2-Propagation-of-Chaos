module

public import SharpWasserstein.Compat
public import SharpWasserstein.PropagatedSourceEquation
public import SharpWasserstein.ParticleFlowPermutation

@[expose] public section

/-! Covariance of actual differentiated flow expectations and their propagated
finite-energy sources. The initial field is only required to be equivariant
almost everywhere; no covariance of the selected Jacobian flux is assumed. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal ContDiff InnerProductSpace
namespace SharpWasserstein.PropagatedSourcePermutation
open WeightedTangent PropagatedSourceEquation FlowSemigroupDerivative NoiseAverage

/-- Pullback acts on genuine compact smooth tests. -/
def pullTest {n : ℕ} (L : Point n ≃L[ℝ] Point n) (φ : Test n) : Test n :=
  ⟨(φ : Point n → ℝ) ∘ L, φ.property.1.comp L.contDiff,
    φ.property.2.comp_homeomorph L.toHomeomorph⟩

/-- The chain rule uses the inverse/adjoint action implicitly through the exact
pairing; it never treats a gradient as a covariant vector under pullback. -/
theorem pullTest_gradient_pairing {n : ℕ} (L : Point n ≃L[ℝ] Point n)
    (φ : Test n) (x v : Point n) :
    ⟪gradient (pullTest L φ : Point n → ℝ) x, v⟫_ℝ = ⟪gradient (φ : Point n → ℝ) (L x), L v⟫_ℝ := by
  simp only [inner_gradient_left]
  change fderiv ℝ ((φ : Point n → ℝ) ∘ L) x v = _
  rw [L.comp_right_fderiv]
  rfl

variable {n : ℕ} [MeasurableSpace (Point n)] [BorelSpace (Point n)]
  {b : Point n → Point n} {M K : ℝ≥0}
  (hv : Continuous (Function.uncurry (fun _ : ℝ => b)))
  (hb : ∀ _ : ℝ, ∀ x, ‖b x‖ ≤ M) (hl : ∀ _ : ℝ, LipschitzWith K b)
  {T : ℝ} [MeasurableSpace C(Icc 0 T, Point n)] [BorelSpace C(Icc 0 T, Point n)]
  (hT : 0 ≤ T) (L : Point n ≃L[ℝ] Point n)
  (hcomm : ∀ x, b (L x) = L (b x))

include hcomm in
omit [MeasurableSpace (Point n)] [BorelSpace (Point n)]
  [MeasurableSpace C(Icc 0 T, Point n)] [BorelSpace C(Icc 0 T, Point n)] in
/-- Equivariance of the actual selected flow follows from trajectory uniqueness. -/
theorem flow_covariant (x : Point n) (w : C(Icc 0 T, Point n))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    BoundedFlow.flow hv hb hl hT (L x) (equivPath L w) t =
      L (BoundedFlow.flow hv hb hl hT x w t) := by
  apply BoundedFlow.flow_eq_of_trajectory hv hb hl hT (L x) (equivPath L w)
    (X := fun r => L (BoundedFlow.flow hv hb hl hT x w r)) _ ht
  have h := (BoundedFlow.flow_trajectory hv hb hl hT x w).map_equiv L
  have he : (fun (_ : ℝ) y => L (b (L.symm y))) = (fun _ => b) := by
    funext r y
    rw [← hcomm, L.apply_symm_apply]
  rw [he] at h
  exact h

include hcomm in
omit [MeasurableSpace (Point n)] [BorelSpace (Point n)]
  [MeasurableSpace C(Icc 0 T, Point n)] [BorelSpace C(Icc 0 T, Point n)] in
/-- The actual initial-value Jacobian commutes with simultaneous permutation
of state, continuous noise and tangent vector. This follows by differentiating
the proved flow identity, without a Jacobian covariance hypothesis. -/
theorem flow_fderiv_covariant (x v : Point n) (w : C(Icc 0 T, Point n))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    fderiv ℝ (fun y => BoundedFlow.flow hv hb hl hT y (equivPath L w) t) (L x) (L v) =
      L (fderiv ℝ (fun y => BoundedFlow.flow hv hb hl hT y w t) x v) := by
  have he : (fun y => BoundedFlow.flow hv hb hl hT y (equivPath L w) t) ∘ L =
      L ∘ (fun y => BoundedFlow.flow hv hb hl hT y w t) := by
    funext y
    exact flow_covariant hv hb hl hT L hcomm y w ht
  have hj := congrArg (fun f : Point n → Point n => fderiv ℝ f x v) he
  rw [L.comp_right_fderiv, L.comp_fderiv] at hj
  exact hj

include hcomm in
omit [MeasurableSpace (Point n)] [BorelSpace (Point n)] in
/-- Permuting the full continuous input law gives covariance of the actual
flow semigroup, including at time zero. -/
theorem expectation_covariant (ξ : Measure C(Icc 0 T, Point n))
    (hξ : ξ.map (equivPath L) = ξ) {t : ℝ} (ht : t ∈ Icc 0 T)
    (φ : Test n) (x : Point n) :
    expectation hv hb hl hT ξ (t := t) (φ : Point n → ℝ) (L x) =
      expectation hv hb hl hT ξ (t := t) (pullTest L φ : Point n → ℝ) x := by
  unfold expectation
  have hi : AEStronglyMeasurable
      (fun w => (φ : Point n → ℝ) (BoundedFlow.flow hv hb hl hT (L x) w t)) (ξ.map (equivPath L)) :=
    (φ.property.1.continuous.comp ((BoundedFlow.flow_continuous hv hb hl hT ht).comp
      (continuous_const.prodMk continuous_id))).aestronglyMeasurable
  rw [← hξ, integral_map (equivPath_continuous L).measurable.aemeasurable hi]
  rw [hξ]
  apply integral_congr_ae
  exact Eventually.of_forall (fun w => congrArg (φ : Point n → ℝ)
    (flow_covariant hv hb hl hT L hcomm x w ht))

include hcomm in
omit [MeasurableSpace (Point n)] [BorelSpace (Point n)] in
/-- Differentiating the proved semigroup covariance yields the actual derivative
identity, without any assumed equivariance of the flow derivative. -/
theorem expectation_fderiv_covariant (ξ : Measure C(Icc 0 T, Point n))
    (hξ : ξ.map (equivPath L) = ξ) {t : ℝ} (ht : t ∈ Icc 0 T)
    (φ : Test n) (x v : Point n) :
    fderiv ℝ (expectation hv hb hl hT ξ (t := t) (pullTest L φ : Point n → ℝ)) x v =
      fderiv ℝ (expectation hv hb hl hT ξ (t := t) (φ : Point n → ℝ)) (L x) (L v) := by
  have he : expectation hv hb hl hT ξ (t := t) (pullTest L φ : Point n → ℝ) =
      (expectation hv hb hl hT ξ (t := t) (φ : Point n → ℝ)) ∘ L := by
    funext y
    exact (expectation_covariant hv hb hl hT L hcomm ξ hξ ht φ y).symm
  rw [he, L.comp_right_fderiv]
  rfl

include hcomm in
/-- A permutation-invariant input measure and almost-everywhere equivariant
L² field produce a genuinely invariant propagated source. -/
theorem source_invariant (ξ : Measure C(Icc 0 T, Point n)) [IsProbabilityMeasure ξ]
    (hξ : ξ.map (equivPath L) = ξ) {t : ℝ} (ht : t ∈ Icc 0 T)
    (hbs : ContDiff ℝ ∞ b) (hB : AllDerivativesBounded b)
    (μ : Measure (Point n)) [IsFiniteMeasure μ] (hμ : μ.map L = μ)
    (u : Point n → Point n) (hu : MemLp u 2 μ)
    (hue : ∀ᵐ x ∂μ, u (L x) = L (u x)) (φ : Test n) :
    PropagatedFlux.Flow.source hv hb hl hT ξ ht hbs hB μ u hu (pullTest L φ) =
      PropagatedFlux.Flow.source hv hb hl hT ξ ht hbs hB μ u hu φ := by
  rw [PropagatedFlux.Flow.source_eq_semigroup_pairing,
    PropagatedFlux.Flow.source_eq_semigroup_pairing]
  simp_rw [expectation_fderiv_covariant hv hb hl hT L hcomm ξ hξ ht]
  obtain ⟨C,A,hC,hA⟩ := compactTest_bounds φ
  have hf := (expectation_contDiff_one hv hb hl hT ξ ht hbs hB
    (φ.property.1.of_le (by simp)) hC hA).continuous_fderiv (by norm_num)
  have hi : AEStronglyMeasurable
      (fun x => fderiv ℝ (expectation hv hb hl hT ξ (t := t) (φ : Point n → ℝ)) x (u x)) μ :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hf.aestronglyMeasurable.prodMk hu.aestronglyMeasurable)
  calc
    _ = ∫ x, fderiv ℝ (expectation hv hb hl hT ξ (t := t) (φ : Point n → ℝ))
        (L x) (u (L x)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hue] with x hx
      rw [hx]
    _ = ∫ x, fderiv ℝ (expectation hv hb hl hT ξ (t := t) (φ : Point n → ℝ)) x (u x)
        ∂μ.map L := (integral_map L.continuous.measurable.aemeasurable (hμ ▸ hi)).symm
    _ = _ := by rw [hμ]

end SharpWasserstein.PropagatedSourcePermutation
