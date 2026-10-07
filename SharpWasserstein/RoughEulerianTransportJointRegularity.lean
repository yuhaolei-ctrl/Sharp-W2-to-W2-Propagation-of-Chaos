module

public import SharpWasserstein.Compat
public import SharpWasserstein.RoughEulerianTransportRegularCoordinates
public import SharpWasserstein.RoughEulerianSpaceTimeSmooth

@[expose] public section

/-! Uniform spatial hypotheses for the actual joint regularized velocity.
Every spatial derivative is obtained by the affine slice inclusion; the
constants are independent of time. No spatial derivative premise is assumed. -/
noncomputable section
open Set MeasureTheory
open scoped NNReal ContDiff
namespace SharpWasserstein.RoughEulerianTransport
open WeightedTangent NoiseAverage RoughEulerianSmoothing

section Generic
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The derivative of the actual affine spatial inclusion. -/
theorem spatial_inclusion_hasFDerivAt (t : ℝ) (x : E) :
    HasFDerivAt (fun y : E => (t,y)) (ContinuousLinearMap.inr ℝ ℝ E) x := by
  have he : (0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E) =
      ContinuousLinearMap.inr ℝ ℝ E := by
    ext z <;> rfl
  rw [← he]
  exact (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)

/-- The spatial derivative is the actual joint derivative restricted to the
spatial summand of the product. -/
theorem spatial_fderiv {f : ℝ × E → F} (hf : Differentiable ℝ f) (t : ℝ) (x : E) :
    fderiv ℝ (fun y => f (t,y)) x =
      (fderiv ℝ f (t,x)).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
  exact ((hf (t,x)).hasFDerivAt.comp x (spatial_inclusion_hasFDerivAt t x)).fderiv

/-- The affine slice inherits actual bounds at every derivative order. -/
theorem spatial_allDerivativesBounded {f : ℝ × E → F}
    (hf : ContDiff ℝ ∞ f) (hB : AllDerivativesBounded f) (t : ℝ) :
    AllDerivativesBounded (fun y => f (t,y)) := by
  apply AllDerivativesBounded.comp_of_fderiv hf (contDiff_const.prodMk contDiff_id) hB
  have hi : fderiv ℝ (fun y : E => (t,y)) = fun _ => ContinuousLinearMap.inr ℝ ℝ E := by
    funext x
    exact (spatial_inclusion_hasFDerivAt t x).fderiv
  change AllDerivativesBounded (fderiv ℝ (fun y : E => (t,y)))
  rw [hi]
  exact allDerivativesBounded_const _

/-- Joint smoothness and actual global derivative bounds provide every
uniform spatial hypothesis of the regular transport theorem. -/
theorem joint_spatial_regular {f : ℝ × E → F}
    (hf : ContDiff ℝ ∞ f) (hB : AllDerivativesBounded f) :
    ∃ M K K₁ : ℝ≥0, (∀ t x, ‖f (t,x)‖ ≤ M) ∧
      (∀ t,LipschitzWith K (fun x => f (t,x))) ∧
      (∀ t,ContDiff ℝ ∞ (fun x => f (t,x))) ∧
      (∀ t,AllDerivativesBounded (fun x => f (t,x))) ∧
      (∀ t,LipschitzWith K₁ (fderiv ℝ (fun x => f (t,x)))) := by
  obtain ⟨M,hM,hMb⟩ := hB.bounded
  obtain ⟨K,hK⟩ := hB.lipschitz (hf.differentiable (by simp))
  obtain ⟨D,hD⟩ := hB.fderiv.lipschitz
    ((contDiff_infty_iff_fderiv.mp hf).2.differentiable (by simp))
  refine ⟨⟨M,hM⟩,K,D*‖ContinuousLinearMap.inr ℝ ℝ E‖₊,
    fun t x => hMb (t,x),?_,fun t => hf.comp (contDiff_const.prodMk contDiff_id),
    spatial_allDerivativesBounded hf hB,?_⟩
  · intro t
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Prod.dist_eq,dist_self,max_eq_right (dist_nonneg)] using hK.dist_le_mul (t,x) (t,y)
  · intro t
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm,spatial_fderiv (hf.differentiable (by simp)),
      spatial_fderiv (hf.differentiable (by simp)),← ContinuousLinearMap.sub_comp]
    calc
      _ ≤ ‖fderiv ℝ f (t,x)-fderiv ℝ f (t,y)‖*‖ContinuousLinearMap.inr ℝ ℝ E‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ((D:ℝ)*dist x y)*‖ContinuousLinearMap.inr ℝ ℝ E‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        simpa only [← dist_eq_norm,Prod.dist_eq,dist_self,max_eq_right (dist_nonneg)] using
          hD.dist_le_mul (t,x) (t,y)
      _ = _ := by simp only [NNReal.coe_mul,coe_nnnorm]; ring
end Generic

section Transport
variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]

/-- Joint regularity is enough for the coefficient-one finite-action bound;
the required time-uniform spatial constants are constructed above. -/
theorem EuclideanCompactWeakContinuity.wassersteinSq_le_finiteAction_of_joint_smooth
    {f : ℝ × Point (N*d) → Point (N*d)}
    {μ : ℝ → ProbabilityMeasure (Point (N*d))} {T : ℝ}
    (h : EuclideanCompactWeakContinuity (fun t x => f (t,x)) μ T)
    (hf : ContDiff ℝ ∞ f) (hB : AllDerivativesBounded f) (hT : 0 ≤ T)
    (hP : HasSecondMoment ((μ 0 : Measure _).map (configurationEuclidean d N).symm))
    {a b : ℝ} (ha : a ∈ Icc 0 T) (hb : b ∈ Icc 0 T) (hab : a ≤ b)
    {E : ℝ → ℝ} (hE : IntervalIntegrable E volume a b)
    (hbound : ∀ᵐ t ∂volume.restrict (Icc a b),
      (∫ x,‖f (t,x)‖^2 ∂(μ t : Measure _)) ≤ E t) :
    wassersteinSq ((μ a : Measure _).map (configurationEuclidean d N).symm)
      ((μ b : Measure _).map (configurationEuclidean d N).symm) ≤
      ENNReal.ofReal ((b-a)*(∫ t in a..b,E t)) := by
  obtain ⟨M,K,K₁,hM,hK,hs,hBs,hK₁⟩ := joint_spatial_regular hf hB
  exact h.wassersteinSq_le_finiteAction hf.continuous hM hK hT hs hBs hK₁
    hP ha hb hab hE hbound
end Transport

variable {d : ℕ} [MeasurableSpace (Point d)] [BorelSpace (Point d)]

/-- The constructed product-convolved flux with Gaussian floor satisfies
all uniform spatial hypotheses, even if the original flux is only integrable. -/
theorem spaceTimeFloorVelocity_spatial_regular {τ ε δ R : ℝ} (hτ : 0 < τ) (hε : 0 < ε)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (ρ : Measure (ℝ × Point d)) [IsFiniteMeasure ρ]
    (hρ : ∀ᵐ z ∂ρ, ‖z‖ ≤ R) {U : ℝ × Point d → Point d} (hU : Integrable U ρ) :
    let f := floorVelocity (1-δ) (spaceTimeDensity τ hτ ε hε ρ)
      (fun p => δ*gaussianFloor p.2) (spaceTimeFlux τ hτ ε hε ρ U)
    ∃ M K K₁ : ℝ≥0, (∀ t x, ‖f (t,x)‖ ≤ M) ∧
      (∀ t,LipschitzWith K (fun x => f (t,x))) ∧
      (∀ t,ContDiff ℝ ∞ (fun x => f (t,x))) ∧
      (∀ t,AllDerivativesBounded (fun x => f (t,x))) ∧
      (∀ t,LipschitzWith K₁ (fderiv ℝ (fun x => f (t,x)))) :=
  joint_spatial_regular (spaceTimeFloorVelocity_smooth hτ hε hδ hδ₁ ρ hU)
    (spaceTimeFloorVelocity_regular hτ hε hδ hδ₁ ρ hρ hU).1

end SharpWasserstein.RoughEulerianTransport
