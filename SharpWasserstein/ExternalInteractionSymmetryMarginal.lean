import SharpWasserstein.ExternalInteractionSymmetryAverage
import SharpWasserstein.PropagatedFlux
import SharpWasserstein.WeightedGradientApproximation

/-! The representative extra-coordinate source is constructed from the actual
observation and projected L² flux. Its canonical tangent pairs correctly with
bounded smooth noncompact tests, by the proved compact-cutoff gradient closure. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal ContDiff InnerProductSpace BigOperators
namespace SharpWasserstein.ExternalInteractionSymmetry
open WeightedTangent PropagatedSourcePermutation

section RandomMap
variable {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
  [MeasurableSpace (Point k)] [BorelSpace (Point k)]
  (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → Point k) (hX : Measurable X)
  (V : Lp (Point k) 2 μ)

/-- The Riesz representative agrees with the actual random-map functional on
the whole closed gradient space, proved from compact tests by density. -/
theorem randomSource_closed_pairing (w : gradientClosure (μ.map X)) :
    PropagatedFlux.tangentFunctional μ X hX V w =
      ⟪(representative (μ.map X) (PropagatedFlux.source μ X hX V) :
        Lp (Point k) 2 (μ.map X)), (w : Lp (Point k) 2 (μ.map X))⟫_ℝ := by
  refine (dense_gradientIntoClosure (μ.map X)).induction_on w
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro φ
  have hp := representative_divergence (μ.map X) (PropagatedFlux.source μ X hX V)
    (PropagatedFlux.source_finiteEnergy μ X hX V) φ
  rw [gradient_pairing_eq_inner, real_inner_comm] at hp
  exact hp

/-- Bounded smooth noncompact tests are legitimate source tests through actual
compact cutoff approximation of their gradients. No marginal consistency or
conditional expectation identity is postulated. -/
theorem randomSource_bounded_pairing (F : Point k → ℝ) (hF : ContDiff ℝ ∞ F)
    (hFa : ∃ A : ℝ, ∀ x, |F x| ≤ A) (hFb : ∃ B : ℝ, ∀ x, ‖gradient F x‖ ≤ B) :
    (∫ z, ⟪gradient F (X z), V z⟫_ℝ ∂μ) =
      ∫ y, ⟪gradient F y,
        (representative (μ.map X) (PropagatedFlux.source μ X hX V) :
          Lp (Point k) 2 (μ.map X)) y⟫_ℝ ∂μ.map X := by
  have hg := bounded_smooth_gradient_memLp (μ.map X) F hF hFb
  let g : gradientClosure (μ.map X) :=
    ⟨hg.toLp (gradient F), bounded_smooth_gradient_memClosure (μ.map X) F hF hFa hFb hg⟩
  have hl : PropagatedFlux.tangentFunctional μ X hX V g =
      ∫ z, ⟪gradient F (X z), V z⟫_ℝ ∂μ := by
    change ⟪V, PropagatedFlux.pullback μ X hX (hg.toLp (gradient F))⟫_ℝ = _
    rw [L2.inner_def]
    have ha := Lp.coeFn_compMeasurePreserving (hg.toLp (gradient F))
      (PropagatedFlux.mapPreserving μ X hX)
    have hb := (PropagatedFlux.mapPreserving μ X hX).quasiMeasurePreserving.ae hg.coeFn_toLp
    apply integral_congr_ae
    filter_upwards [ha,hb] with z hz hw
    change ⟪V z, (Lp.compMeasurePreserving X (PropagatedFlux.mapPreserving μ X hX)
      (hg.toLp (gradient F))) z⟫_ℝ = _
    rw [hz]
    dsimp only [Function.comp_apply]
    rw [hw,real_inner_comm]
  have hr := randomSource_closed_pairing μ X hX V g
  rw [hl, L2.inner_def] at hr
  rw [hr]
  apply integral_congr_ae
  filter_upwards [hg.coeFn_toLp] with y hy
  change ⟪_, hg.toLp (gradient F) y⟫_ℝ = _
  rw [hy,real_inner_comm]

end RandomMap

section Observation
variable {d m N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  [MeasurableSpace (Point (m*d+d))] [BorelSpace (Point (m*d+d))]
  (hm : m ≤ N) (j : Fin N) (μ : Measure (Point (N*d))) [IsFiniteMeasure μ]
  (U : Lp (Point (N*d)) 2 μ)

/-- The actual projected random velocity in the observed particle coordinates. -/
def observedVelocity : Lp (Point (m*d+d)) 2 μ :=
  (observation hm j).compLpₗ 2 μ U

omit [BorelSpace (Point (N*d))] [MeasurableSpace (Point (m*d+d))]
  [BorelSpace (Point (m*d+d))] [IsFiniteMeasure μ] in
theorem observedVelocity_ae : observedVelocity hm j μ U =ᵐ[μ] fun x => observation hm j (U x) :=
  (observation hm j).coeFn_compLp U

/-- A genuine finite-energy marginal source, built from the actual observation
and projected full tangent, not specified by a presumed marginal formula. -/
def observedSource : Test (m*d+d) →ₗ[ℝ] ℝ :=
  PropagatedFlux.source μ (observation hm j) (observation hm j).continuous.measurable
    (observedVelocity hm j μ U)

theorem observedSource_finiteEnergy :
    FiniteEnergy (μ.map (observation hm j)) (observedSource hm j μ U) :=
  PropagatedFlux.source_finiteEnergy _ _ _ _

/-- The constructed source has the exact cylinder differential action on
all genuine compact tests of the observed configuration. -/
theorem observedSource_apply (φ : Test (m*d+d)) :
    observedSource hm j μ U φ = pairing μ U ((φ : Point (m*d+d) → ℝ) ∘ observation hm j) := by
  rw [observedSource, PropagatedFlux.source_apply]
  unfold pairing
  apply integral_congr_ae
  filter_upwards [observedVelocity_ae hm j μ U] with x hx
  rw [hx, inner_gradient_left, fderiv_comp x (test_differentiable φ _) (observation hm j).differentiableAt,
    ContinuousLinearMap.fderiv]
  rfl

/-- The genuine observed canonical tangent represents the source action on
bounded smooth tests, including the actual external interaction. -/
theorem observedSource_bounded_pairing (F : Point (m*d+d) → ℝ) (hF : ContDiff ℝ ∞ F)
    (hFa : ∃ A : ℝ, ∀ x, |F x| ≤ A) (hFb : ∃ B : ℝ, ∀ x, ‖gradient F x‖ ≤ B) :
    pairing μ U (F ∘ observation hm j) =
      ∫ y, ⟪gradient F y,
        (representative (μ.map (observation hm j)) (observedSource hm j μ U) :
          Lp (Point (m*d+d)) 2 (μ.map (observation hm j))) y⟫_ℝ ∂μ.map (observation hm j) := by
  unfold observedSource
  rw [← randomSource_bounded_pairing μ (observation hm j) (observation hm j).continuous.measurable
    (observedVelocity hm j μ U) F hF hFa hFb]
  unfold pairing
  apply integral_congr_ae
  filter_upwards [observedVelocity_ae hm j μ U] with x hx
  rw [hx, inner_gradient_left, fderiv_comp x (hF.differentiable (by simp) _) (observation hm j).differentiableAt,
    ContinuousLinearMap.fderiv]
  rfl

end Observation

/-- The exact external source contribution is an integral against the actual
(m+1)-particle canonical tangent, with its finite-N coefficient. -/
theorem external_pairing_meanField_marginal {d m N : ℕ}
    [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
    [MeasurableSpace (Point (m*d+d))] [BorelSpace (Point (m*d+d))]
    (hm : m < N) (μ : Measure (Point (N*d))) [IsFiniteMeasure μ]
    (hμ : ∀ e : Equiv.Perm (Fin N), μ.map (euclideanPermutation e) = μ)
    (U : Lp (Point (N*d)) 2 μ)
    (hU : ∀ e : Equiv.Perm (Fin N), ∀ᵐ x ∂μ,
      U (euclideanPermutation e x) = euclideanPermutation e (U x))
    (F : Point (m*d+d) → ℝ) (hF : ContDiff ℝ ∞ F)
    (hFa : ∃ A : ℝ, ∀ x, |F x| ≤ A) (hFb : ∃ B : ℝ, ∀ x, ‖gradient F x‖ ≤ B) :
    (N:ℝ)⁻¹*(∑ j : Fin N with m ≤ j.val, pairing μ U (F ∘ observation hm.le j)) =
      (((N:ℝ)-m)/N) * ∫ y, ⟪gradient F y,
        (representative (μ.map (observation hm.le ⟨m,hm⟩))
          (observedSource hm.le ⟨m,hm⟩ μ U) :
          Lp (Point (m*d+d)) 2 (μ.map (observation hm.le ⟨m,hm⟩))) y⟫_ℝ
        ∂μ.map (observation hm.le ⟨m,hm⟩) := by
  rw [external_pairing_meanField hm μ hμ U hU,
    observedSource_bounded_pairing hm.le ⟨m,hm⟩ μ U F hF hFa hFb]

end SharpWasserstein.ExternalInteractionSymmetry
