import SharpWasserstein.PropagatedFlux
import SharpWasserstein.WeightedGradientApproximation

/-! The constructed random-map distribution pairs with bounded smooth
gradients exactly through its canonical representative. Compact cutoff
density, rather than a smoothness assumption on that representative, proves
the extension. -/
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff
namespace SharpWasserstein.PropagatedFlux
open WeightedTangent
variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
  [MeasurableSpace (Point n)] [BorelSpace (Point n)]
  (ρ : Measure Ω) [IsFiniteMeasure ρ] (X : Ω → Point n) (hX : Measurable X)

theorem representative_pairing (V : Lp (Point n) 2 ρ) (w : gradientClosure (ρ.map X)) :
    ⟪WeightedTangent.representative (ρ.map X) (source ρ X hX V),w⟫_ℝ =
      tangentFunctional ρ X hX V w := by
  refine (dense_gradientIntoClosure (ρ.map X)).induction_on w
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro φ
  exact DenseVariational.representative_pairing _ _ (dense_gradientIntoClosure (ρ.map X))
    (finiteEnergy_dense (ρ.map X) _ (source_finiteEnergy ρ X hX V)) φ

/-- Literal output-space pairing equals the actual random flux integral. -/
theorem representative_bounded_smooth_pairing (V : Lp (Point n) 2 ρ)
    {f : Point n → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfa : ∃ A : ℝ,∀ x,|f x| ≤ A) (hfb : ∃ B : ℝ,∀ x,‖gradient f x‖ ≤ B) :
    (∫ x,⟪gradient f x,
      (WeightedTangent.representative (ρ.map X) (source ρ X hX V)).val x⟫_ℝ ∂ρ.map X) =
      ∫ z,⟪gradient f (X z),V z⟫_ℝ ∂ρ := by
  have hg := bounded_smooth_gradient_memLp (ρ.map X) f hf hfb
  let w : gradientClosure (ρ.map X) :=
    ⟨hg.toLp (gradient f),bounded_smooth_gradient_memClosure (ρ.map X) f hf hfa hfb hg⟩
  have he := representative_pairing ρ X hX V w
  change ⟪(WeightedTangent.representative (ρ.map X) (source ρ X hX V)).val,w.val⟫_ℝ =
    ⟪V,pullback ρ X hX w.val⟫_ℝ at he
  rw [L2.inner_def,L2.inner_def] at he
  have hp := Lp.coeFn_compMeasurePreserving w.val (mapPreserving ρ X hX)
  have hgp := (mapPreserving ρ X hX).quasiMeasurePreserving.ae hg.coeFn_toLp
  calc
    _ = ∫ x,⟪(WeightedTangent.representative (ρ.map X) (source ρ X hX V)).val x,w.val x⟫_ℝ ∂ρ.map X := by
      apply integral_congr_ae
      filter_upwards [hg.coeFn_toLp] with x hx
      change _ = ⟪_,hg.toLp (gradient f) x⟫_ℝ
      rw [hx,real_inner_comm]
    _ = _ := he
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hp,hgp] with z hz hzg
      change ⟪V z,(Lp.compMeasurePreserving X (mapPreserving ρ X hX) w.val) z⟫_ℝ = _
      rw [hz]
      change ⟪V z,hg.toLp (gradient f) (X z)⟫_ℝ = _
      rw [hzg,real_inner_comm]

end SharpWasserstein.PropagatedFlux
