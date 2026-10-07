module

public import SharpWasserstein.Compat
public import SharpWasserstein.PropagatedSourcePermutation

@[expose] public section

/-! Equivariance of the actual minimum-energy tangent representative is
derived from symmetry of the law and scalar source. The proof uses the
proved energy gap, rather than assuming symmetry of a selected vector field. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology InnerProductSpace ContDiff
namespace SharpWasserstein.WeightedSourceSymmetry
open WeightedTangent PropagatedSourcePermutation
variable {n : ℕ} [MeasurableSpace (Point n)] [BorelSpace (Point n)]
  (μ : Measure (Point n)) (L : Point n ≃ₗᵢ[ℝ] Point n) (hμ : μ.map L = μ)

include hμ in
theorem measurePreserving_isometry : MeasurePreserving L μ μ := ⟨L.continuous.measurable,hμ⟩

def pullVector (v : Lp (Point n) 2 μ) : Lp (Point n) 2 μ :=
  L.symm.toContinuousLinearEquiv.toContinuousLinearMap.compLpₗ 2 μ
    (Lp.compMeasurePreserving L (measurePreserving_isometry μ L hμ) v)

theorem pullVector_ae (v : Lp (Point n) 2 μ) :
    pullVector μ L hμ v =ᵐ[μ] (fun y => L.symm (v (L y))) := by
  filter_upwards [L.symm.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLp
    (Lp.compMeasurePreserving L (measurePreserving_isometry μ L hμ) v),
    Lp.coeFn_compMeasurePreserving v (measurePreserving_isometry μ L hμ)] with y hy hz
  exact hy.trans (congrArg L.symm hz)

theorem pullVector_norm (v : Lp (Point n) 2 μ) : ‖pullVector μ L hμ v‖ = ‖v‖ := by
  have he : ∀ᵐ y ∂μ, ‖pullVector μ L hμ v y‖ =
      ‖Lp.compMeasurePreserving L (measurePreserving_isometry μ L hμ) v y‖ := by
    filter_upwards [pullVector_ae μ L hμ v,
      Lp.coeFn_compMeasurePreserving v (measurePreserving_isometry μ L hμ)] with y hy hz
    rw [hy,hz,L.symm.norm_map]
    rfl
  calc
    _ = ‖Lp.compMeasurePreserving L (measurePreserving_isometry μ L hμ) v‖ := by
      simp only [Lp.norm_def]
      congr 1
      exact eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _) he
    _ = _ := Lp.norm_compMeasurePreserving _ _

omit [MeasurableSpace (Point n)] [BorelSpace (Point n)] in
theorem source_invariant_inverse (σ : Test n →ₗ[ℝ] ℝ)
    (hσ : ∀ φ, σ (pullTest L.toContinuousLinearEquiv φ) = σ φ) (φ : Test n) :
    σ (pullTest L.symm.toContinuousLinearEquiv φ) = σ φ := by
  have he : pullTest L.toContinuousLinearEquiv (pullTest L.symm.toContinuousLinearEquiv φ) = φ := by
    apply Subtype.ext
    funext x
    change (φ : Point n → ℝ) (L.symm (L x)) = (φ : Point n → ℝ) x
    rw [L.symm_apply_apply]
  simpa only [he] using (hσ (pullTest L.symm.toContinuousLinearEquiv φ)).symm

variable [IsFiniteMeasure μ]

theorem pullVector_representative_divergence (σ : Test n →ₗ[ℝ] ℝ) (hσE : FiniteEnergy μ σ)
    (hσ : ∀ φ, σ (pullTest L.toContinuousLinearEquiv φ) = σ φ) (φ : Test n) :
    σ φ = ∫ x, ⟪gradient (φ : Point n → ℝ) x,
      pullVector μ L hμ (representative μ σ : Lp (Point n) 2 μ) x⟫_ℝ ∂μ := by
  let u : Lp (Point n) 2 μ := representative μ σ
  let ψ := pullTest L.symm.toContinuousLinearEquiv φ
  have hi := (integrable_gradient_pairing μ u ψ).aestronglyMeasurable
  have hi' : AEStronglyMeasurable (fun x => ⟪gradient (ψ : Point n → ℝ) x,u x⟫_ℝ) (μ.map L) := by
    rw [hμ]
    exact hi
  have he := integral_map L.continuous.measurable.aemeasurable hi'
  rw [hμ] at he
  calc
    σ φ = σ ψ := (source_invariant_inverse L σ hσ φ).symm
    _ = ∫ x, ⟪gradient (ψ : Point n → ℝ) x,u x⟫_ℝ ∂μ := representative_divergence μ σ hσE ψ
    _ = ∫ x, ⟪gradient (ψ : Point n → ℝ) (L x),u (L x)⟫_ℝ ∂μ := he
    _ = ∫ x, ⟪gradient (φ : Point n → ℝ) x,L.symm (u (L x))⟫_ℝ ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp only [ψ]
        rw [pullTest_gradient_pairing]
        simp only [LinearIsometryEquiv.coe_toContinuousLinearEquiv,LinearIsometryEquiv.symm_apply_apply]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [pullVector_ae μ L hμ u] with x hx
      rw [hx]

include hμ in
/-- The unique minimal-energy representative is genuinely equivariant
almost everywhere, with the correct vector action. -/
theorem representative_equivariant (σ : Test n →ₗ[ℝ] ℝ) (hσE : FiniteEnergy μ σ)
    (hσ : ∀ φ, σ (pullTest L.toContinuousLinearEquiv φ) = σ φ) :
    ∀ᵐ x ∂μ, (representative μ σ : Lp (Point n) 2 μ) (L x) =
      L ((representative μ σ : Lp (Point n) 2 μ) x) := by
  let u : Lp (Point n) 2 μ := representative μ σ
  let v := pullVector μ L hμ u
  have hgap := flux_energy_decomposition μ σ v (pullVector_representative_divergence μ L hμ σ hσE hσ)
  rw [← lp_norm_sq_eq_integral,energy_eq_norm_sq μ σ hσE] at hgap
  have hn : ‖v‖ = ‖u‖ := pullVector_norm μ L hμ u
  have he : v = u := by
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    change ‖v‖^2 = ‖u‖^2+‖v-u‖^2 at hgap
    rw [hn] at hgap
    exact sq_eq_zero_iff.mp (by linarith)
  have hae := pullVector_ae μ L hμ u
  change v =ᵐ[μ] (fun x => L.symm (u (L x))) at hae
  rw [he] at hae
  filter_upwards [hae] with x hx
  have hh := congrArg L hx
  simpa only [LinearIsometryEquiv.apply_symm_apply] using hh.symm

end SharpWasserstein.WeightedSourceSymmetry
