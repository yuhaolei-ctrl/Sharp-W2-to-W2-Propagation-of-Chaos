import SharpWasserstein.PeriodicDriftGradientBound
import SharpWasserstein.PeriodicDiffusionEnergy

/-! Exact drift pairing for the genuine periodic Galerkin optimizers. The
residual is explicitly constructed and proved to vanish using strong gradient
convergence and the derived uniform drift-test gradient bound. -/
noncomputable section
namespace SharpWasserstein.PeriodicDriftResidual
open MeasureTheory Set Filter PeriodicIntegrationByParts PeriodicFourierTests PeriodicBochner
open PeriodicGalerkin PeriodicGradientClosure PeriodicSmoothGradient PeriodicWeakHessian
open PeriodicDriftEnergy PeriodicDriftGradientBound WeightedTangent WeightedDensity
open scoped Topology BigOperators ContDiff InnerProductSpace BoundedContinuousFunction
variable {n : ℕ} [MeasurableSpace (Point n)] [BorelSpace (Point n)]

omit [MeasurableSpace (Point n)] [BorelSpace (Point n)] in
theorem periodic_drift {f : Coordinates n → ℝ} (hpf : Periodic f)
    {b : Coordinates n → Coordinates n} (hpb : ∀ j, Periodic (fun x => b x j)) :
    Periodic (drift b f) := by
  intro i x
  apply Finset.sum_congr rfl
  intro j _
  have hj : b (x + Pi.single i 1) j = b x j := hpb j i x
  rw [hj,periodic_coordinatePartial hpf j i x]

theorem weightedOperator_gradientVector_inner (ρ : Point n →ᵇ ℝ)
    {f g : Coordinates n → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ⟪weightedOperator cubePoint ρ (gradientVector f hf),gradientVector g hg⟫_ℝ =
      ∫ x, ρ ((coordinateEquiv n).symm x)*
        (∑ i : Fin n, coordinatePartial f i x*coordinatePartial g i x) ∂cube n := by
  rw [weightedOperator_inner]
  calc
    _ = ∫ y, ρ y*⟪gradient (compactTest f hf : Point n → ℝ) y,
        gradient (compactTest g hg : Point n → ℝ) y⟫_ℝ ∂cubePoint := by
      apply integral_congr_ae
      filter_upwards [testGradient_ae cubePoint (compactTest f hf),
        testGradient_ae cubePoint (compactTest g hg)] with y hy hz
      change ρ y*⟪testGradient cubePoint (compactTest f hf) y,
        testGradient cubePoint (compactTest g hg) y⟫_ℝ = _
      rw [hy,hz]
    _ = _ := by
      rw [integral_cubePoint]
      apply integral_congr_ae
      filter_upwards [cube_ae_mem n] with x hx
      rw [compactTest_gradient_on_cube f hf hx,compactTest_gradient_on_cube g hg hx,
        gradientPairing_pullback,ContinuousLinearEquiv.apply_symm_apply]

def residual (ρ : Point n →ᵇ ℝ)
    (ℓ : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)
    (b : Coordinates n → Coordinates n) (hb : ContDiff ℝ ∞ b)
    (s : Finset ((Fin n → ℤ) × Bool)) : ℝ :=
  ⟪weightedOperator cubePoint ρ
      ((optimizer ρ ℓ : gradientClosure (cubePoint (n := n)))-vector ρ ℓ s),
    gradientVector (drift b (potential ρ ℓ s).val)
      (smooth_drift (frequencySpace_properties s (potential ρ ℓ s).property).1 hb)⟫_ℝ

theorem residual_tendsto_zero (ρ : Point n →ᵇ ℝ)
    (ℓ : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ)
    {σ : Coordinates n → ℝ} {a B A D : ℝ}
    (ha : 0 < a) (hB : 0 ≤ B) (hp : ∀ y, a ≤ ρ y)
    (hρ : ContDiff ℝ 2 (fun x => ρ ((coordinateEquiv n).symm x)))
    (hpρ : Periodic (fun x => ρ ((coordinateEquiv n).symm x)))
    (hΔρ : ∀ᵐ x ∂cube n, PeriodicIntegrationByParts.laplacian
      (fun x => ρ ((coordinateEquiv n).symm x)) x ≤ B)
    (hσ : ContDiff ℝ 1 σ) (hpσ : Periodic σ)
    (hsource : ∀ (s : Finset ((Fin n → ℤ) × Bool)) (ψ : frequencySpace s),
      ℓ (trialGradient s ψ) = ∫ x, σ x*ψ.val x ∂cube n)
    {b : Coordinates n → Coordinates n} (hb : ContDiff ℝ ∞ b)
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hbA : ∀ x j, ‖b x j‖ ≤ A)
    (hbD : ∀ x i j, ‖coordinatePartial (fun y => b y j) i x‖ ≤ D) :
    Tendsto (residual ρ ℓ b hb) atTop (𝓝 0) := by
  let C := Real.sqrt (2*(n:ℝ)^2*D^2*(‖ℓ‖/a)^2+2*(n:ℝ)*A^2*regularityBound ℓ σ a B)
  have hG (s : Finset ((Fin n → ℤ) × Bool)) := potential_drift_gradient_uniform_bound
    ρ ℓ ha hB hp hρ hpρ hΔρ hσ hpσ hsource hb hA hD hbA hbD s
  have hv := vector_tendsto ρ ℓ ha (Filter.Eventually.of_forall hp)
  have he : Tendsto (fun s => ‖(optimizer ρ ℓ : gradientClosure (cubePoint (n := n)))-vector ρ ℓ s‖)
      atTop (𝓝 0) := by
    simpa only [sub_self,norm_zero] using ((tendsto_const_nhds (x :=
      (optimizer ρ ℓ : gradientClosure (cubePoint (n := n))))).sub hv).norm
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _
    (show Tendsto (fun s => (‖weightedOperator cubePoint ρ‖*
      ‖(optimizer ρ ℓ : gradientClosure (cubePoint (n := n)))-vector ρ ℓ s‖)*C)
      atTop (𝓝 0) from by simpa only [mul_zero,zero_mul] using (he.const_mul _).mul_const C)
  intro s
  exact (norm_inner_le_norm _ _).trans
    (mul_le_mul ((weightedOperator cubePoint ρ).le_opNorm _) (hG s) (norm_nonneg _) (by positivity))

theorem finite_drift_pairing_integral (ρ : Point n →ᵇ ℝ)
    (ℓ : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ) {a : ℝ}
    (ha : 0 < a) (hp : ∀ᵐ y ∂cubePoint, a ≤ ρ y)
    (hρ : ContDiff ℝ 1 (fun x => ρ ((coordinateEquiv n).symm x)))
    (hpρ : Periodic (fun x => ρ ((coordinateEquiv n).symm x)))
    {b : Coordinates n → Coordinates n} (hb : ContDiff ℝ ∞ b)
    (hpb : ∀ j, Periodic (fun x => b x j))
    (s : Finset ((Fin n → ℤ) × Bool)) :
    2*ℓ (gradientVector (drift b (potential ρ ℓ s).val)
      (smooth_drift (frequencySpace_properties s (potential ρ ℓ s).property).1 hb))+
      (∫ x, PeriodicDriftEnergy.divergence
        (fun y => ρ ((coordinateEquiv n).symm y) • b y) x*
        gradientSquare (potential ρ ℓ s).val x ∂cube n) =
      2*(∫ x, ρ ((coordinateEquiv n).symm x)*jacobianForm b (potential ρ ℓ s).val x ∂cube n)+
        2*residual ρ ℓ b hb s := by
  have hf := frequencySpace_properties s (potential ρ ℓ s).property
  let g := gradientVector (drift b (potential ρ ℓ s).val) (smooth_drift hf.1 hb)
  have hg : g ∈ periodicSpace := gradientVector_mem_periodicSpace _ _ (periodic_drift hf.2.1 hpb)
  have hu := optimizer_equation ρ ℓ ha hp ⟨g,hg⟩
  have hv := weightedOperator_gradientVector_inner ρ hf.1 (smooth_drift hf.1 hb)
  have hev : gradientVector (potential ρ ℓ s).val hf.1 = vector ρ ℓ s := gradient_potential ρ ℓ s
  rw [hev] at hv
  have hr : ℓ g = (∫ x, ρ ((coordinateEquiv n).symm x)*
      (∑ i : Fin n, coordinatePartial (potential ρ ℓ s).val i x*
        coordinatePartial (drift b (potential ρ ℓ s).val) i x) ∂cube n)+residual ρ ℓ b hb s := by
    change ℓ g = _+⟪weightedOperator cubePoint ρ
      ((optimizer ρ ℓ : gradientClosure (cubePoint (n := n)))-vector ρ ℓ s),g⟫_ℝ
    rw [map_sub,inner_sub_left,hu,hv]
    ring
  have hc := integral_drift_energy hρ hpρ hf.1 hf.2.1 hb hpb
  change 2*ℓ g+_ = _
  rw [hr]
  linarith

theorem finite_drift_pairing (ρ ρ' : Point n →ᵇ ℝ)
    (ℓ : gradientClosure (cubePoint (n := n)) →L[ℝ] ℝ) {a : ℝ}
    (ha : 0 < a) (hp : ∀ᵐ y ∂cubePoint, a ≤ ρ y)
    (hρ : ContDiff ℝ 1 (fun x => ρ ((coordinateEquiv n).symm x)))
    (hpρ : Periodic (fun x => ρ ((coordinateEquiv n).symm x)))
    {b : Coordinates n → Coordinates n} (hb : ContDiff ℝ ∞ b)
    (hpb : ∀ j, Periodic (fun x => b x j))
    (hρ' : ∀ᵐ x ∂cube n, ρ' ((coordinateEquiv n).symm x) =
      -PeriodicDriftEnergy.divergence (fun y => ρ ((coordinateEquiv n).symm y) • b y) x)
    (s : Finset ((Fin n → ℤ) × Bool)) :
    2*ℓ (gradientVector (drift b (potential ρ ℓ s).val)
      (smooth_drift (frequencySpace_properties s (potential ρ ℓ s).property).1 hb))-
      (∫ y, ρ' y*‖(vector ρ ℓ s : Lp (Point n) 2 cubePoint) y‖^2 ∂cubePoint) =
      2*(∫ x, ρ ((coordinateEquiv n).symm x)*jacobianForm b (potential ρ ℓ s).val x ∂cube n)+
        2*residual ρ ℓ b hb s := by
  have hI : (∫ y, ρ' y*‖(vector ρ ℓ s : Lp (Point n) 2 cubePoint) y‖^2 ∂cubePoint) =
      -(∫ x, PeriodicDriftEnergy.divergence
        (fun y => ρ ((coordinateEquiv n).symm y) • b y) x*gradientSquare (potential ρ ℓ s).val x ∂cube n) := by
    rw [PeriodicDiffusionEnergy.integral_vector_square]
    rw [← integral_neg]
    exact integral_congr_ae (hρ'.mono fun x hx => by dsimp only; rw [hx]; ring)
  rw [hI,sub_neg_eq_add]
  exact finite_drift_pairing_integral ρ ℓ ha hp hρ hpρ hb hpb s

end SharpWasserstein.PeriodicDriftResidual
