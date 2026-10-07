module

public import SharpWasserstein.Compat
public import SharpWasserstein.FiniteTrialEnergyIdentity

@[expose] public section

/-! Integrated drift residual absorption for actual finite weighted trial
potentials. Coefficients involving the drift supremum multiply only the
actual L² residual error, which is controlled by the exact energy gap. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace BigOperators
namespace SharpWasserstein.FiniteGradientTrial
open WeightedTangent NoiseAverage BochnerIdentity
variable {n : ℕ} [MeasurableSpace (Point n)] [BorelSpace (Point n)]
  (μ : Measure (Point n)) [IsFiniteMeasure μ]

omit [BorelSpace (Point n)] [IsFiniteMeasure μ] in
theorem integrable_memLp_pairing {f g : Point n → Point n}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) : Integrable (fun x => ⟪f x,g x⟫_ℝ) μ := by
  apply (L2.integrable_inner (𝕜 := ℝ) (hf.toLp _) (hg.toLp _)).congr
  filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with x hx hy
  rw [hx,hy]

theorem integral_drift_residual_le {f : Point n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hBf : AllDerivativesBounded f)
    {b : Point n → Point n} (hb : ContDiff ℝ ∞ b) (hBb : AllDerivativesBounded b)
    {L M ε : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hbL : ∀ x,‖fderiv ℝ b x‖ ≤ L) (hbM : ∀ x,‖b x‖ ≤ M) (hε : 0 < ε)
    (U : Lp (Point n) 2 μ) :
    2*(∫ x,⟪U x-gradient f x,gradient (fun y => ⟪b y,gradient f y⟫_ℝ) x⟫_ℝ ∂μ) ≤
      ε*((∫ x,‖gradient f x‖^2 ∂μ)+(∫ x,HierarchyAlgebra.frobeniusSq (hessian f x) ∂μ))+
      (2*(L^2+M^2)/ε)*(∫ x,‖U x-gradient f x‖^2 ∂μ) := by
  have memG {g : Point n → ℝ} (hg : ContDiff ℝ ∞ g) (hBg : AllDerivativesBounded g) :
      MemLp (gradient g) 2 μ := by
    obtain ⟨B,_,hB⟩ := (WeightedPeriodicCoefficientEvolution.gradient_allDerivativesBounded hg hBg).bounded
    exact bounded_smooth_gradient_memLp μ g hg ⟨B,hB⟩
  have hg := memG hf hBf
  have hr := (Lp.memLp U).sub hg
  have hgs := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  have hrs := (memLp_two_iff_integrable_sq_norm hr.aestronglyMeasurable).mp hr
  have hH := hessian_square_integrable μ hf hBf
  have hD := hb.inner ℝ (smooth_gradient hf)
  have hBD : AllDerivativesBounded (fun y => ⟪b y,gradient f y⟫_ℝ) := by
    have he : (fun y => ⟪b y,gradient f y⟫_ℝ) = fun y => fderiv ℝ f y (b y) := by
      funext y
      exact inner_gradient_right
    rw [he]
    exact hBf.fderiv.clm_apply (contDiff_infty_iff_fderiv.mp hf).2 hb hBb
  have hi := integrable_memLp_pairing μ hr (memG hD hBD)
  have hbnd := integral_mono (hi.const_mul 2)
    (((hgs.add hH).const_mul ε).add (hrs.const_mul (2*(L^2+M^2)/ε)))
    (fun x => FiniteTrialDriftResidual.drift_residual_young hf
      (hb.differentiable (by simp)) hL hM hbL hbM hε x (U x-gradient f x))
  simp only [Pi.add_apply,Pi.sub_apply] at hbnd
  have hsum : Integrable (fun x => ‖gradient f x‖^2+HierarchyAlgebra.frobeniusSq (hessian f x)) μ := hgs.add hH
  have hr2 : Integrable (fun x => ‖U x-gradient f x‖^2) μ := hrs
  rw [integral_const_mul,integral_add (hsum.const_mul ε) (hr2.const_mul (2*(L^2+M^2)/ε)),
    integral_const_mul,integral_const_mul,integral_add hgs hH] at hbnd
  exact hbnd

variable {ι : Type*} [Fintype ι]
  (a : ι → Point n → ℝ) (ha : ∀ i,ContDiff ℝ ∞ (a i))
  (hB : ∀ i,∃ B : ℝ,∀ x,‖gradient (a i) x‖ ≤ B)

theorem solution_residual_integral (δ : ℝ) (hδ : 0 < δ) (U : Lp (Point n) 2 μ) :
    let T := gradientMap μ a ha hB
    let c := RegularizedTrialEnergy.solution T δ U
    (∫ x,‖U x-gradient (potential a c) x‖^2 ∂μ) =
      ‖U‖^2-RegularizedTrialEnergy.energy T δ U-δ*‖c‖^2 := by
  dsimp only
  have h := RegularizedTrialEnergy.energy_gap (gradientMap μ a ha hB) δ hδ U
  have he : ‖U-gradientMap μ a ha hB (RegularizedTrialEnergy.solution (gradientMap μ a ha hB) δ U)‖^2 =
      ∫ x,‖U x-gradient (potential a (RegularizedTrialEnergy.solution (gradientMap μ a ha hB) δ U)) x‖^2 ∂μ := by
    rw [lp_norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub U (gradientMap μ a ha hB _),gradientMap_ae μ a ha hB
      (RegularizedTrialEnergy.solution (gradientMap μ a ha hB) δ U)] with x hx hy
    rw [hx,Pi.sub_apply,hy]
  rw [he] at h
  linarith

theorem solution_residual_integral_le (δ : ℝ) (hδ : 0 < δ) (U : Lp (Point n) 2 μ) :
    let T := gradientMap μ a ha hB
    let c := RegularizedTrialEnergy.solution T δ U
    (∫ x,‖U x-gradient (potential a c) x‖^2 ∂μ) ≤
      ‖U‖^2-RegularizedTrialEnergy.energy T δ U := by
  dsimp only
  rw [solution_residual_integral μ a ha hB δ hδ U]
  exact sub_le_self _ (mul_nonneg hδ.le (sq_nonneg _))

end SharpWasserstein.FiniteGradientTrial
