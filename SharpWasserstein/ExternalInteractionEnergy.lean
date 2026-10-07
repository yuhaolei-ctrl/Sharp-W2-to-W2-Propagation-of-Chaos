module

public import SharpWasserstein.Compat
public import SharpWasserstein.ExternalInteractionGradientCancellation
public import SharpWasserstein.PointwiseTrajectory

@[expose] public section

/-! Actual joint-law external energy estimates. The measure can be any weighted
law, including a density against periodic volume. The fluctuation is the literal
difference of fields; its identification with an energy increment is separate. -/
noncomputable section
namespace SharpWasserstein.ExternalInteraction
open MeasureTheory WeightedTangent WeightedMarginal BochnerIdentity PDEPairings Filter
open scoped BigOperators InnerProductSpace ContDiff
variable {d m : ℕ} [MeasurableSpace (Point (m*d+d))] [BorelSpace (Point (m*d+d))]

/-- The bound depends only on spatial dimension and the original kernel constants. -/
def gradientConstant (d : ℕ) (M L₁ L₂ : ℝ) : ℝ :=
  4*(d:ℝ)*(L₁^2+L₂^2)+2*(d:ℝ)*M^2

theorem gradientConstant_nonneg (d : ℕ) (M L₁ L₂ : ℝ) : 0 ≤ gradientConstant d M L₁ L₂ := by
  unfold gradientConstant
  positivity

section Energy
variable (μ : Measure (Point (m*d+d)))
  {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
  (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
  (hm : 1 ≤ m) (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
  {f : Point (m*d) → ℝ} (hf : ContDiff ℝ ∞ f)
  (hG : MemLp (fun z => gradient f (prefixProjection (m*d) d z)) 2 μ)
  (hH : Integrable (fun z => HierarchyAlgebra.frobeniusSq (hessian f (prefixProjection (m*d) d z))) μ)
include hb hbound hm hM hL₁ hL₂ hf hG hH

/-- The genuine external-test gradient is square-integrable as a consequence of
the proved pointwise bound and the actual marginal energy and Hessian action. -/
theorem interaction_gradient_memLp : MemLp (gradient (interaction b f)) 2 μ := by
  have hg := (memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).mp hG
  have hi := (hg.add hH).const_mul (gradientConstant d M L₁ L₂*(m:ℝ))
  have hmG := (smooth_gradient (interaction_smooth hb hf)).continuous.aestronglyMeasurable (μ := μ)
  apply (memLp_two_iff_integrable_sq_norm hmG).mpr
  apply hi.mono' (hmG.norm.pow 2)
  filter_upwards [] with z
  simp only [Pi.pow_apply,Pi.add_apply] at *
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact interaction_gradient_norm_sq_le_combined hb hbound hm hM hL₁ hL₂ hf z

/-- Integrating the actual sharp gradient estimate introduces no additional
particle factor. -/
theorem integral_interaction_gradient_sq_le :
    (∫ z, ‖gradient (interaction b f) z‖^2 ∂μ) ≤
      gradientConstant d M L₁ L₂*(m:ℝ)*
        ((∫ z, ‖gradient f (prefixProjection (m*d) d z)‖^2 ∂μ)+
          ∫ z, HierarchyAlgebra.frobeniusSq (hessian f (prefixProjection (m*d) d z)) ∂μ) := by
  have hg := (memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).mp hG
  have hΦ := interaction_gradient_memLp μ hb hbound hm hM hL₁ hL₂ hf hG hH
  have hi := (memLp_two_iff_integrable_sq_norm hΦ.aestronglyMeasurable).mp hΦ
  have hh := integral_mono hi ((hg.add hH).const_mul (gradientConstant d M L₁ L₂*(m:ℝ)))
    (interaction_gradient_norm_sq_le_combined hb hbound hm hM hL₁ hL₂ hf)
  simpa only [Pi.add_apply,integral_const_mul,integral_add hg hH] using hh

/-- Cauchy--Schwarz for an arbitrary actual joint flux, with the explicit
sharp gradient constant and literal field energies. -/
theorem integral_pairing_abs_le {V : Point (m*d+d) → Point (m*d+d)} (hV : MemLp V 2 μ) :
    |∫ z, ⟪V z,gradient (interaction b f) z⟫_ℝ ∂μ| ≤
      Real.sqrt (∫ z, ‖V z‖^2 ∂μ)*
        Real.sqrt (gradientConstant d M L₁ L₂*(m:ℝ)*
          ((∫ z, ‖gradient f (prefixProjection (m*d) d z)‖^2 ∂μ)+
            ∫ z, HierarchyAlgebra.frobeniusSq (hessian f (prefixProjection (m*d) d z)) ∂μ)) := by
  have hΦ := interaction_gradient_memLp μ hb hbound hm hM hL₁ hL₂ hf hG hH
  have hc := (norm_integral_le_integral_norm (fun z => ⟪V z,gradient (interaction b f) z⟫_ℝ)).trans
    (PointwiseTrajectory.integral_norm_inner_le hV hΦ)
  rw [Real.norm_eq_abs,PointwiseTrajectory.norm_toLp_two_eq_sqrt hV,
    PointwiseTrajectory.norm_toLp_two_eq_sqrt hΦ] at hc
  exact hc.trans (mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (integral_interaction_gradient_sq_le μ hb hbound hm hM hL₁ hL₂ hf hG hH))
    (Real.sqrt_nonneg _))

/-- The square form of the actual joint-flux pairing estimate. -/
theorem integral_pairing_sq_le {V : Point (m*d+d) → Point (m*d+d)} (hV : MemLp V 2 μ) :
    (∫ z, ⟪V z,gradient (interaction b f) z⟫_ℝ ∂μ)^2 ≤
      gradientConstant d M L₁ L₂*(m:ℝ)*(∫ z, ‖V z‖^2 ∂μ)*
        ((∫ z, ‖gradient f (prefixProjection (m*d) d z)‖^2 ∂μ)+
          ∫ z, HierarchyAlgebra.frobeniusSq (hessian f (prefixProjection (m*d) d z)) ∂μ) := by
  have hh := integral_pairing_abs_le μ hb hbound hm hM hL₁ hL₂ hf hG hH hV
  have hV₀ : 0 ≤ ∫ z, ‖V z‖^2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  have hG₀ : 0 ≤ ∫ z, ‖gradient f (prefixProjection (m*d) d z)‖^2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  have hH₀ : 0 ≤ ∫ z, HierarchyAlgebra.frobeniusSq (hessian f (prefixProjection (m*d) d z)) ∂μ :=
    integral_nonneg (fun _ => HierarchyAlgebra.frobeniusSq_nonneg _)
  have hC := gradientConstant_nonneg d M L₁ L₂
  have hs := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hh
  rw [sq_abs,mul_pow,Real.sq_sqrt hV₀,Real.sq_sqrt (by positivity)] at hs
  nlinarith

end Energy

/-- The actual lifted marginal gradient in the full Euclidean coordinates. -/
def liftedGradient (f : Point (m*d) → ℝ) (z : Point (m*d+d)) : Point (m*d+d) :=
  prefixEmbedding (m*d) d (gradient f (prefixProjection (m*d) d z))

/-- The literal fluctuation between the full tangent and the lifted marginal tangent. -/
def fluctuation (f : Point (m*d) → ℝ) (U : Point (m*d+d) → Point (m*d+d))
    (z : Point (m*d+d)) : Point (m*d+d) := U z-liftedGradient f z

omit [BorelSpace (Point (m*d+d))] in
/-- Both terms in the fluctuation are actual square-integrable fields. -/
theorem fluctuation_memLp (μ : Measure (Point (m*d+d)))
    {f : Point (m*d) → ℝ} {U : Point (m*d+d) → Point (m*d+d)}
    (hG : MemLp (fun z => gradient f (prefixProjection (m*d) d z)) 2 μ) (hU : MemLp U 2 μ) :
    MemLp (fluctuation f U) 2 μ :=
  hU.sub ((prefixEmbedding (m*d) d).toContinuousLinearMap.comp_memLp' hG)

/-- Square-integrable genuine field differences satisfy the sharp cross bound;
no orthogonality or energy-increment identity is assumed here. -/
theorem fluctuation_pairing_sq_le (μ : Measure (Point (m*d+d)))
    {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
    (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
    (hm : 1 ≤ m) (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    {f : Point (m*d) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hG : MemLp (fun z => gradient f (prefixProjection (m*d) d z)) 2 μ)
    (hH : Integrable (fun z => HierarchyAlgebra.frobeniusSq (hessian f (prefixProjection (m*d) d z))) μ)
    {U : Point (m*d+d) → Point (m*d+d)} (hU : MemLp U 2 μ) :
    (∫ z, ⟪U z-prefixEmbedding (m*d) d (gradient f (prefixProjection (m*d) d z)),
      gradient (interaction b f) z⟫_ℝ ∂μ)^2 ≤
      gradientConstant d M L₁ L₂*(m:ℝ)*
        (∫ z, ‖U z-prefixEmbedding (m*d) d (gradient f (prefixProjection (m*d) d z))‖^2 ∂μ)*
        ((∫ z, ‖gradient f (prefixProjection (m*d) d z)‖^2 ∂μ)+
          ∫ z, HierarchyAlgebra.frobeniusSq (hessian f (prefixProjection (m*d) d z)) ∂μ) :=
  integral_pairing_sq_le μ hb hbound hm hM hL₁ hL₂ hf hG hH (fluctuation_memLp μ hG hU)

/-- Young absorption derived from a genuine square bound, including zero energies. -/
theorem young_of_sq_le {q A B ε : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hε : 0 < ε)
    (hq : q^2 ≤ A*B) : 2*|q| ≤ ε*B+A/ε := by
  have hsA := Real.sq_sqrt hA
  have hsB := Real.sq_sqrt hB
  have hab : |q| ≤ Real.sqrt A*Real.sqrt B := by
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
    rw [sq_abs,mul_pow,hsA,hsB]
    exact hq
  have he : ε*B+A/ε = (ε^2*B+A)/ε := by field_simp
  rw [he]
  apply (le_div_iff₀ hε).mpr
  have hmul := mul_le_mul_of_nonneg_left hab (show 0 ≤ 2*ε by positivity)
  nlinarith [sq_nonneg (ε*Real.sqrt B-Real.sqrt A)]

/-- The fluctuation term can absorb an arbitrarily small fraction of the
actual Hessian action; the remaining coefficient is linear in `m`. -/
theorem fluctuation_pairing_young (μ : Measure (Point (m*d+d)))
    {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
    (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
    (hm : 1 ≤ m) (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    {f : Point (m*d) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hG : MemLp (fun z => gradient f (prefixProjection (m*d) d z)) 2 μ)
    (hH : Integrable (fun z => HierarchyAlgebra.frobeniusSq (hessian f (prefixProjection (m*d) d z))) μ)
    {U : Point (m*d+d) → Point (m*d+d)} (hU : MemLp U 2 μ) {ε : ℝ} (hε : 0 < ε) :
    2*|∫ z, ⟪U z-prefixEmbedding (m*d) d (gradient f (prefixProjection (m*d) d z)),
      gradient (interaction b f) z⟫_ℝ ∂μ| ≤
      ε*((∫ z, ‖gradient f (prefixProjection (m*d) d z)‖^2 ∂μ)+
          ∫ z, HierarchyAlgebra.frobeniusSq (hessian f (prefixProjection (m*d) d z)) ∂μ)+
        (gradientConstant d M L₁ L₂*(m:ℝ)/ε)*
          (∫ z, ‖U z-prefixEmbedding (m*d) d (gradient f (prefixProjection (m*d) d z))‖^2 ∂μ) := by
  have hC := gradientConstant_nonneg d M L₁ L₂
  have hV₀ : 0 ≤ ∫ z, ‖U z-prefixEmbedding (m*d) d (gradient f (prefixProjection (m*d) d z))‖^2 ∂μ :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hG₀ : 0 ≤ ∫ z, ‖gradient f (prefixProjection (m*d) d z)‖^2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  have hH₀ : 0 ≤ ∫ z, HierarchyAlgebra.frobeniusSq (hessian f (prefixProjection (m*d) d z)) ∂μ :=
    integral_nonneg (fun _ => HierarchyAlgebra.frobeniusSq_nonneg _)
  have hh := young_of_sq_le (by positivity) (add_nonneg hG₀ hH₀) hε
    (fluctuation_pairing_sq_le μ hb hbound hm hM hL₁ hL₂ hf hG hH hU)
  convert hh using 1
  ring

end SharpWasserstein.ExternalInteraction
