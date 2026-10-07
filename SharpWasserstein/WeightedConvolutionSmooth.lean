module

public import SharpWasserstein.Compat
public import SharpWasserstein.NoiseAverageSmooth
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

/-! Smooth translation integrals against integrable operator-valued weights.
The measure need not be finite and the weights need not be bounded or
continuous. Every differentiation is justified by the integrable operator norm. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal ContDiff
namespace SharpWasserstein.WeightedConvolution
open NoiseAverage
universe u v w
variable {Ω : Type w} {E F : Type u} {G : Type (max u v)} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  (μ : Measure Ω) (ξ : Ω → E)

/-- The genuine Bochner integral of a translated smooth function evaluated
by an integrable family of continuous linear maps. -/
def operatorAverage (W : Ω → F →L[ℝ] G) (f : E → F) (x : E) : G :=
  ∫ z,W z (f (x+ξ z)) ∂μ

omit [NormedSpace ℝ E] in
theorem operatorIntegrand_measurable (hξ : StronglyMeasurable ξ)
    {W : Ω → F →L[ℝ] G} (hW : AEStronglyMeasurable W μ)
    {f : E → F} (hf : Continuous f) (x : E) :
    AEStronglyMeasurable (fun z => W z (f (x+ξ z))) μ := by
  exact (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
    (hW.prodMk (hf.comp_stronglyMeasurable (stronglyMeasurable_const.add hξ)).aestronglyMeasurable)

omit [NormedSpace ℝ E] in
theorem operatorIntegrand_integrable (hξ : StronglyMeasurable ξ)
    {W : Ω → F →L[ℝ] G} (hW : Integrable W μ)
    {f : E → F} (hf : Continuous f) {C : ℝ} (hC : ∀ x,‖f x‖ ≤ C) (x : E) :
    Integrable (fun z => W z (f (x+ξ z))) μ := by
  apply Integrable.mono' (hW.norm.const_mul C)
    (operatorIntegrand_measurable μ ξ hξ hW.aestronglyMeasurable hf x)
  exact Eventually.of_forall fun z => (ContinuousLinearMap.le_opNorm _ _).trans
    (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hC (x+ξ z)) (norm_nonneg (W z)))

omit [NormedSpace ℝ E] in
theorem continuous_operatorAverage (hξ : StronglyMeasurable ξ)
    {W : Ω → F →L[ℝ] G} (hW : Integrable W μ)
    {f : E → F} (hf : Continuous f) {C : ℝ} (hC : ∀ x,‖f x‖ ≤ C) :
    Continuous (operatorAverage μ ξ W f) := by
  apply continuous_of_dominated (bound := fun z => C*‖W z‖)
  · intro x
    exact operatorIntegrand_measurable μ ξ hξ hW.aestronglyMeasurable hf x
  · intro x
    exact Eventually.of_forall fun z => (ContinuousLinearMap.le_opNorm _ _).trans
      (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hC (x+ξ z)) (norm_nonneg (W z)))
  · exact hW.norm.const_mul C
  · exact Eventually.of_forall fun z => (W z).continuous.comp
      (hf.comp (continuous_id.add continuous_const))

/-- The actual Fréchet derivative passes through the weighted integral. -/
theorem hasFDerivAt_operatorAverage (hξ : StronglyMeasurable ξ)
    {W : Ω → F →L[ℝ] G} (hW : Integrable W μ)
    {f : E → F} (hf : ContDiff ℝ 1 f) {C D : ℝ}
    (hC : ∀ x,‖f x‖ ≤ C) (hD : ∀ x,‖fderiv ℝ f x‖ ≤ D) (x : E) :
    HasFDerivAt (operatorAverage μ ξ W f)
      (∫ z,(W z).comp (fderiv ℝ f (x+ξ z)) ∂μ) x := by
  letI : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
  letI : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
  letI : NormedAddCommGroup (E →L[ℝ] G) := inferInstance
  letI : NormedSpace ℝ (E →L[ℝ] G) := inferInstance
  letI : NormedAddCommGroup (F →L[ℝ] G) := inferInstance
  letI : NormedSpace ℝ (F →L[ℝ] G) := inferInstance
  letI : NormedAddCommGroup ((E →L[ℝ] F) →L[ℝ] E →L[ℝ] G) := inferInstance
  letI : NormedSpace ℝ ((E →L[ℝ] F) →L[ℝ] E →L[ℝ] G) := inferInstance
  have hW' : Integrable (fun z => ContinuousLinearMap.compL ℝ E F G (W z)) μ := by
    exact ContinuousLinearMap.integrable_comp (𝕜 := ℝ) (𝕜' := ℝ)
      (σ := RingHom.id ℝ) (ContinuousLinearMap.compL ℝ E F G) hW
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun y z => W z (f (y+ξ z)))
    (F' := fun y z => (W z).comp (fderiv ℝ f (y+ξ z)))
    (s := univ) (bound := fun z => D*‖W z‖) (by simp)
  · exact Eventually.of_forall fun y =>
      operatorIntegrand_measurable μ ξ hξ hW.aestronglyMeasurable hf.continuous y
  · exact operatorIntegrand_integrable μ ξ hξ hW hf.continuous hC x
  · exact operatorIntegrand_measurable μ ξ hξ hW'.aestronglyMeasurable
      (hf.continuous_fderiv (by norm_num)) x
  · exact Eventually.of_forall fun z y _ => (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hD (y+ξ z)) (norm_nonneg (W z)))
  · exact hW.norm.const_mul D
  · exact Eventually.of_forall fun z y _ =>
      (W z).hasFDerivAt.comp y (by
        simpa only [Function.comp_def,id_eq,ContinuousLinearMap.comp_id] using
          ((hf.differentiable (by norm_num)) (y+ξ z)).hasFDerivAt.comp y
            ((hasFDerivAt_id y).add_const (ξ z)))

/-- Exact first-derivative identity, in a form stable under iteration. -/
theorem fderiv_operatorAverage (hξ : StronglyMeasurable ξ)
    {W : Ω → F →L[ℝ] G} (hW : Integrable W μ)
    {f : E → F} (hf : ContDiff ℝ 1 f) {C D : ℝ}
    (hC : ∀ x,‖f x‖ ≤ C) (hD : ∀ x,‖fderiv ℝ f x‖ ≤ D) :
    fderiv ℝ (operatorAverage μ ξ W f) =
      operatorAverage μ ξ (fun z => ContinuousLinearMap.compL ℝ E F G (W z)) (fderiv ℝ f) :=
  funext fun x => (hasFDerivAt_operatorAverage μ ξ hξ hW hf hC hD x).fderiv

/-- Finite-order smoothness is proved by differentiating the actual weighted
integral and retaining an integrable operator weight at each order. -/
theorem contDiff_nat_operatorAverage (hξ : StronglyMeasurable ξ) (n : ℕ)
    {W : Ω → F →L[ℝ] G} (hW : Integrable W μ)
    {f : E → F} (hf : ContDiff ℝ ∞ f) (hB : AllDerivativesBounded f) :
    ContDiff ℝ (n : ℕ) (operatorAverage μ ξ W f) := by
  induction n generalizing F G with
  | zero =>
    obtain ⟨C,_,hC⟩ := hB.bounded
    exact contDiff_zero.mpr (continuous_operatorAverage μ ξ hξ hW hf.continuous hC)
  | succ n ih =>
    obtain ⟨C,_,hC⟩ := hB.bounded
    obtain ⟨D,_,hD⟩ := hB.fderiv.bounded
    have hf₁ : ContDiff ℝ 1 f := hf.of_le (by simp)
    have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := (contDiff_infty_iff_fderiv.mp hf).2
    letI : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
    letI : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
    letI : NormedAddCommGroup (E →L[ℝ] G) := inferInstance
    letI : NormedSpace ℝ (E →L[ℝ] G) := inferInstance
    letI : NormedAddCommGroup (F →L[ℝ] G) := inferInstance
    letI : NormedSpace ℝ (F →L[ℝ] G) := inferInstance
    letI : NormedAddCommGroup ((E →L[ℝ] F) →L[ℝ] E →L[ℝ] G) := inferInstance
    letI : NormedSpace ℝ ((E →L[ℝ] F) →L[ℝ] E →L[ℝ] G) := inferInstance
    have hW' : Integrable (fun z => ContinuousLinearMap.compL ℝ E F G (W z)) μ := by
      exact ContinuousLinearMap.integrable_comp (𝕜 := ℝ) (𝕜' := ℝ)
        (σ := RingHom.id ℝ) (ContinuousLinearMap.compL ℝ E F G) hW
    have hc : ContDiff ℝ ((n : WithTop ℕ∞)+1) (operatorAverage μ ξ W f) := by
      apply contDiff_succ_iff_fderiv.mpr
      refine ⟨fun x => (hasFDerivAt_operatorAverage μ ξ hξ hW hf₁ hC hD x).differentiableAt,?_,?_⟩
      · simp
      · rw [fderiv_operatorAverage μ ξ hξ hW hf₁ hC hD]
        exact ih hW' hdf hB.fderiv
    simpa only [Nat.cast_add,Nat.cast_one] using hc

/-- Integrable operator weights preserve C∞ smoothness of kernels with all
bounded derivatives, even for an infinite underlying measure. -/
theorem contDiff_infty_operatorAverage (hξ : StronglyMeasurable ξ)
    {W : Ω → F →L[ℝ] G} (hW : Integrable W μ)
    {f : E → F} (hf : ContDiff ℝ ∞ f) (hB : AllDerivativesBounded f) :
    ContDiff ℝ ∞ (operatorAverage μ ξ W f) :=
  contDiff_infty.mpr fun n => contDiff_nat_operatorAverage μ ξ hξ n hW hf hB

end SharpWasserstein.WeightedConvolution
