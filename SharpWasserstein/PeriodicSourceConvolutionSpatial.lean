import SharpWasserstein.PeriodicSourceConvolutionUniform

/-! Joint regularity of the actual translated kernel generator families and
spatial continuity of their genuine propagated source actions. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal ContDiff Topology Interval
namespace SharpWasserstein.PeriodicSourceConvolution
open WeightedTangent NoiseAverage PropagatedSourceEquation FlowSemigroupDerivative
open PeriodicIntegrationByParts PeriodicPositiveKernel PeriodicBochner
variable {P E F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Parameter-dependent Fréchet derivatives are genuinely jointly smooth. -/
theorem joint_fderiv {f : P → E → F} (hf : ContDiff ℝ ∞ (Function.uncurry f)) :
    ContDiff ℝ ∞ (Function.uncurry (fun p => fderiv ℝ (f p))) := by
  have hh : ContDiff ℝ ∞ (fun q : (P × E) × E => f q.1.1 q.2) :=
    hf.comp (contDiff_fst.fst.prodMk contDiff_snd)
  exact hh.fderiv contDiff_snd (by simp)

variable {d N : ℕ}

theorem joint_coordinateDerivative {f : P → Configuration d N → ℝ}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) (i : Fin N) (a : Fin d) :
    ContDiff ℝ ∞ (Function.uncurry (fun p => coordinateDerivative (f p) i a)) :=
  (joint_fderiv hf).clm_apply contDiff_const

theorem joint_generator {f : P → Configuration d N → ℝ}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) {b : Configuration d N → Configuration d N}
    (hb : ContDiff ℝ ∞ b) : ContDiff ℝ ∞ (Function.uncurry (fun p => generator b (f p))) := by
  have hLap : ContDiff ℝ ∞ (Function.uncurry (fun p => SharpWasserstein.laplacian (f p))) := by
    change ContDiff ℝ ∞ (fun q : P × Configuration d N => ∑ i : Fin N,∑ a : Fin d,
      coordinateDerivative (coordinateDerivative (f q.1) i a) i a q.2)
    exact ContDiff.sum fun i _ => ContDiff.sum fun a _ =>
      joint_coordinateDerivative (joint_coordinateDerivative hf i a) i a
  have he : Function.uncurry (fun p => generator b (f p)) =
      fun q : P × Configuration d N => laplacian (f q.1) q.2+fderiv ℝ (f q.1) q.2 (b q.2) := by
    funext q
    exact generator_eq_laplacian_add_fderiv _ _ _
  rw [he]
  exact hLap.add ((joint_fderiv hf).clm_apply (hb.comp contDiff_snd))

theorem joint_euclideanGenerator {f : P → Point (N*d) → ℝ}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) {b : Configuration d N → Configuration d N}
    (hb : ContDiff ℝ ∞ b) :
    ContDiff ℝ ∞ (Function.uncurry (fun p => euclideanGenerator b (f p))) := by
  have hp : ContDiff ℝ ∞ (Function.uncurry (fun (p : P) (x : Configuration d N) =>
      f p (configurationEuclidean d N x))) := by
    convert hf.comp (contDiff_fst.prodMk
      ((configurationEuclidean d N).contDiff.comp contDiff_snd)) using 1; rfl
  have hg := joint_generator hp hb
  convert hg.comp (contDiff_fst.prodMk
    ((configurationEuclidean d N).symm.contDiff.comp contDiff_snd)) using 1; rfl

theorem joint_euclideanKernelTest {n : ℕ} (κ : ℝ) :
    ContDiff ℝ ∞ (Function.uncurry (euclideanKernelTest (n := n) κ)) :=
  (kernel_smooth n κ).comp (contDiff_fst.sub ((coordinateEquiv n).contDiff.comp contDiff_snd))

section Action
variable [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {b : E → E} {M K : ℝ≥0}
  (hv : Continuous (Function.uncurry (fun _ : ℝ => b)))
  (hb : ∀ _ : ℝ,∀ x,‖b x‖ ≤ M) (hl : ∀ _ : ℝ,LipschitzWith K b)
  {T : ℝ} [MeasurableSpace C(Icc 0 T,E)] [BorelSpace C(Icc 0 T,E)] (hT : 0 ≤ T)
  (ξ : Measure C(Icc 0 T,E)) [IsProbabilityMeasure ξ]
  (μ : Measure E) [IsFiniteMeasure μ]
  (hbs : ContDiff ℝ ∞ b) (hB : AllDerivativesBounded b)

include hbs hB in
/-- Uniformly bounded genuine test differentials may be integrated against
the actual JV flux continuously in their spatial parameter. -/
theorem action_continuous_param {f : P → E → ℝ}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) (hBf : UniformDerivatives f)
    {u : E → E} (hu : MemLp u 2 μ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Continuous (fun p => action hv hb hl hT ξ μ u (f p) t) := by
  have hf' (p : P) : ContDiff ℝ ∞ (f p) := hf.comp (contDiff_const.prodMk contDiff_id)
  obtain ⟨C,_,hC⟩ := hBf.bounded
  obtain ⟨L,hL0,hL⟩ := hBf.fderiv.bounded
  let V := fun q : E × C(Icc 0 T,E) =>
    fderiv ℝ (fun y => BoundedFlow.flow hv hb hl hT y q.2 t) q.1 (u q.1)
  have hV : MemLp V 2 (μ.prod ξ) := FlowInitialDerivative.boundedFlow_fderiv_apply_memLp
    hv hb hl hbs hB hT ht (μ.prod ξ)
      (hu.comp_measurePreserving (measurePreserving_fst (μ := μ) (ν := ξ)))
  have he (p : P) : action hv hb hl hT ξ μ u (f p) t =
      ∫ q : E × C(Icc 0 T,E),fderiv ℝ (f p) (BoundedFlow.flow hv hb hl hT q.1 q.2 t) (V q) ∂μ.prod ξ :=
    action_eq_randomFlux hv hb hl hT ξ μ hbs hB
      ((hf' p).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)) (hC p)
      (L := NNReal.mk L hL0) (hL p) hu ht
  simp_rw [he]
  apply continuous_of_dominated (bound := fun q => L*‖V q‖)
  · intro p
    exact (integrable_differential_pairing hv hb hl hT ξ ht hbs hB μ
      ((hf' p).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1))
      (L := NNReal.mk L hL0) (hL p) hu).1
  · intro p
    exact Eventually.of_forall fun q => (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hL p _) (norm_nonneg _))
  · exact (hV.integrable (by norm_num)).norm.const_mul L
  · exact Eventually.of_forall fun q =>
      (((joint_fderiv hf).continuous.comp (continuous_id.prodMk continuous_const)).clm_apply continuous_const)
end Action
end SharpWasserstein.PeriodicSourceConvolution
