module

public import SharpWasserstein.Compat
public import SharpWasserstein.BrownianForwardDerivative
public import SharpWasserstein.FrozenGaussianLaw

@[expose] public section

/-! Exact identification of the constructed constant-drift Brownian flow with
the concrete Gaussian transition law. This transfers actual weak-evolution
identities to bounded smooth Gaussian tests, without a compact-support
assumption or a postulated Gaussian generator formula. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal Interval ContDiff
namespace SharpWasserstein
namespace BrownianNoise

/-- The full flattened Brownian position has the actual independent Gaussian
vector law with covariance `2t I`. -/
theorem configurationLaw_eval_flat_hasLaw {d N : ℕ} {T : ℝ} (t : Icc 0 T) :
    HasLaw (fun w : C(Icc 0 T,Configuration d N) => configurationFlatten d N (w t))
      (gaussianVectorLaw (0 : Position (N*d)) (2*NNReal.mk t t.property.1))
      (configurationLaw d N T) := by
  let v : ℝ≥0 := 2*NNReal.mk t t.property.1
  have hc : MeasurePreserving (fun w : Fin d → C(Icc 0 T,ℝ) => fun a => w a t)
      (coordinateLaw d T) (gaussianVectorLaw (0 : Position d) v) :=
    measurePreserving_pi (fun _ : Fin d => scalarLaw T) (fun _ => gaussianReal 0 v)
      (fun _ => (scalarLaw_hasLaw t).measurePreserving (continuous_eval_const t).measurable)
  have hp := measurePreserving_pi (fun _ : Fin N => coordinateLaw d T)
    (fun _ => gaussianVectorLaw (0 : Position d) v) (fun _ => hc)
  have hflat := (configurationFlatten_gaussian (d := d) (N := N) v).comp hp
  have hm : Measurable (fun w : C(Icc 0 T,Configuration d N) => configurationFlatten d N (w t)) :=
    (configurationFlatten d N).measurable.comp (continuous_eval_const t).measurable
  refine ⟨hm.aemeasurable, ?_⟩
  rw [configurationLaw,Measure.map_map hm configurationPath_measurable]
  exact hflat.map_eq

end BrownianNoise

theorem gaussianVectorLaw_add_mean {m : ℕ} (a : Position m) (v : ℝ≥0) :
    MeasurePreserving (fun z : Position m => a+z)
      (gaussianVectorLaw (0 : Position m) v) (gaussianVectorLaw a v) := by
  apply measurePreserving_pi (fun _ : Fin m => gaussianReal 0 v) (fun i => gaussianReal (a i) v)
  intro i
  have hid : HasLaw (id : ℝ → ℝ) (gaussianReal 0 v) (gaussianReal 0 v) :=
    (MeasurePreserving.id _).hasLaw
  have h := gaussianReal_const_add hid (a i)
  convert h.measurePreserving (by fun_prop) using 1 <;>
    first | rfl | simp only [zero_add]

namespace BoundedFlow

theorem flow_constant {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (u : E) {M K : ℝ≥0}
    (hv : Continuous (Function.uncurry (fun (_ : ℝ) (_ : E) => u)))
    (hb : ∀ (_ : ℝ) (_ : E), ‖u‖ ≤ M) (hl : ∀ _ : ℝ,LipschitzWith K (fun _ : E => u))
    {T : ℝ} (hT : 0 ≤ T) (x : E) (w : C(Icc 0 T,E)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    flow hv hb hl hT x w t = x+t•u+w ⟨t,ht⟩ := by
  have he := (flow_trajectory hv hb hl hT x w).equation t ht
  simpa only [intervalIntegral.integral_const,sub_zero,noiseExtension,projIcc_of_mem _ ht] using he

end BoundedFlow
namespace BrownianFlow

/-- The actual constant-drift flow started at a point is precisely the
Gaussian transition law, including the degenerate time-zero law. -/
theorem law_constant_dirac {d N : ℕ} (x u : Configuration d N) {M K : ℝ≥0}
    (hv : Continuous (Function.uncurry (fun (_ : ℝ) (_ : Configuration d N) => u)))
    (hb : ∀ (_ : ℝ) (_ : Configuration d N), ‖u‖ ≤ M)
    (hl : ∀ _ : ℝ,LipschitzWith K (fun _ : Configuration d N => u))
    {T : ℝ} (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    law hv hb hl hT (Measure.dirac x) t = FrozenGaussian.transitionLaw x u (NNReal.mk t ht.1) := by
  let a := configurationFlatten d N (x+t•u)
  have hpos := BrownianNoise.configurationLaw_eval_flat_hasLaw (d := d) (N := N) (⟨t,ht⟩ : Icc 0 T)
  have hshift := (gaussianVectorLaw_add_mean a (2*NNReal.mk t ht.1)).hasLaw.comp hpos
  have hunflat : MeasurePreserving (configurationFlatten d N).symm
      (gaussianVectorLaw a (2*NNReal.mk t ht.1)) (FrozenGaussian.transitionLaw x u (NNReal.mk t ht.1)) :=
    ⟨(configurationFlatten d N).symm.measurable,rfl⟩
  have hfinal := hunflat.hasLaw.comp hshift
  rw [law,Measure.dirac_prod,Measure.map_map
    (BoundedFlow.flow_continuous hv hb hl hT ht).measurable measurable_prodMk_left]
  rw [← hfinal.map_eq]
  congr 1
  funext w
  dsimp only [Function.comp_def]
  rw [BoundedFlow.flow_constant u hv hb hl hT x w ht]
  apply (configurationFlatten d N).injective
  rw [MeasurableEquiv.apply_symm_apply,configurationFlatten_add]

theorem globalLaw_constant_dirac {d N : ℕ} (x u : Configuration d N) {M K : ℝ≥0}
    (hv : Continuous (Function.uncurry (fun (_ : ℝ) (_ : Configuration d N) => u)))
    (hb : ∀ (_ : ℝ) (_ : Configuration d N), ‖u‖ ≤ M)
    (hl : ∀ _ : ℝ,LipschitzWith K (fun _ : Configuration d N => u))
    {t : ℝ} (ht : 0 ≤ t) :
    globalLaw hv hb hl (Measure.dirac x) t = FrozenGaussian.transitionLaw x u (NNReal.mk t ht) := by
  rw [globalLaw_eq hv hb hl ht (Measure.dirac x) ⟨ht,le_rfl⟩]
  exact law_constant_dirac x u hv hb hl ht ⟨ht,le_rfl⟩

end BrownianFlow

namespace FrozenGaussian
open WeightedTangent
variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]

/-- The genuine frozen-Gaussian generator identity holds for bounded smooth
Euclidean tests with bounded gradient and Laplacian. It follows from the
constructed Brownian weak evolution and its proved Gaussian law. -/
theorem timeExpectation_sub_eq_integral_bounded_smooth
    (f : Point (N*d) → ℝ) (hf : ContDiff ℝ ∞ f) {A B D : ℝ}
    (hfa : ∀ z,|f z| ≤ A) (hfb : ∀ z,‖gradient f z‖ ≤ B)
    (hfd : ∀ z,|PDEPairings.laplacian f z| ≤ D)
    (x u : Configuration d N) {t : ℝ} (ht : 0 ≤ t) :
    timeExpectation (f ∘ configurationEuclidean d N) x u t - f (configurationEuclidean d N x) =
      ∫ s in (0 : ℝ)..t,timeExpectation (generator (fun _ => u) (f ∘ configurationEuclidean d N)) x u s := by
  let hv : Continuous (Function.uncurry (fun (_ : ℝ) (_ : Configuration d N) => u)) := continuous_const
  let hb : ∀ (_ : ℝ) (_ : Configuration d N), ‖u‖ ≤ (‖u‖₊ : ℝ) := fun _ _ => le_rfl
  let hl : ∀ _ : ℝ,LipschitzWith 0 (fun _ : Configuration d N => u) := fun _ => LipschitzWith.const u
  let P := BrownianFlow.globalLaw hv hb hl (Measure.dirac x)
  have hμ : HasSecondMoment (Measure.dirac x) := by
    simp only [HasSecondMoment,lintegral_dirac]
    exact ENNReal.ofReal_lt_top
  have hP := BrownianFlow.globalLaw_weakEvolution hv hb hl (Measure.dirac x) hμ
  have heq := (WeakEvolution.equation_bounded_smooth hP
    (fun _ _ => measurable_const) (fun _ _ _ => le_refl ‖configurationEuclidean d N u‖)
    f hf hfa hfb hfd t ht).2
  have hfc : Continuous (f ∘ configurationEuclidean d N) :=
    hf.continuous.comp (configurationEuclidean d N).continuous
  have hgc : Continuous (generator (fun _ => u) (f ∘ configurationEuclidean d N)) := by
    have he : generator (fun _ => u) (f ∘ configurationEuclidean d N) =
        fun z => BoundedWeakTests.generator f (configurationEuclidean d N z) (configurationEuclidean d N u) :=
      funext (generator_pullback f (fun _ => u))
    rw [he]
    unfold BoundedWeakTests.generator
    exact ((BochnerIdentity.smooth_laplacian hf).continuous.comp
      (configurationEuclidean d N).continuous).add
      (continuous_const.inner ((BochnerIdentity.smooth_gradient hf).continuous.comp
        (configurationEuclidean d N).continuous))
  have hint (g : Configuration d N → ℝ) (hg : Continuous g) {s : ℝ} (hs : 0 ≤ s) :
      (∫ z,g z ∂P s) = timeExpectation g x u s := by
    change (∫ z,g z ∂BrownianFlow.globalLaw hv hb hl (Measure.dirac x) s) = _
    rw [BrownianFlow.globalLaw_constant_dirac x u hv hb hl hs,integral_transitionLaw hg]
    rfl
  have heq' : (∫ z,(f ∘ configurationEuclidean d N) z ∂P t)-f (configurationEuclidean d N x) =
      ∫ s in (0 : ℝ)..t,∫ z,generator (fun _ => u) (f ∘ configurationEuclidean d N) z ∂P s := by
    simpa only [P,BrownianFlow.globalLaw_initial,integral_dirac,Function.comp_def] using heq
  rw [hint _ hfc ht] at heq'
  rw [heq']
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht] at hs
  exact hint _ hgc hs.1

end FrozenGaussian

end SharpWasserstein
