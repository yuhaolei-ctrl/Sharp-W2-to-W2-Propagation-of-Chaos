import SharpWasserstein.PeriodicSourceConvolutionSpatial

/-! Uniform time remainders of genuine propagated source actions. All
constants follow from actual derivative families and initial L² energy. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal ContDiff Topology Interval
namespace SharpWasserstein.PeriodicSourceConvolution
open WeightedTangent NoiseAverage PropagatedSourceEquation FlowSemigroupDerivative
variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  {b : Configuration d N → Configuration d N} {M K M' K' : ℝ≥0}
  (hv : Continuous (Function.uncurry (fun _ : ℝ => b)))
  (hb : ∀ _ : ℝ,∀ x,‖b x‖ ≤ M) (hl : ∀ _ : ℝ,LipschitzWith K b)
  (hv' : Continuous (Function.uncurry (fun _ : ℝ => equivDrift (configurationEuclidean d N) b)))
  (hb' : ∀ _ : ℝ,∀ y,‖equivDrift (configurationEuclidean d N) b y‖ ≤ M')
  (hl' : ∀ _ : ℝ,LipschitzWith K' (equivDrift (configurationEuclidean d N) b))
  {T : ℝ} (hT : 0 ≤ T) (hbs : ContDiff ℝ ∞ b) (hB : AllDerivativesBounded b)
  (μ : Measure (Point (N*d))) [IsFiniteMeasure μ]
  {u : Point (N*d) → Point (N*d)} (hu : MemLp u 2 μ)
include hbs hB hu

/-- All source actions of a bounded derivative family share a global bound. -/
theorem uniform_action_bound {ι : Type*} {f : ι → Point (N*d) → ℝ}
    (hf : ∀ p,ContDiff ℝ ∞ (f p)) (hBf : UniformDerivatives f) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ t p,
      ‖action hv' hb' hl' hT (euclideanBrownianPathLaw d N T) μ u (f p) t‖ ≤ C := by
  obtain ⟨A,_,hA⟩ := hBf.bounded
  obtain ⟨L,hL0,hL⟩ := hBf.fderiv.bounded
  refine ⟨L*Real.exp ((K':ℝ)*T)*(∫ x,‖u x‖ ∂μ),
    mul_nonneg (mul_nonneg hL0 (Real.exp_pos _).le) (integral_nonneg fun _ => norm_nonneg _),fun t p => ?_⟩
  exact norm_action_le hv' hb' hl' hT _ μ (equivDrift_smooth _ hbs)
    (equivDrift_allDerivativesBounded _ hbs hB)
    ((hf p).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)) (hA p)
    (L := NNReal.mk L hL0) (hL p) hu t

include hv hb hl
/-- Their actual time increments have a common Lipschitz bound. -/
theorem uniform_action_increment {ι : Type*} {f : ι → Point (N*d) → ℝ}
    (hf : ∀ p,ContDiff ℝ ∞ (f p)) (hBf : UniformDerivatives f) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ s ∈ Icc 0 T,∀ t ∈ Icc 0 T,∀ p,
      ‖action hv' hb' hl' hT (euclideanBrownianPathLaw d N T) μ u (f p) s-
        action hv' hb' hl' hT (euclideanBrownianPathLaw d N T) μ u (f p) t‖ ≤ |s-t| * C := by
  obtain ⟨C,hC,hc⟩ := uniform_action_bound hv' hb' hl' hT hbs hB μ hu
    (fun p => euclideanGenerator_smooth hbs (hf p)) (uniform_euclideanGenerator hbs hB hf hBf)
  refine ⟨C,hC,fun s hs t ht p => ?_⟩
  rw [(brownian_action_equation hv hb hl hv' hb' hl' hT hbs hB μ hu (hf p) (hBf.at p) ht hs).2]
  simpa only [mul_comm] using intervalIntegral.norm_integral_le_of_norm_le_const (fun r _ => hc r p)

/-- A second actual generator equation supplies a uniform quadratic remainder. -/
theorem uniform_action_remainder {ι : Type*} {f : ι → Point (N*d) → ℝ}
    (hf : ∀ p,ContDiff ℝ ∞ (f p)) (hBf : UniformDerivatives f) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ s ∈ Icc 0 T,∀ t ∈ Icc 0 T,∀ p,
      ‖action hv' hb' hl' hT (euclideanBrownianPathLaw d N T) μ u (f p) s-
        action hv' hb' hl' hT (euclideanBrownianPathLaw d N T) μ u (f p) t-
        (s-t)*action hv' hb' hl' hT (euclideanBrownianPathLaw d N T) μ u (euclideanGenerator b (f p)) t‖ ≤
        C*|s-t|^2 := by
  obtain ⟨C,hC,hc⟩ := uniform_action_increment hv hb hl hv' hb' hl' hT hbs hB μ hu
    (fun p => euclideanGenerator_smooth hbs (hf p)) (uniform_euclideanGenerator hbs hB hf hBf)
  refine ⟨C,hC,fun s hs t ht p => ?_⟩
  have heq := brownian_action_equation hv hb hl hv' hb' hl' hT hbs hB μ hu (hf p) (hBf.at p) ht hs
  let G := action hv' hb' hl' hT (euclideanBrownianPathLaw d N T) μ u (euclideanGenerator b (f p))
  have he : action hv' hb' hl' hT (euclideanBrownianPathLaw d N T) μ u (f p) s-
      action hv' hb' hl' hT (euclideanBrownianPathLaw d N T) μ u (f p) t-(s-t)*G t =
        ∫ r in t..s,G r-G t := by
    rw [intervalIntegral.integral_sub heq.1 intervalIntegrable_const,intervalIntegral.integral_const,
      heq.2,smul_eq_mul]
  rw [he]
  have hbnd : ∀ r ∈ Ι t s,‖G r-G t‖ ≤ |s-t| * C := by
    intro r hr
    have hr' : r ∈ uIcc t s := uIoc_subset_uIcc hr
    have hrT := uIcc_subset_Icc ht hs hr'
    apply (hc r hrT t ht p).trans
    apply mul_le_mul_of_nonneg_right _ hC
    simpa only [Real.dist_eq,abs_sub_comm] using Real.dist_left_le_of_mem_uIcc hr'
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const hbnd
  calc
    _ ≤ (|s-t| * C)*|s-t| := hh
    _ = _ := by ring
end SharpWasserstein.PeriodicSourceConvolution
