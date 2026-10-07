module

public import SharpWasserstein.Compat
public import SharpWasserstein.RoughEulerianCompressionGeometry
public import SharpWasserstein.RoughEulerianCompressionPushforward
public import Mathlib.Probability.Kernel.Composition.Lemmas

@[expose] public section

/-! Actual spatial compression of a joint L² vector flux. The Jacobian field is
pushed under (t,x)↦(t,θ_R x) by the proved full-L² Riesz construction. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped InnerProductSpace Topology ENNReal ProbabilityTheory ContDiff
namespace SharpWasserstein.RoughEulerianCompression
open WeightedTangent
variable {α : Type*} [MeasurableSpace α] {d : ℕ}
  [MeasurableSpace (Point d)] [BorelSpace (Point d)]
  (ρ : Measure (α × Point d))

/-- Spatial compression preserves the time label exactly. -/
def compressionMap (R : ℝ) (z : α × Point d) : α × Point d := (z.1,compression R z.2)

theorem compressionMap_measurable (R : ℝ) : Measurable (compressionMap (α := α) (d := d) R) :=
  measurable_fst.prodMk ((compression_contDiff R).continuous.measurable.comp measurable_snd)

/-- The literal compressed velocity before averaging over fibers. -/
def compressionVector (R : ℝ) (U : Lp (Point d) 2 ρ) (z : α × Point d) : Point d :=
  fderiv ℝ (compression R) z.2 (U z)

theorem compressionVector_memLp {R : ℝ} (hR : R ≠ 0) (U : Lp (Point d) 2 ρ) :
    MemLp (compressionVector ρ R U) 2 ρ := by
  apply (Lp.memLp U).of_le ?_ (Eventually.of_forall fun z => compression_fderiv_apply_norm_le hR z.2 (U z))
  have hd : AEStronglyMeasurable (fun z : α × Point d => fderiv ℝ (compression R) z.2) ρ :=
    (((compression_contDiff R).continuous_fderiv (by simp)).stronglyMeasurable.comp_measurable measurable_snd).aestronglyMeasurable
  exact (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
    (hd.prodMk (Lp.aestronglyMeasurable U))

def compressionVectorLp {R : ℝ} (hR : R ≠ 0) (U : Lp (Point d) 2 ρ) : Lp (Point d) 2 ρ :=
  (compressionVector_memLp ρ hR U).toLp (compressionVector ρ R U)

theorem compressionVectorLp_ae {R : ℝ} (hR : R ≠ 0) (U : Lp (Point d) 2 ρ) :
    compressionVectorLp ρ hR U =ᵐ[ρ] compressionVector ρ R U :=
  (compressionVector_memLp ρ hR U).coeFn_toLp

/-- The actual output flux, with joint measurability built into the L² representative. -/
def compressedFlux {R : ℝ} (hR : R ≠ 0) (U : Lp (Point d) 2 ρ) :
    Lp (Point d) 2 (ρ.map (compressionMap R)) :=
  pushedFlux ρ (compressionMap R) (compressionMap_measurable R) (compressionVectorLp ρ hR U)

theorem compressedFlux_stronglyMeasurable {R : ℝ} (hR : R ≠ 0) (U : Lp (Point d) 2 ρ) :
    StronglyMeasurable (fun z => compressedFlux ρ hR U z) := Lp.stronglyMeasurable _

/-- Spatial compression and fiber averaging together preserve the exact action bound. -/
theorem compressedFlux_energy_le {R : ℝ} (hR : R ≠ 0) (U : Lp (Point d) 2 ρ) :
    (∫ z,‖compressedFlux ρ hR U z‖^2 ∂ρ.map (compressionMap R)) ≤ ∫ z,‖U z‖^2 ∂ρ := by
  apply (pushedFlux_energy_le ρ (compressionMap R) (compressionMap_measurable R)
    (compressionVectorLp ρ hR U)).trans
  have hiV := (memLp_two_iff_integrable_sq_norm (Lp.memLp (compressionVectorLp ρ hR U)).aestronglyMeasurable).mp
    (Lp.memLp (compressionVectorLp ρ hR U))
  have hiU := (memLp_two_iff_integrable_sq_norm (Lp.memLp U).aestronglyMeasurable).mp (Lp.memLp U)
  apply integral_mono_ae hiV hiU
  filter_upwards [compressionVectorLp_ae ρ hR U] with z hz
  rw [hz]
  exact pow_le_pow_left₀ (norm_nonneg _) (compression_fderiv_apply_norm_le hR z.2 (U z)) 2

/-- Exact pushed vector-flux pairing, with the actual compression Jacobian. -/
theorem compressedFlux_pairing {R : ℝ} (hR : R ≠ 0) (U : Lp (Point d) 2 ρ)
    (G : α × Point d → Point d) (hG : MemLp G 2 (ρ.map (compressionMap R))) :
    (∫ z,⟪G z,compressedFlux ρ hR U z⟫_ℝ ∂ρ.map (compressionMap R)) =
      ∫ z,⟪G (z.1,compression R z.2),fderiv ℝ (compression R) z.2 (U z)⟫_ℝ ∂ρ := by
  rw [compressedFlux,pushedFlux_pairing ρ (compressionMap R) (compressionMap_measurable R)
    (compressionVectorLp ρ hR U) G hG]
  apply integral_congr_ae
  filter_upwards [compressionVectorLp_ae ρ hR U] with z hz
  rw [hz]
  rfl

/-- The carrying measure really is the joint measure of the compressed probability kernel. -/
theorem compressionMap_compProd (ν : Measure α) [SFinite ν]
    (κ : Kernel α (Point d)) [IsSFiniteKernel κ] (R : ℝ) :
    (ν ⊗ₘ κ).map (compressionMap R) = ν ⊗ₘ (κ.map (compression R)) := by
  exact (Measure.compProd_map (compression_contDiff R).continuous.measurable).symm

/-- The compressed law is carried by a fixed compact spatial ball. The flux is
integrated against this law, so its vector measure has the same support bound. -/
theorem compressedMeasure_outside_ball (R : ℝ) :
    (ρ.map (compressionMap R)) (univ ×ˢ (Metric.closedBall (0 : Point d)
      (Real.sqrt (d : ℝ)*|R|))ᶜ) = 0 := by
  rw [Measure.map_apply (compressionMap_measurable R)
    (MeasurableSet.univ.prod Metric.isClosed_closedBall.measurableSet.compl)]
  have he : compressionMap (α := α) (d := d) R ⁻¹'
      (univ ×ˢ (Metric.closedBall (0 : Point d) (Real.sqrt (d : ℝ)*|R|))ᶜ) = ∅ := by
    ext z
    simp only [mem_preimage,mem_prod,mem_univ,mem_compl_iff,true_and,mem_empty_iff_false,iff_false]
    exact not_not.mpr (compression_range_subset R ⟨z.2,rfl⟩)
  rw [he,measure_empty]

end SharpWasserstein.RoughEulerianCompression
