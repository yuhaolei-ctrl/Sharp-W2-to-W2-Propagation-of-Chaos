import SharpWasserstein.TestGenerator
import SharpWasserstein.GaussianHeatCalculus
import SharpWasserstein.FlattenedEuclidean

/-! Genuine frozen-drift Gaussian calculus for arbitrary particle and spatial
dimensions. The extra unused scalar label keeps the finite Stein API uniform. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace SharpWasserstein.FrozenGaussian
open GaussianSharpness

def noiseMap (d N : ℕ) : (Fin (N*d+1) → ℝ) →L[ℝ] Configuration d N :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun a =>
    ContinuousLinearMap.proj (finProdFinEquiv (i,a)).succ

@[simp] theorem noiseMap_apply {d N : ℕ} (ω : Fin (N*d+1) → ℝ) (i : Fin N) (a : Fin d) :
    noiseMap d N ω i a = ω (finProdFinEquiv (i,a)).succ := rfl

theorem noiseMap_single {d N : ℕ} (i : Fin N) (a : Fin d) :
    noiseMap d N (Pi.single (finProdFinEquiv (i,a)).succ 1) = coordinateVector i a := by
  ext j c
  simp only [noiseMap_apply, Pi.single_apply, coordinateVector]
  congr 1
  simp only [Fin.succ_inj, Equiv.apply_eq_iff_eq, Prod.mk.injEq]

theorem vector_decomposition {d N : ℕ} (u : Configuration d N) :
    u = ∑ i, ∑ a, u i a • coordinateVector i a := by
  ext j c
  simp [Finset.sum_apply, coordinateVector, Pi.smul_apply, smul_eq_mul, mul_ite, ite_and]

def label {d N : ℕ} (x u : Configuration d N) (α : ℝ) (ω : Fin (N*d+1) → ℝ) : Configuration d N :=
  x + (α^2/2) • u + α • noiseMap d N ω

theorem label_continuous {d N : ℕ} (x u : Configuration d N) (α : ℝ) : Continuous (label x u α) := by
  exact continuous_const.add ((noiseMap d N).continuous.const_smul α)

theorem label_joint_continuous {d N : ℕ} (x u : Configuration d N) :
    Continuous (fun p : ℝ × (Fin (N*d+1) → ℝ) => label x u p.1 p.2) := by
  unfold label
  fun_prop

theorem label_hasDerivAt {d N : ℕ} (x u : Configuration d N) (α : ℝ) (ω : Fin (N*d+1) → ℝ) :
    HasDerivAt (fun β => label x u β ω) (α • u + noiseMap d N ω) α := by
  have hq : HasDerivAt (fun β : ℝ => β^2/2) α α := by
    convert! ((hasDerivAt_id α).pow 2).div_const 2 using 1
    simp
  convert! ((hq.smul_const u).const_add x).add ((hasDerivAt_id α).smul_const (noiseMap d N ω)) using 1
  simp

theorem label_insert_hasDerivAt {d N : ℕ} (x u : Configuration d N) (α : ℝ)
    (i : Fin N) (a : Fin d) (ω : Fin (N*d) → ℝ) (z : ℝ) :
    HasDerivAt (fun y => label x u α ((finProdFinEquiv (i,a)).succ.insertNth y ω))
      (α • coordinateVector i a) z := by
  have h := (noiseMap d N).hasFDerivAt.comp_hasDerivAt z
    (insertNth_hasDerivAt (finProdFinEquiv (i,a)).succ ω z)
  convert! (h.const_smul α).const_add (x+(α^2/2)•u) using 1
  simp [noiseMap_single]

theorem test_hasDerivAt {d N : ℕ} {φ : Configuration d N → ℝ} (hφ : SmoothCompactTest φ)
    (x u : Configuration d N) (α : ℝ) (ω : Fin (N*d+1) → ℝ) :
    HasDerivAt (fun β => φ (label x u β ω))
      (∑ i, ∑ a, (α * u i a + ω (finProdFinEquiv (i,a)).succ) * coordinateDerivative φ i a (label x u α ω)) α := by
  have h := (hφ.1.differentiable (by simp) (label x u α ω)).hasFDerivAt.comp_hasDerivAt
    α (label_hasDerivAt x u α ω)
  rw [vector_decomposition (α • u + noiseMap d N ω)] at h
  simpa only [Function.comp_def, map_sum, map_smul, smul_eq_mul, coordinateDerivative,
    Pi.add_apply, Pi.smul_apply, noiseMap_apply] using h

theorem test_insert_hasDerivAt {d N : ℕ} {φ : Configuration d N → ℝ} (hφ : SmoothCompactTest φ)
    (x u : Configuration d N) (α : ℝ) (i : Fin N) (a : Fin d)
    (ω : Fin (N*d) → ℝ) (z : ℝ) :
    HasDerivAt (fun y => φ (label x u α ((finProdFinEquiv (i,a)).succ.insertNth y ω)))
      (α * coordinateDerivative φ i a (label x u α ((finProdFinEquiv (i,a)).succ.insertNth z ω))) z := by
  have h := (hφ.1.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt z
    (label_insert_hasDerivAt x u α i a ω z)
  simpa only [Function.comp_def, map_smul, smul_eq_mul, coordinateDerivative] using h

/-- Exact Gaussian integration by parts after adding the frozen drift. -/
theorem coordinate_stein {d N : ℕ} {φ : Configuration d N → ℝ} (hφ : SmoothCompactTest φ)
    (x u : Configuration d N) (α : ℝ) (i : Fin N) (a : Fin d) :
    (∫ ω, ω (finProdFinEquiv (i,a)).succ * coordinateDerivative φ i a (label x u α ω)
      ∂standardLabels (N*d+1)) =
      α * ∫ ω, coordinateDerivative (coordinateDerivative φ i a) i a (label x u α ω)
        ∂standardLabels (N*d+1) := by
  have h₁ := CompactGenerator.coordinate_test hφ i a
  have h₂ := CompactGenerator.coordinate_test h₁ i a
  obtain ⟨C,hC⟩ := (h₁.2.isCompact_range h₁.1.continuous).isBounded.exists_norm_le
  obtain ⟨D,hD⟩ := (h₂.2.isCompact_range h₂.1.continuous).isBounded.exists_norm_le
  have hf := h₁.1.continuous.comp (label_continuous x u α)
  have hg : Continuous (fun ω => α * coordinateDerivative (coordinateDerivative φ i a) i a (label x u α ω)) :=
    continuous_const.mul (h₂.1.continuous.comp (label_continuous x u α))
  have h := standardLabels_stein (finProdFinEquiv (i,a)).succ hf.aestronglyMeasurable hg.aestronglyMeasurable
    (test_insert_hasDerivAt h₁ x u α i a)
    (fun ω => hg.comp (continuous_iff_continuousAt.mpr (fun z => (insertNth_hasDerivAt _ ω z).continuousAt)))
    C (‖α‖*D) (fun ω => hC _ (mem_range_self _))
    (fun ω => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hD _ (mem_range_self _)) (norm_nonneg _))
  simpa only [Function.comp_def, integral_const_mul] using h

end SharpWasserstein.FrozenGaussian
