module

public import SharpWasserstein.Compat
public import SharpWasserstein.FrozenGaussianCalculus

@[expose] public section

/-! Differentiation under the genuine Gaussian integral, followed by Stein's
identity, gives the frozen drift plus Laplacian generator. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace SharpWasserstein.FrozenGaussian
open GaussianSharpness

theorem compact_bound {d N : ℕ} {φ : Configuration d N → ℝ} (hφ : SmoothCompactTest φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖φ x‖ ≤ C := by
  obtain ⟨C,hC⟩ := (hφ.2.isCompact_range hφ.1.continuous).isBounded.exists_norm_le
  exact ⟨max C 0, le_max_right _ _, fun x => (hC _ (mem_range_self x)).trans (le_max_left _ _)⟩

def expectation {d N : ℕ} (φ : Configuration d N → ℝ) (x u : Configuration d N) (α : ℝ) : ℝ :=
  ∫ ω, φ (label x u α ω) ∂standardLabels (N*d+1)

def velocityPairing {d N : ℕ} (φ : Configuration d N → ℝ) (x u : Configuration d N)
    (α : ℝ) (ω : Fin (N*d+1) → ℝ) : ℝ :=
  ∑ i, ∑ a, (α*u i a + ω (finProdFinEquiv (i,a)).succ) * coordinateDerivative φ i a (label x u α ω)

theorem expectation_continuous {d N : ℕ} {φ : Configuration d N → ℝ}
    (hφ : SmoothCompactTest φ) (x u : Configuration d N) : Continuous (expectation φ x u) := by
  letI := standardLabels_probability (N*d+1)
  obtain ⟨C,_,hC⟩ := compact_bound hφ
  apply continuous_of_dominated (bound := fun _ => C)
  · intro α
    exact (hφ.1.continuous.comp (label_continuous x u α)).aestronglyMeasurable
  · intro α
    exact Eventually.of_forall fun ω => hC _
  · exact integrable_const C
  · exact Eventually.of_forall fun ω => hφ.1.continuous.comp
      ((label_joint_continuous x u).comp (continuous_id.prodMk continuous_const))

/-- The derivative is proved by an integrable local envelope, not by a formal
exchange of differentiation and expectation. -/
theorem expectation_hasDerivAt_raw {d N : ℕ} {φ : Configuration d N → ℝ}
    (hφ : SmoothCompactTest φ) (x u : Configuration d N) (α : ℝ) :
    HasDerivAt (expectation φ x u)
      (∫ ω, velocityPairing φ x u α ω ∂standardLabels (N*d+1)) α := by
  letI := standardLabels_probability (N*d+1)
  choose C hCn hC using fun i : Fin N => fun a : Fin d => compact_bound (CompactGenerator.coordinate_test hφ i a)
  obtain ⟨B,_,hB⟩ := compact_bound hφ
  let bound := fun ω : Fin (N*d+1) → ℝ =>
    ∑ i, ∑ a, ((|α|+1)*|u i a| + ‖ω (finProdFinEquiv (i,a)).succ‖) * C i a
  have hb : Integrable bound (standardLabels (N*d+1)) := by
    apply integrable_finsetSum
    intro i _
    apply integrable_finsetSum
    intro a _
    exact ((integrable_const ((|α|+1)*|u i a|)).add
      ((coordinate_memLp (N*d+1) (finProdFinEquiv (i,a)).succ).integrable (by norm_num)).norm).mul_const (C i a)
  have hG (β : ℝ) : Continuous (velocityPairing φ x u β) := by
    apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro a _
    exact (continuous_const.add (continuous_apply _)).mul
      ((CompactGenerator.coordinate_test hφ i a).1.continuous.comp (label_continuous x u β))
  have hbound (ω : Fin (N*d+1) → ℝ) (β : ℝ) (hβ : β ∈ Metric.ball α 1) :
      ‖velocityPairing φ x u β ω‖ ≤ bound ω := by
    have hba : |β| ≤ |α|+1 := by
      have hdist : |β-α| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using hβ
      have ht := abs_add_le (β-α) α
      rw [sub_add_cancel] at ht
      linarith
    calc
      ‖velocityPairing φ x u β ω‖ ≤ ∑ i, ∑ a, ‖(β*u i a + ω (finProdFinEquiv (i,a)).succ) *
          coordinateDerivative φ i a (label x u β ω)‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
      _ ≤ bound ω := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro a _
        rw [norm_mul]
        apply mul_le_mul _ (hC i a _) (norm_nonneg _) (by positivity)
        calc
          ‖β*u i a + ω (finProdFinEquiv (i,a)).succ‖ ≤ ‖β*u i a‖ + ‖ω (finProdFinEquiv (i,a)).succ‖ := norm_add_le _ _
          _ ≤ _ := by rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]; gcongr
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := standardLabels (N*d+1)) (F := fun β ω => φ (label x u β ω))
    (F' := velocityPairing φ x u) (x₀ := α) (s := Metric.ball α 1) (bound := bound)
    (Metric.ball_mem_nhds _ zero_lt_one)
    (Eventually.of_forall fun β => (hφ.1.continuous.comp (label_continuous x u β)).aestronglyMeasurable)
    (Integrable.of_bound (hφ.1.continuous.comp (label_continuous x u α)).aestronglyMeasurable B (Eventually.of_forall fun ω => hB _))
    (hG α).aestronglyMeasurable
    (Eventually.of_forall hbound) hb
    (Eventually.of_forall fun ω β _ => test_hasDerivAt hφ x u β ω)
  exact h.2

theorem integrable_comp_label {d N : ℕ} {f : Configuration d N → ℝ}
    (hf : Continuous f) (hc : HasCompactSupport f) (x u : Configuration d N) (α : ℝ) :
    Integrable (fun ω => f (label x u α ω)) (standardLabels (N*d+1)) := by
  letI := standardLabels_probability (N*d+1)
  obtain ⟨C,hC⟩ := (hc.isCompact_range hf).isBounded.exists_norm_le
  exact Integrable.of_bound (hf.comp (label_continuous x u α)).aestronglyMeasurable
    C (Eventually.of_forall fun ω => hC _ (mem_range_self _))

theorem integral_velocityPairing {d N : ℕ} {φ : Configuration d N → ℝ}
    (hφ : SmoothCompactTest φ) (x u : Configuration d N) (α : ℝ) :
    (∫ ω, velocityPairing φ x u α ω ∂standardLabels (N*d+1)) =
      α * expectation (generator (fun _ => u) φ) x u α := by
  letI := standardLabels_probability (N*d+1)
  let L := fun ω => laplacian φ (label x u α ω)
  let S := fun ω => ∑ i, ∑ a, u i a * coordinateDerivative φ i a (label x u α ω)
  let H := fun ω => ∑ i, ∑ a, ω (finProdFinEquiv (i,a)).succ * coordinateDerivative φ i a (label x u α ω)
  have hD (i : Fin N) (a : Fin d) : Integrable
      (fun ω => coordinateDerivative φ i a (label x u α ω)) (standardLabels (N*d+1)) :=
    integrable_comp_label (CompactGenerator.coordinate_test hφ i a).1.continuous
      (CompactGenerator.coordinate_test hφ i a).2 x u α
  have hDD (i : Fin N) (a : Fin d) : Integrable
      (fun ω => coordinateDerivative (coordinateDerivative φ i a) i a (label x u α ω)) (standardLabels (N*d+1)) :=
    integrable_comp_label (CompactGenerator.coordinate_test (CompactGenerator.coordinate_test hφ i a) i a).1.continuous
      (CompactGenerator.coordinate_test (CompactGenerator.coordinate_test hφ i a) i a).2 x u α
  have hWD (i : Fin N) (a : Fin d) : Integrable
      (fun ω => ω (finProdFinEquiv (i,a)).succ * coordinateDerivative φ i a (label x u α ω))
      (standardLabels (N*d+1)) := by
    obtain ⟨C,_,hC⟩ := compact_bound (CompactGenerator.coordinate_test hφ i a)
    exact ((coordinate_memLp (N*d+1) (finProdFinEquiv (i,a)).succ).integrable (by norm_num)).mul_bdd
      (hD i a).aestronglyMeasurable (Eventually.of_forall fun ω => hC _)
  have hS : Integrable S (standardLabels (N*d+1)) :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun a _ => (hD i a).const_mul (u i a)))
  have hH : Integrable H (standardLabels (N*d+1)) :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun a _ => hWD i a))
  have hL : Integrable L (standardLabels (N*d+1)) :=
    integrable_comp_label (CompactGenerator.laplacian_test hφ).1.continuous
      (CompactGenerator.laplacian_test hφ).2 x u α
  have heH : (∫ ω, H ω ∂standardLabels (N*d+1)) = α * ∫ ω, L ω ∂standardLabels (N*d+1) := by
    rw [show H = fun ω => ∑ i, ∑ a, ω (finProdFinEquiv (i,a)).succ * coordinateDerivative φ i a (label x u α ω) from rfl,
      integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun a _ => hWD i a))]
    simp_rw [integral_finsetSum _ (fun a _ => hWD _ a), coordinate_stein hφ x u α]
    simp_rw [← Finset.mul_sum]
    congr 1
    simp_rw [← integral_finsetSum _ (fun a _ => hDD _ a)]
    rw [← integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun a _ => hDD i a))]
    rfl
  have heG : velocityPairing φ x u α = fun ω => α*S ω + H ω := by
    funext ω
    simp only [velocityPairing, S, H, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [heG, integral_add (hS.const_mul α) hH, integral_const_mul, heH, ← mul_add]
  congr 1
  rw [← integral_add hS hL]
  apply integral_congr_ae
  exact Eventually.of_forall fun ω => by simp only [S,L,generator]; ring

/-- The exact frozen-generator derivative, including diffusion coefficient one. -/
theorem expectation_hasDerivAt {d N : ℕ} {φ : Configuration d N → ℝ}
    (hφ : SmoothCompactTest φ) (x u : Configuration d N) (α : ℝ) :
    HasDerivAt (expectation φ x u)
      (α * expectation (generator (fun _ => u) φ) x u α) α := by
  simpa only [integral_velocityPairing hφ x u α] using expectation_hasDerivAt_raw hφ x u α

end SharpWasserstein.FrozenGaussian
