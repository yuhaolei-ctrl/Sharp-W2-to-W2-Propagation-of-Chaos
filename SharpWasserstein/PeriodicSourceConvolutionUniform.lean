import SharpWasserstein.PeriodicSourceConvolutionTime

/-! Bounds for every translated kernel and its genuine repeated diffusion
generators are uniform in the convolution position. -/
noncomputable section
open scoped ContDiff BigOperators
namespace SharpWasserstein.PeriodicSourceConvolution
open NoiseAverage WeightedTangent PeriodicIntegrationByParts PeriodicBochner
variable {ι : Type*} {D E F G : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Global derivative bounds shared by an actual family of smooth tests. -/
def UniformDerivatives (f : ι → E → F) : Prop :=
  ∀ m : ℕ,∃ C : ℝ,0 ≤ C ∧ ∀ p x,‖iteratedFDeriv ℝ m (f p) x‖ ≤ C

theorem UniformDerivatives.at {f : ι → E → F} (h : UniformDerivatives f) (p : ι) :
    AllDerivativesBounded (f p) := fun m => by
  obtain ⟨C,hC,hb⟩ := h m
  exact ⟨C,hC,hb p⟩

theorem UniformDerivatives.bounded {f : ι → E → F} (h : UniformDerivatives f) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ p x,‖f p x‖ ≤ C := by
  simpa only [norm_iteratedFDeriv_zero] using h 0

theorem UniformDerivatives.fderiv {f : ι → E → F} (h : UniformDerivatives f) :
    UniformDerivatives (fun p => _root_.fderiv ℝ (f p)) := by
  intro m
  obtain ⟨C,hC,hb⟩ := h (m+1)
  exact ⟨C,hC,fun p x => by rw [norm_iteratedFDeriv_fderiv]; exact hb p x⟩

theorem UniformDerivatives.add {f g : ι → E → F}
    (hf : ∀ p,ContDiff ℝ ∞ (f p)) (hg : ∀ p,ContDiff ℝ ∞ (g p))
    (hBf : UniformDerivatives f) (hBg : UniformDerivatives g) :
    UniformDerivatives (fun p x => f p x+g p x) := by
  intro m
  obtain ⟨C,hC,hCf⟩ := hBf m
  obtain ⟨D,hD,hDg⟩ := hBg m
  refine ⟨C+D,add_nonneg hC hD,fun p x => ?_⟩
  rw [fun_iteratedFDeriv_add_apply
    ((hf p).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl m)).contDiffAt
    ((hg p).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl m)).contDiffAt]
  exact (norm_add_le _ _).trans (add_le_add (hCf p x) (hDg p x))

theorem uniform_const (c : F) : UniformDerivatives (fun _ : ι => fun _ : E => c) := by
  intro m
  obtain ⟨C,hC,hb⟩ := (allDerivativesBounded_const (E := E) c) m
  exact ⟨C,hC,fun _ => hb⟩

theorem UniformDerivatives.sum {α : Type*} (s : Finset α) {f : α → ι → E → F}
    (hf : ∀ i ∈ s,∀ p,ContDiff ℝ ∞ (f i p)) (hB : ∀ i ∈ s,UniformDerivatives (f i)) :
    UniformDerivatives (fun p x => ∑ i ∈ s,f i p x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using uniform_const (ι := ι) (E := E) (0:F)
  | @insert i s hi ih =>
    have hs (p) : ContDiff ℝ ∞ (fun x => ∑ j ∈ s,f j p x) :=
      ContDiff.sum (fun j hj => hf j (Finset.mem_insert_of_mem hj) p)
    simpa only [Finset.sum_insert hi] using
      (hB i (Finset.mem_insert_self i s)).add (hf i (Finset.mem_insert_self i s)) hs
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)) (fun j hj => hB j (Finset.mem_insert_of_mem hj)))

theorem UniformDerivatives.clm_apply {f : ι → E → F →L[ℝ] G} {g : ι → E → F}
    (hf : ∀ p,ContDiff ℝ ∞ (f p)) (hg : ∀ p,ContDiff ℝ ∞ (g p))
    (hBf : UniformDerivatives f) (hBg : UniformDerivatives g) :
    UniformDerivatives (fun p x => f p x (g p x)) := by
  choose C hC hCf using hBf
  choose B hB hBg' using hBg
  intro m
  refine ⟨∑ i ∈ Finset.range (m+1),(m.choose i:ℝ)*C i*B (m-i),
    Finset.sum_nonneg (fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC i)) (hB _)),fun p x => ?_⟩
  apply (norm_iteratedFDeriv_clm_apply (hf p) (hg p) x
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl m)).trans
  exact Finset.sum_le_sum fun i _ => mul_le_mul
    (mul_le_mul_of_nonneg_left (hCf i p x) (Nat.cast_nonneg _)) (hBg' (m-i) p x)
    (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hC i))

theorem UniformDerivatives.comp_linear {f : ι → E → F}
    (hf : ∀ p,ContDiff ℝ ∞ (f p)) (hBf : UniformDerivatives f) (L : D →L[ℝ] E) :
    UniformDerivatives (fun p x => f p (L x)) := by
  choose C hC hCf using hBf
  have hBL : AllDerivativesBounded (_root_.fderiv ℝ L) := by
    have he : _root_.fderiv ℝ L = fun _ => L := funext (fun _ => L.fderiv)
    rw [he]
    exact allDerivativesBounded_const L
  choose B hB hBg using hBL
  intro m
  let Cm : ℝ := ∑ i ∈ Finset.range (m+1),C i
  let Bm : ℝ := 1+∑ i ∈ Finset.range m,B i
  have hCm : 0 ≤ Cm := Finset.sum_nonneg fun i _ => hC i
  have hBm : 1 ≤ Bm := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => hB i)
  refine ⟨(m.factorial:ℝ)*Cm*Bm^m,by positivity,fun p x => ?_⟩
  apply norm_iteratedFDeriv_comp_le (hf p) L.contDiff (ENat.natCast_le_of_coe_top_le_withTop le_rfl m)
  · intro i hi
    exact (hCf i p (L x)).trans (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_range.mpr (by omega)))
  · intro i hi him
    have hei : i = (i-1)+1 := by omega
    have hb : ‖iteratedFDeriv ℝ i L x‖ ≤ B (i-1) := by
      rw [hei,← norm_iteratedFDeriv_fderiv]
      exact hBg (i-1) x
    have hb' : B (i-1) ≤ Bm := by
      have hh := Finset.single_le_sum (fun j _ => hB j) (Finset.mem_range.mpr (by omega : i-1<m))
      dsimp [Bm]
      linarith
    exact hb.trans (hb'.trans (by simpa only [pow_one] using pow_le_pow_right₀ hBm hi))

/-- The reflected product kernels share all derivative bounds globally. -/
theorem euclideanKernelTest_uniform {n : ℕ} (κ : ℝ) :
    UniformDerivatives (euclideanKernelTest (n := n) κ) := by
  have he (x : Coordinates n) : euclideanKernelTest κ x = fun y =>
      euclideanKernelTest κ 0 (y-(coordinateEquiv n).symm x) := by
    funext y
    simp only [euclideanKernelTest,map_sub,ContinuousLinearEquiv.apply_symm_apply]
    congr 1
    abel
  intro m
  obtain ⟨C,hC,hb⟩ := (euclideanKernelTest_bounded (n := n) κ 0) m
  refine ⟨C,hC,fun x y => ?_⟩
  rw [he,show (fun y => euclideanKernelTest κ 0 (y-(coordinateEquiv n).symm x)) =
    (fun y => euclideanKernelTest κ 0 (y+(-(coordinateEquiv n).symm x))) by rfl,
    iteratedFDeriv_comp_add_right]
  exact hb _

variable {d N : ℕ}

theorem uniform_coordinateDerivative {f : ι → Configuration d N → ℝ}
    (hf : ∀ p,ContDiff ℝ ∞ (f p)) (hB : UniformDerivatives f) (i : Fin N) (a : Fin d) :
    UniformDerivatives (fun p => coordinateDerivative (f p) i a) :=
  hB.fderiv.clm_apply (fun p => (contDiff_infty_iff_fderiv.mp (hf p)).2)
    (fun _ => contDiff_const) (uniform_const (coordinateVector i a))

/-- The genuine diffusion generator preserves uniform derivative families. -/
theorem uniform_generator {f : ι → Configuration d N → ℝ}
    {b : Configuration d N → Configuration d N} (hb : ContDiff ℝ ∞ b)
    (hBb : AllDerivativesBounded b) (hf : ∀ p,ContDiff ℝ ∞ (f p)) (hB : UniformDerivatives f) :
    UniformDerivatives (fun p => generator b (f p)) := by
  have hc (p) (i : Fin N) (a : Fin d) := coordinateDerivative_smooth (coordinateDerivative_smooth (hf p) i a) i a
  have hL (p) : ContDiff ℝ ∞ (laplacian (f p)) := ContDiff.sum fun i _ => ContDiff.sum fun a _ => hc p i a
  have hBL : UniformDerivatives (fun p => laplacian (f p)) :=
    UniformDerivatives.sum Finset.univ (fun i _ p => ContDiff.sum fun a _ => hc p i a)
      (fun i _ => UniformDerivatives.sum Finset.univ (fun a _ p => hc p i a)
        (fun a _ => uniform_coordinateDerivative (fun p => coordinateDerivative_smooth (hf p) i a)
          (uniform_coordinateDerivative hf hB i a) i a))
  have hbb : UniformDerivatives (fun _ : ι => b) := by
    intro m
    obtain ⟨C,hC,h⟩ := hBb m
    exact ⟨C,hC,fun _ => h⟩
  have he : (fun p => generator b (f p)) = fun p x => laplacian (f p) x+fderiv ℝ (f p) x (b x) := by
    funext p x
    exact generator_eq_laplacian_add_fderiv _ _ _
  rw [he]
  exact hBL.add hL (fun p => (contDiff_infty_iff_fderiv.mp (hf p)).2.clm_apply hb)
    (hB.fderiv.clm_apply (fun p => (contDiff_infty_iff_fderiv.mp (hf p)).2) (fun _ => hb) hbb)

open PropagatedSourceEquation in
theorem uniform_euclideanGenerator {f : ι → Point (N*d) → ℝ}
    {b : Configuration d N → Configuration d N} (hb : ContDiff ℝ ∞ b)
    (hBb : AllDerivativesBounded b) (hf : ∀ p,ContDiff ℝ ∞ (f p)) (hB : UniformDerivatives f) :
    UniformDerivatives (fun p => euclideanGenerator b (f p)) :=
  (uniform_generator hb hBb (fun p => (hf p).comp (configurationEuclidean d N).contDiff)
    (hB.comp_linear hf (configurationEuclidean d N).toContinuousLinearMap)).comp_linear
    (fun p => generator_smooth hb ((hf p).comp (configurationEuclidean d N).contDiff))
    (configurationEuclidean d N).symm.toContinuousLinearMap

end SharpWasserstein.PeriodicSourceConvolution
