import SharpWasserstein.EntropyDual
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! # Relative entropy bounds under narrow convergence
Bounded continuous tests are proved to characterize finite KL bounds, using
bounded clipping and L¹ density. Weak-limit stability is then an actual KL
statement, with neither absolute continuity nor finite limit entropy assumed. -/
noncomputable section
open MeasureTheory InformationTheory Real Filter Set
open scoped ENNReal Topology BoundedContinuousFunction
namespace SharpWasserstein

/-- Exponential is Lipschitz on any interval bounded above. -/
theorem entropy_abs_exp_sub_le {u v M : ℝ} (hu : u ≤ M) (hv : v ≤ M) :
    |exp u - exp v| ≤ exp M * |u - v| := by
  wlog huv : u ≤ v generalizing u v
  · simpa [abs_sub_comm] using this hv hu (le_of_not_ge huv)
  have h := mul_le_mul_of_nonneg_left (add_one_le_exp (u - v)) (exp_pos v).le
  have hh : exp v * exp (u - v) = exp u := by rw [← exp_add]; congr 1; ring
  rw [hh] at h
  have hM := exp_le_exp.mpr hv
  rw [abs_of_nonpos (sub_nonpos.mpr (exp_le_exp.mpr huv)),
    abs_of_nonpos (sub_nonpos.mpr huv)]
  nlinarith [mul_le_mul_of_nonneg_right hM (sub_nonneg.mpr huv)]

/-- Clipping an approximation cannot enlarge its error from a bounded target. -/
theorem entropy_clip_error_le {a b M : ℝ} (ha : |a| ≤ M) :
    |a - max (-M) (min M b)| ≤ |a - b| := by
  obtain ⟨hal, hau⟩ := abs_le.mp ha
  by_cases hb : b ≤ M
  · rw [min_eq_right hb]
    by_cases hl : -M ≤ b
    · rw [max_eq_right hl]
    · rw [max_eq_left (le_of_not_ge hl), abs_of_nonneg (by linarith),
        abs_of_nonneg (by linarith)]
      linarith
  · rw [min_eq_left (le_of_not_ge hb), max_eq_right (by linarith),
      abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith

variable {A : Type*} [MeasurableSpace A] [TopologicalSpace A] [BorelSpace A] [NormalSpace A]
  {μ ν : Measure A} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Bounded continuous tests suffice for a finite entropy bound on regular spaces. -/
theorem klDiv_le_of_continuous_entropy_tests [(μ + ν).WeaklyRegular] {C : ℝ}
    (htest : ∀ f : A →ᵇ ℝ,
      (∫ x, f x ∂μ) - (∫ x, exp (f x) ∂ν) + 1 ≤ C) :
    klDiv μ ν ≤ ENNReal.ofReal C := by
  apply klDiv_le_of_bounded_entropy_tests
  intro f hf ⟨M, hb⟩
  have hM : 0 ≤ M := by
    haveI : Nonempty A := nonempty_of_isProbabilityMeasure μ
    obtain ⟨x⟩ := ‹Nonempty A›
    exact (abs_nonneg (f x)).trans (hb x)
  have hfi : Integrable f (μ + ν) :=
    Integrable.of_bound hf.aestronglyMeasurable M (ae_of_all _ hb)
  have hfiμ : Integrable f μ := (integrable_add_measure.mp hfi).1
  have hfiν : Integrable f ν := (integrable_add_measure.mp hfi).2
  have hexpf : Integrable (fun x ↦ exp (f x)) ν := by
    refine Integrable.of_bound hf.exp.aestronglyMeasurable (exp M) (ae_of_all _ fun x ↦ ?_)
    rw [norm_eq_abs, abs_of_pos (exp_pos _)]
    exact exp_le_exp.mpr ((le_abs_self _).trans (hb x))
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε / (1 + exp M)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨g, hg, hgi⟩ := hfi.exists_boundedContinuous_integral_sub_le hδ
  let q : A →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x ↦ max (-M) (min M (g x))) (by fun_prop) M (fun x ↦ by
      rw [norm_eq_abs, abs_le]
      exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩)
  have hq (x : A) : |q x| ≤ M := by
    change |max (-M) (min M (g x))| ≤ M
    rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hqe (x : A) : |f x - q x| ≤ |f x - g x| := entropy_clip_error_le (hb x)
  have heq : Integrable (fun x ↦ exp (q x)) ν := by
    refine Integrable.of_bound q.continuous.measurable.exp.aestronglyMeasurable (exp M)
      (ae_of_all _ fun x ↦ ?_)
    rw [norm_eq_abs, abs_of_pos (exp_pos _)]
    exact exp_le_exp.mpr ((le_abs_self _).trans (hq x))
  have heμ : ∫ x, |f x - g x| ∂μ ≤ δ := by
    calc
      _ ≤ ∫ x, |f x - g x| ∂(μ + ν) := integral_mono_measure
        (Measure.le_add_right le_rfl) (ae_of_all _ fun x ↦ abs_nonneg _) (hfi.sub hgi).abs
      _ ≤ δ := hg
  have heν : ∫ x, |f x - g x| ∂ν ≤ δ := by
    calc
      _ ≤ ∫ x, |f x - g x| ∂(μ + ν) := integral_mono_measure
        (Measure.le_add_left le_rfl) (ae_of_all _ fun x ↦ abs_nonneg _) (hfi.sub hgi).abs
      _ ≤ δ := hg
  have h1 : |(∫ x, f x ∂μ) - ∫ x, q x ∂μ| ≤ δ := by
    rw [← integral_sub hfiμ (q.integrable μ)]
    calc
      _ ≤ ∫ x, |f x - q x| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ x, |f x - g x| ∂μ := integral_mono (hfiμ.sub (q.integrable μ)).abs
        (hfiμ.sub (g.integrable μ)).abs hqe
      _ ≤ δ := heμ
  have h2 : |(∫ x, exp (f x) ∂ν) - ∫ x, exp (q x) ∂ν| ≤ exp M * δ := by
    rw [← integral_sub hexpf heq]
    calc
      _ ≤ ∫ x, |exp (f x) - exp (q x)| ∂ν := abs_integral_le_integral_abs
      _ ≤ ∫ x, exp M * |f x - g x| ∂ν := integral_mono (hexpf.sub heq).abs
        ((hfiν.sub (g.integrable ν)).abs.const_mul _) fun x ↦
          (entropy_abs_exp_sub_le ((le_abs_self _).trans (hb x))
            ((le_abs_self _).trans (hq x))).trans
              (mul_le_mul_of_nonneg_left (hqe x) (exp_pos M).le)
      _ = exp M * ∫ x, |f x - g x| ∂ν := integral_const_mul _ _
      _ ≤ exp M * δ := mul_le_mul_of_nonneg_left heν (exp_pos M).le
  have ht := htest q
  have hd : δ + exp M * δ = ε := by dsimp [δ]; field_simp
  linarith [(abs_le.mp h1).2, (abs_le.mp h2).1]

/-- Exponentiating a bounded continuous test again gives such a test. -/
def entropyTestExp (f : A →ᵇ ℝ) : A →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x ↦ exp (f x))
    f.continuous.rexp (exp ‖f‖) fun x ↦ by
      rw [norm_eq_abs, abs_of_pos (exp_pos _)]
      exact exp_le_exp.mpr ((le_abs_self _).trans (f.norm_coe_le_norm x))

/-- Joint lower semicontinuity of the actual relative entropy under narrow
convergence. The limit laws need no absolute-continuity or entropy hypothesis. -/
theorem klDiv_le_liminf_of_narrow {ι : Type*} {F : Filter ι} [NeBot F]
    (μs νs : ι → ProbabilityMeasure A) (μ ν : ProbabilityMeasure A)
    [((μ : Measure A) + (ν : Measure A)).WeaklyRegular]
    (hμ : Tendsto μs F (𝓝 μ)) (hν : Tendsto νs F (𝓝 ν)) :
    klDiv (μ : Measure A) (ν : Measure A) ≤
      liminf (fun n ↦ klDiv (μs n : Measure A) (νs n : Measure A)) F := by
  let L := liminf (fun n ↦ klDiv (μs n : Measure A) (νs n : Measure A)) F
  by_cases hL : L = ∞
  · change _ ≤ L
    rw [hL]
    exact le_top
  have ht : ∀ f : A →ᵇ ℝ,
      (∫ x, f x ∂(μ : Measure A)) - (∫ x, exp (f x) ∂(ν : Measure A)) + 1 ≤ L.toReal := by
    intro f
    have hm := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ f
    have hn := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hν (entropyTestExp f)
    have hc : Tendsto (fun n ↦ ENNReal.ofReal
        ((∫ x, f x ∂(μs n : Measure A)) - (∫ x, exp (f x) ∂(νs n : Measure A)) + 1)) F
        (𝓝 (ENNReal.ofReal ((∫ x, f x ∂(μ : Measure A)) -
          (∫ x, exp (f x) ∂(ν : Measure A)) + 1))) :=
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((hm.sub hn).add_const 1)
    have hb (n : ι) : ENNReal.ofReal
        ((∫ x, f x ∂(μs n : Measure A)) - (∫ x, exp (f x) ∂(νs n : Measure A)) + 1) ≤
          klDiv (μs n : Measure A) (νs n : Measure A) := by
      by_cases hk : klDiv (μs n : Measure A) (νs n : Measure A) = ∞
      · rw [hk]; exact le_top
      · exact ENNReal.ofReal_le_of_le_toReal (bounded_entropy_test_le_klDiv hk
          f.continuous.measurable (fun x ↦ f.norm_coe_le_norm x))
    have hl : ENNReal.ofReal ((∫ x, f x ∂(μ : Measure A)) -
        (∫ x, exp (f x) ∂(ν : Measure A)) + 1) ≤ L := by
      calc
        _ = liminf (fun n ↦ ENNReal.ofReal ((∫ x, f x ∂(μs n : Measure A)) -
            (∫ x, exp (f x) ∂(νs n : Measure A)) + 1)) F := hc.liminf_eq.symm
        _ ≤ L := liminf_le_liminf (Filter.Eventually.of_forall hb)
    exact (ENNReal.ofReal_le_iff_le_toReal hL).mp hl
  exact (klDiv_le_of_continuous_entropy_tests ht).trans_eq (ENNReal.ofReal_toReal hL)

/-- A uniform entropy-cost bound survives simultaneous narrow limits of both
laws. This specializes the lower-semicontinuity theorem to approximation schemes. -/
theorem klDiv_le_of_narrow_entropy_bound {ι : Type*} {F : Filter ι} [NeBot F]
    (μs νs : ι → ProbabilityMeasure A) (μ ν : ProbabilityMeasure A)
    [((μ : Measure A) + (ν : Measure A)).WeaklyRegular]
    (hμ : Tendsto μs F (𝓝 μ)) (hν : Tendsto νs F (𝓝 ν)) {C : ℝ≥0∞}
    (hbound : ∀ᶠ n in F, klDiv (μs n : Measure A) (νs n : Measure A) ≤ C) :
    klDiv (μ : Measure A) (ν : Measure A) ≤ C := by
  apply (klDiv_le_liminf_of_narrow μs νs μ ν hμ hν).trans
  simpa using liminf_le_liminf (f := F) hbound

end SharpWasserstein
