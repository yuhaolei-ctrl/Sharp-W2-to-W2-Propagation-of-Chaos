import SharpWasserstein.BoundedIndependentSum
import SharpWasserstein.EntropyVariational

/-!
# The internal entropy source from bounded interactions

For each tagged coordinate, split the reference product law into that particle
and the remaining independent coordinates. Hoeffding concentration for the
centered off-diagonal sum and a bounded diagonal shift give an exponential-
square moment. The entropy variational inequality then applies to the actual
current law. Self-interaction is retained throughout.
-/

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Real
open scoped ENNReal NNReal BigOperators

namespace SharpWasserstein

/-- Centering of a scalar interaction in its second variable. -/
def centeredKernel {A : Type*} [MeasurableSpace A] (r : Measure A)
    (b : A → A → ℝ) (x y : A) : ℝ := b x y - ∫ z, b x z ∂r

/-- The internal interaction sum, including its diagonal term. -/
def internalScalarCurrent {A : Type*} [MeasurableSpace A] {m : ℕ}
    (r : Measure A) (b : A → A → ℝ) (i : Fin m) (x : Fin m → A) : ℝ :=
  ∑ j, centeredKernel r b (x i) (x j)

theorem measurable_centeredKernel {A : Type*} [MeasurableSpace A]
    {r : Measure A} [SFinite r] {b : A → A → ℝ}
    (hb : Measurable (Function.uncurry b)) : Measurable (Function.uncurry (centeredKernel r b)) := by
  exact hb.sub ((hb.stronglyMeasurable.integral_prod_right (ν := r)).measurable.comp measurable_fst)

theorem measurable_internalScalarCurrent {A : Type*} [MeasurableSpace A]
    {r : Measure A} [SFinite r] {b : A → A → ℝ}
    (hb : Measurable (Function.uncurry b)) {m : ℕ} (i : Fin m) :
    Measurable (internalScalarCurrent r b i) := by
  unfold internalScalarCurrent
  apply Finset.measurable_sum
  intro j _
  have hg : Measurable (fun x : Fin m → A ↦ (x i, x j)) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply j)
  exact (measurable_centeredKernel (r := r) hb).comp hg

theorem centeredKernel_abs_le {A : Type*} [MeasurableSpace A]
    {r : Measure A} [IsProbabilityMeasure r] {b : A → A → ℝ} {M : ℝ}
    (hb : Measurable (Function.uncurry b)) (hbound : ∀ x y, |b x y| ≤ M) (x y : A) :
    |centeredKernel r b x y| ≤ 2 * M := by
  have hi : |∫ z, b x z ∂r| ≤ M := integral_bounded_observable_abs_le (r := r)
    (hb.comp measurable_prodMk_left) (hbound x)
  have h := abs_sub (b x y) (∫ z, b x z ∂r)
  unfold centeredKernel
  linarith [hbound x y]

theorem internalScalarCurrent_abs_le {A : Type*} [MeasurableSpace A]
    {r : Measure A} [IsProbabilityMeasure r] {b : A → A → ℝ} {M : ℝ}
    (hb : Measurable (Function.uncurry b)) (hbound : ∀ x y, |b x y| ≤ M)
    {m : ℕ} (i : Fin m) (x : Fin m → A) : |internalScalarCurrent r b i x| ≤ m * (2 * M) := by
  unfold internalScalarCurrent
  calc
    _ ≤ ∑ j, |centeredKernel r b (x i) (x j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin m, 2 * M := Finset.sum_le_sum (fun _ _ ↦ centeredKernel_abs_le (r := r) hb hbound _ _)
    _ = _ := by simp

theorem internalScalarCurrent_split {A : Type*} [MeasurableSpace A]
    (r : Measure A) (b : A → A → ℝ) {n : ℕ} (i : Fin (n + 1)) (x : Fin (n + 1) → A) :
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ A) i
    internalScalarCurrent r b i x = centeredKernel r b (e x).1 (e x).1 +
      centeredProductSum r (fun _ : Fin n ↦ b (e x).1) (e x).2 := by
  change (∑ j, centeredKernel r b (x i) (x j)) =
    centeredKernel r b (x i) (x i) + ∑ j : Fin n, centeredKernel r b (x i) (x (i.succAbove j))
  exact Fin.sum_univ_succAbove _ i

/-- Uniform exponential-square moment for the actual empirical interaction
sum under the reference tensor law, with the diagonal contribution included. -/
theorem internalScalarCurrent_exp_square_le {A : Type*} [MeasurableSpace A]
    {r : Measure A} [IsProbabilityMeasure r] {b : A → A → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hb : Measurable (Function.uncurry b)) (hbound : ∀ x y, |b x y| ≤ M)
    {m : ℕ} (i : Fin m) :
    ∫ x, exp (internalSquareScale M / m * internalScalarCurrent r b i x ^ 2)
      ∂Measure.pi (fun _ : Fin m ↦ r) ≤ exp 1 * squareExponentialConstant := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := i.isLt; omega : m ≠ 0)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ A) i
  let F := fun p : A × (Fin n → A) ↦ exp (internalSquareScale M / (n + 1 : ℝ) *
    internalScalarCurrent r b i (e.symm p) ^ 2)
  have hFi : Integrable F (r.prod (Measure.pi fun _ : Fin n ↦ r)) := by
    exact integrable_exp_sq_of_bounded
      ((measurable_internalScalarCurrent (r := r) hb i).comp e.symm.measurable)
      (fun p ↦ internalScalarCurrent_abs_le (r := r) hb hbound i (e.symm p)) (by
        exact div_nonneg (internalSquareScale_pos hM).le (by positivity))
  have hsplit (x : A) (y : Fin n → A) :
      internalScalarCurrent r b i (e.symm (x, y)) =
        centeredKernel r b x x + centeredProductSum r (fun _ : Fin n ↦ b x) y := by
    have h := internalScalarCurrent_split r b i (e.symm (x, y))
    change internalScalarCurrent r b i (e.symm (x, y)) =
      centeredKernel r b (e (e.symm (x, y))).1 (e (e.symm (x, y))).1 +
        centeredProductSum r (fun _ : Fin n ↦ b (e (e.symm (x, y))).1) (e (e.symm (x, y))).2 at h
    simpa only [e.apply_symm_apply] using h
  have hpull := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ r) i).integral_comp' F
  change (∫ x, F (e x) ∂Measure.pi (fun _ : Fin (n + 1) ↦ r)) = _ at hpull
  simp only [F, e.symm_apply_apply] at hpull
  rw [Nat.cast_succ]
  rw [hpull, integral_prod _ hFi]
  calc
    _ ≤ ∫ _x : A, exp 1 * squareExponentialConstant ∂r := by
      apply integral_mono_ae hFi.integral_prod_left (integrable_const _)
      exact Filter.Eventually.of_forall fun x ↦ by
        dsimp only [F]
        simp_rw [hsplit x]
        exact shifted_centeredProductSum_exp_square_le hM
          (fun _ ↦ hb.comp measurable_prodMk_left) (fun _ ↦ hbound x)
          (centeredKernel_abs_le (r := r) hb hbound x x)
    _ = _ := by simp

/-- The dimension-free scalar constant used after the entropy variational step. -/
def internalSourceConstant (M : ℝ) : ℝ :=
  (1 + |log (exp 1 * squareExponentialConstant)|) / internalSquareScale M

theorem internalSourceConstant_nonneg {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ internalSourceConstant M := by
  exact div_nonneg (by positivity) (internalSquareScale_pos hM).le

theorem integrable_internalScalarCurrent_sq {A : Type*} [MeasurableSpace A]
    {r : Measure A} [IsProbabilityMeasure r] {b : A → A → ℝ} {M : ℝ}
    (hb : Measurable (Function.uncurry b)) (hbound : ∀ x y, |b x y| ≤ M)
    {m : ℕ} (i : Fin m) (P : Measure (Fin m → A)) [IsFiniteMeasure P] :
    Integrable (fun x ↦ internalScalarCurrent r b i x ^ 2) P := by
  apply (integrable_const (((m : ℝ) * (2 * M)) ^ 2)).mono'
    ((measurable_internalScalarCurrent (r := r) hb i).pow_const 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h := pow_le_pow_left₀ (abs_nonneg (internalScalarCurrent r b i x))
      (internalScalarCurrent_abs_le (r := r) hb hbound i x) 2
    rwa [sq_abs] at h

/-- Entropy controls the square of each actual tagged-particle internal sum.
The uniform exponential moment is proved from the bounded kernel above. -/
theorem internalScalarCurrent_sq_le_entropy {A : Type*} [MeasurableSpace A]
    {r : Measure A} [IsProbabilityMeasure r] {b : A → A → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hb : Measurable (Function.uncurry b)) (hbound : ∀ x y, |b x y| ≤ M)
    {m : ℕ} (i : Fin m) {P : Measure (Fin m → A)} [IsProbabilityMeasure P]
    (hfinite : klDiv P (Measure.pi fun _ : Fin m ↦ r) ≠ ∞) :
    ∫ x, internalScalarCurrent r b i x ^ 2 ∂P ≤
      internalSourceConstant M * m * (1 + (klDiv P (Measure.pi fun _ : Fin m ↦ r)).toReal) := by
  have hm : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by have := i.isLt; omega)
  have hscalePos := internalSquareScale_pos hM
  have hα : 0 < internalSquareScale M / m := div_pos hscalePos hm
  have hi := integrable_internalScalarCurrent_sq (r := r) hb hbound i P
  have hexp : Integrable (fun x ↦ exp (internalSquareScale M / m * internalScalarCurrent r b i x ^ 2))
      (Measure.pi fun _ : Fin m ↦ r) :=
    integrable_exp_sq_of_bounded (measurable_internalScalarCurrent (r := r) hb i)
      (internalScalarCurrent_abs_le (r := r) hb hbound i) hα.le
  have h := integral_le_klDiv_add_log_exp hfinite (hi.const_mul (internalSquareScale M / m)) hexp
  rw [integral_const_mul] at h
  have hlog := log_le_log (integral_exp_pos hexp) (internalScalarCurrent_exp_square_le hM hb hbound i)
  have hn : 0 ≤ (klDiv P (Measure.pi fun _ : Fin m ↦ r)).toReal := ENNReal.toReal_nonneg
  have hbound' : internalSquareScale M / m * (∫ x, internalScalarCurrent r b i x ^ 2 ∂P) ≤
      (1 + |log (exp 1 * squareExponentialConstant)|) *
        (1 + (klDiv P (Measure.pi fun _ : Fin m ↦ r)).toReal) := by
    nlinarith [le_abs_self (log (exp 1 * squareExponentialConstant)),
      abs_nonneg (log (exp 1 * squareExponentialConstant)),
      mul_nonneg hn (abs_nonneg (log (exp 1 * squareExponentialConstant)))]
  apply (mul_le_mul_iff_of_pos_left hα).mp
  calc
    _ ≤ _ := hbound'
    _ = _ := by
      unfold internalSourceConstant
      field_simp [ne_of_gt hm, ne_of_gt hscalePos]

/-- The Euclidean square of a vector internal sum is the sum of the squares
of its scalar coordinates. This definition uses the product Euclidean metric. -/
def internalCurrentSquare {A : Type*} [MeasurableSpace A] {m d : ℕ}
    (r : Measure A) (b : A → A → Fin d → ℝ) (i : Fin m) (x : Fin m → A) : ℝ :=
  ∑ a, internalScalarCurrent r (fun u v ↦ b u v a) i x ^ 2

theorem integrable_internalCurrentSquare {A : Type*} [MeasurableSpace A]
    {r : Measure A} [IsProbabilityMeasure r] {m d : ℕ} {b : A → A → Fin d → ℝ} {M : ℝ}
    (hb : Measurable (Function.uncurry b)) (hbound : ∀ x y a, |b x y a| ≤ M)
    (i : Fin m) (P : Measure (Fin m → A)) [IsFiniteMeasure P] :
    Integrable (internalCurrentSquare r b i) P := by
  apply integrable_finsetSum
  intro a _
  exact integrable_internalScalarCurrent_sq (r := r) (b := fun u v ↦ b u v a) ((measurable_pi_apply a).comp hb)
    (fun x y ↦ hbound x y a) i P

/-- Actual vector-valued internal source energy. Boundedness and finite KL
are the only quantitative hypotheses; concentration and the diagonal estimate
are derived in this module. The constant depends only on M and the dimension. -/
theorem internal_source_energy_le_entropy {A : Type*} [MeasurableSpace A]
    {r : Measure A} [IsProbabilityMeasure r] {m d N : ℕ} {b : A → A → Fin d → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hb : Measurable (Function.uncurry b)) (hbound : ∀ x y a, |b x y a| ≤ M)
    {P : Measure (Fin m → A)} [IsProbabilityMeasure P]
    (hfinite : klDiv P (Measure.pi fun _ : Fin m ↦ r) ≠ ∞) :
    (∫ x, ∑ i : Fin m, internalCurrentSquare r b i x ∂P) / (N : ℝ) ^ 2 ≤
      (d * internalSourceConstant M) * (m : ℝ) ^ 2 / (N : ℝ) ^ 2 *
        (1 + (klDiv P (Measure.pi fun _ : Fin m ↦ r)).toReal) := by
  have hrow (i : Fin m) : ∫ x, internalCurrentSquare r b i x ∂P ≤
      d * internalSourceConstant M * m * (1 + (klDiv P (Measure.pi fun _ : Fin m ↦ r)).toReal) := by
    unfold internalCurrentSquare
    rw [integral_finsetSum _ (fun a _ ↦ integrable_internalScalarCurrent_sq (r := r) (b := fun u v ↦ b u v a)
      ((measurable_pi_apply a).comp hb) (fun x y ↦ hbound x y a) i P)]
    calc
      _ ≤ ∑ _a : Fin d, internalSourceConstant M * m *
          (1 + (klDiv P (Measure.pi fun _ : Fin m ↦ r)).toReal) :=
        Finset.sum_le_sum (fun a _ ↦ internalScalarCurrent_sq_le_entropy (r := r) (b := fun u v ↦ b u v a) hM
          ((measurable_pi_apply a).comp hb) (fun x y ↦ hbound x y a) i hfinite)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  rw [integral_finsetSum _ (fun i _ ↦ integrable_internalCurrentSquare (r := r) hb hbound i P)]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hrow i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have h := div_le_div_of_nonneg_right hsum (sq_nonneg (N : ℝ))
  calc
    _ ≤ (m * (d * internalSourceConstant M * m *
        (1 + (klDiv P (Measure.pi fun _ : Fin m ↦ r)).toReal))) / (N : ℝ) ^ 2 := h
    _ = _ := by ring

end SharpWasserstein
