module

public import SharpWasserstein.Compat
public import SharpWasserstein.WeightedPeriodicFourierApproximation

@[expose] public section

/-! Positive-period Fourier tests in the original Euclidean coordinates.
Only the test functions are dilated; the carrying law, diffusion coefficient,
and drift Jacobian are not silently rescaled. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff BigOperators
namespace SharpWasserstein.WeightedPeriodicFourierScale
open PeriodicIntegrationByParts PeriodicFourierTests PeriodicFourierPolynomials
open WeightedPeriodicFourier
variable {n : ℕ}

/-- Actual period P in each ordinary coordinate. -/
def PeriodicOf (P : ℝ) (f : Coordinates n → ℝ) : Prop :=
  ∀ i, Function.Periodic f (Pi.single i P)

def dilation (P : ℝ) : Coordinates n →L[ℝ] Coordinates n :=
  P • ContinuousLinearMap.id ℝ (Coordinates n)

def rescale (P : ℝ) (f : Coordinates n → ℝ) : Coordinates n → ℝ :=
  f ∘ dilation P

def rescaleLinear (P : ℝ) : (Coordinates n → ℝ) →ₗ[ℝ] (Coordinates n → ℝ) where
  toFun := rescale P
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem rescale_apply (P : ℝ) (f : Coordinates n → ℝ) (x : Coordinates n) :
    rescale P f x = f (P • x) := rfl

theorem rescale_smooth (P : ℝ) {f : Coordinates n → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (rescale P f) := hf.comp (dilation P).contDiff

theorem rescale_inverse {P : ℝ} (hP : P ≠ 0) (f : Coordinates n → ℝ) :
    rescale P⁻¹ (rescale P f) = f := by
  funext x
  simp only [rescale_apply,smul_smul,mul_inv_cancel₀ hP,one_smul]

theorem rescale_periodic {P : ℝ} {f : Coordinates n → ℝ} (hp : PeriodicOf P f) :
    Periodic (rescale P f) := by
  intro i x
  simp only [rescale_apply,smul_add]
  have he : P • Pi.single i (1 : ℝ) = Pi.single i P := by
    ext j
    by_cases hj : j = i <;> simp [hj]
  rw [he]
  exact hp i (P • x)

theorem rescale_inverse_periodic {P : ℝ} (hP : P ≠ 0) {f : Coordinates n → ℝ}
    (hp : Periodic f) : PeriodicOf P (rescale P⁻¹ f) := by
  intro i x
  simp only [rescale_apply,smul_add]
  have he : P⁻¹ • Pi.single i P = Pi.single i (1 : ℝ) := by
    ext j
    by_cases hj : j = i <;> simp [hj,hP]
  rw [he]
  exact hp i (P⁻¹ • x)

/-- The coordinate chain rule retains the actual dilation factor. -/
theorem coordinatePartial_rescale (P : ℝ) {f : Coordinates n → ℝ}
    (hf : Differentiable ℝ f) (i : Fin n) (x : Coordinates n) :
    coordinatePartial (rescale P f) i x = P*coordinatePartial f i (P • x) := by
  unfold coordinatePartial rescale
  rw [fderiv_comp x (hf _) (dilation P).differentiableAt,ContinuousLinearMap.fderiv]
  change (fderiv ℝ f (P • x)) (P • Pi.single i 1) = _
  rw [map_smul]
  rfl

theorem partial_rescale_eq (P : ℝ) {f : Coordinates n → ℝ} (hf : Differentiable ℝ f)
    (i : Fin n) : coordinatePartial (rescale P f) i = P • rescale P (coordinatePartial f i) := by
  funext x
  exact coordinatePartial_rescale P hf i x

/-- Actual Laplacian scaling, derived from two genuine coordinate derivatives. -/
theorem laplacian_rescale (P : ℝ) {f : Coordinates n → ℝ} (hf : ContDiff ℝ ∞ f) :
    PeriodicIntegrationByParts.laplacian (rescale P f) = P^2 • rescale P (PeriodicIntegrationByParts.laplacian f) := by
  funext x
  unfold PeriodicIntegrationByParts.laplacian
  simp only [partial_rescale_eq P (hf.differentiable (by simp)),coordinatePartial_smul,
    Pi.smul_apply,smul_eq_mul,rescale_apply]
  simp_rw [coordinatePartial_rescale P ((smooth_coordinatePartial hf _).differentiable (by simp))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A finite trial space whose atoms have the specified physical period. -/
def frequencySpace (P : ℝ) (s : Finset ((Fin n → ℤ) × Bool)) :
    Submodule ℝ (Coordinates n → ℝ) :=
  (PeriodicFourierTests.frequencySpace s).map (rescaleLinear P⁻¹)

def atom (P : ℝ) (k : (Fin n → ℤ) × Bool) : Coordinates n → ℝ :=
  rescale P⁻¹ (PeriodicFourierTests.atom k)

theorem atom_smooth (P : ℝ) (k : (Fin n → ℤ) × Bool) : ContDiff ℝ ∞ (atom P k) :=
  rescale_smooth P⁻¹ (smooth_atom k)

theorem atom_periodic {P : ℝ} (hP : P ≠ 0) (k : (Fin n → ℤ) × Bool) :
    PeriodicOf P (atom P k) := rescale_inverse_periodic hP (periodic_atom k)

/-- The concrete physical-period eigenvalue is Λ/P². -/
theorem laplacian_atom (P : ℝ) (k : (Fin n → ℤ) × Bool) :
    PeriodicIntegrationByParts.laplacian (atom P k) = (-(eigenvalue k.1 / P^2)) • atom P k := by
  rw [atom,laplacian_rescale P⁻¹ (smooth_atom k),PeriodicFourierTests.laplacian_atom]
  funext x
  simp only [Pi.smul_apply,rescale_apply,smul_eq_mul]
  ring

theorem frequencySpace_properties {P : ℝ} (hP : P ≠ 0)
    (s : Finset ((Fin n → ℤ) × Bool)) {f : Coordinates n → ℝ}
    (hf : f ∈ frequencySpace P s) : ContDiff ℝ ∞ f ∧ PeriodicOf P f := by
  obtain ⟨g,hg,rfl⟩ := hf
  have hp := PeriodicFourierTests.frequencySpace_properties s hg
  exact ⟨rescale_smooth P⁻¹ hp.1,rescale_inverse_periodic hP hp.2.1⟩

/-- Every smooth physical-period potential has actual finite Fourier C¹
approximants in the same physical coordinates and period. -/
theorem exists_frequencySpace_uniform_C1 {P : ℝ} (hP : 0 < P)
    (f : Coordinates n → ℝ) (hp : PeriodicOf P f) (hf : ContDiff ℝ ∞ f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (s : Finset (Fin n → ℤ)) (p : Coordinates n → ℝ),
      p ∈ frequencySpace P (frequencySet s) ∧
      (∀ y, |p y-f y| < ε) ∧
      (∀ i y, |coordinatePartial p i y-coordinatePartial f i y| < ε) := by
  let η : ℝ := min ε (P*ε)
  have hη : 0 < η := lt_min hε (mul_pos hP hε)
  obtain ⟨s,q,hq,hq0,hq1⟩ := WeightedPeriodicFourier.exists_frequencySpace_uniform_C1
    (rescale P f) (rescale_periodic hp) (rescale_smooth P hf) hη
  have hqs := (PeriodicFourierTests.frequencySpace_properties (frequencySet s) hq).1
  refine ⟨s,rescale P⁻¹ q,⟨q,hq,rfl⟩,?_,?_⟩
  · intro y
    have he := hq0 (P⁻¹ • y)
    simp only [rescale_apply,smul_smul,mul_inv_cancel₀ hP.ne',one_smul] at he
    exact he.trans_le (min_le_left _ _)
  · intro i y
    have he := hq1 i (P⁻¹ • y)
    rw [coordinatePartial_rescale P⁻¹ (hqs.differentiable (by simp))]
    have hc : P⁻¹*coordinatePartial (rescale P f) i (P⁻¹ • y) = coordinatePartial f i y := by
      rw [coordinatePartial_rescale P (hf.differentiable (by simp)),smul_smul,
        mul_inv_cancel₀ hP.ne',one_smul,← mul_assoc,inv_mul_cancel₀ hP.ne',one_mul]
    have hnorm : |P⁻¹*coordinatePartial q i (P⁻¹ • y)-coordinatePartial f i y| =
        P⁻¹*|coordinatePartial q i (P⁻¹ • y)-coordinatePartial (rescale P f) i (P⁻¹ • y)| := by
      calc
        _ = |P⁻¹*coordinatePartial q i (P⁻¹ • y)-
            P⁻¹*coordinatePartial (rescale P f) i (P⁻¹ • y)| := by rw [hc]
        _ = _ := by rw [← mul_sub,abs_mul,abs_of_pos (inv_pos.mpr hP)]
    rw [hnorm]
    calc
      _ < P⁻¹*η := mul_lt_mul_of_pos_left he (inv_pos.mpr hP)
      _ ≤ P⁻¹*(P*ε) := mul_le_mul_of_nonneg_left (min_le_right _ _) (inv_nonneg.mpr hP.le)
      _ = ε := by rw [← mul_assoc,inv_mul_cancel₀ hP.ne',one_mul]

end SharpWasserstein.WeightedPeriodicFourierScale
