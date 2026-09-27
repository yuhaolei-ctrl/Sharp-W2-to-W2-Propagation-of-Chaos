import SharpWasserstein.GaussianHistoryMarginals
import SharpWasserstein.EulerBridge
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Dimension-free entropy cost of finite Gaussian meeting bridges
The coordinate drift is measured with its genuine Euclidean norm. The initial
coupling labels are retained by the history law, so every control moment is
integrated against that coupling, not an uncontrolled comparison law. -/
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped ENNReal NNReal BigOperators
namespace SharpWasserstein.GaussianBridge

abbrev Labels (d : ℕ) := Position d × Position d
abbrev History (d j : ℕ) := GaussianHistory (Labels d) d j

def displacementSq {d : ℕ} (z : Labels d) : ℝ := ∑ i, (z.2 i - z.1 i)^2

def euclideanDrift {d : ℕ} (v : ℝ → Position d → Position d) (t : ℝ)
    (z : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (v t (WithLp.ofLp z))

/-- Initial position before the first transition, or the last generated state. -/
def state {d : ℕ} : (j : ℕ) → History d j → Position d
  | 0, h => h.1.1
  | j+1, h => h.2 (Fin.last j)

theorem measurable_state {d : ℕ} (j : ℕ) : Measurable (state (d := d) j) := by
  cases j <;> unfold state <;> fun_prop

def ordinaryMean {d : ℕ} (v : ℝ → Position d → Position d) (δ : ℝ≥0)
    (j : ℕ) (h : History d j) : Position d :=
  state j h + (δ : ℝ) • v ((j : ℝ) * δ) (state j h)

def shiftedMean {d : ℕ} (v : ℝ → Position d → Position d) (T : ℝ) (δ : ℝ≥0)
    (j : ℕ) (h : History d j) : Position d :=
  state j h + (δ : ℝ) • EulerBridge.shiftedDrift v h.1.1 h.1.2 T ((j : ℝ)*δ) (state j h)

theorem measurable_ordinaryMean {d : ℕ} {v : ℝ → Position d → Position d}
    (hv : ∀ t, Measurable (v t)) (δ : ℝ≥0) (j : ℕ) : Measurable (ordinaryMean v δ j) :=
  (measurable_state j).add (((hv _).comp (measurable_state j)).const_smul (δ : ℝ))

theorem measurable_shiftedMean {d : ℕ} {v : ℝ → Position d → Position d}
    (hv : ∀ t, Measurable (v t)) (T : ℝ) (δ : ℝ≥0) (j : ℕ) :
    Measurable (shiftedMean v T δ j) := by
  have hdisp : Measurable (fun h : History d j ↦ h.1.2 - h.1.1) :=
    (measurable_snd.comp measurable_fst).sub (measurable_fst.comp measurable_fst)
  exact (measurable_state j).add ((((hv _).comp ((measurable_state j).add
    (hdisp.const_smul (1 - (j : ℝ) * δ / T)))).add (hdisp.const_smul T⁻¹)).const_smul (δ : ℝ))

theorem measurable_displacementSq (d : ℕ) : Measurable (displacementSq (d := d)) := by
  unfold displacementSq
  fun_prop

theorem displacementSq_nonneg {d : ℕ} (z : Labels d) : 0 ≤ displacementSq z :=
  Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- The drift-control bound in the exact Euclidean coordinate square. -/
theorem drift_difference_square_le {d : ℕ} {v : ℝ → Position d → Position d}
    (x y z : Position d) {T t : ℝ} {K : ℝ≥0}
    (hl : LipschitzWith K (euclideanDrift v t)) (hT : 0 < T) (ht : t ∈ Icc 0 T) :
    (∑ i, (v t z i - EulerBridge.shiftedDrift v x y T t z i)^2) ≤
      (RegularizationRates.bridgeRate K T t)^2 * displacementSq (x,y) := by
  let X : ℝ → EuclideanSpace ℝ (Fin d) := fun _ ↦ WithLp.toLp 2 z
  have h := ControlledBridge.control_norm_le (X := X) (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    hl hT ht
  have he : ControlledBridge.control (euclideanDrift v) X (WithLp.toLp 2 x) (WithLp.toLp 2 y) T t =
      WithLp.toLp 2 (v t z - EulerBridge.shiftedDrift v x y T t z) := by
    ext i
    change v t z i - v t (z + (1 - t/T) • (y-x)) i - T⁻¹ * (y i - x i) =
      v t z i - (v t (z + (1 - t/T) • (y-x)) i + T⁻¹ * (y i - x i))
    ring
  rw [he] at h
  have hr : 0 ≤ RegularizationRates.bridgeRate K T t := by
    unfold RegularizationRates.bridgeRate
    exact add_nonneg (mul_nonneg K.coe_nonneg (sub_nonneg.mpr ((div_le_one hT).mpr ht.2)))
      (by positivity)
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hr (norm_nonneg _))).mpr h
  simpa only [mul_pow, EuclideanSpace.real_norm_sq_eq, PiLp.sub_apply, Pi.sub_apply,
    displacementSq] using hs

/-- Exact single-transition cost bound with the `sqrt(2)` noise coefficient. -/
theorem transition_cost_le {d : ℕ} {v : ℝ → Position d → Position d}
    {T : ℝ} {δ : ℝ≥0} (hδ : δ ≠ 0) {K : ℝ≥0}
    (hl : ∀ t, LipschitzWith K (euclideanDrift v t)) (hT : 0 < T)
    (j : ℕ) (hj : (j : ℝ) * δ ≤ T) (h : History d j) :
    (∑ i, (ordinaryMean v δ j h i - shiftedMean v T δ j h i)^2 / (2 * (2 * (δ : ℝ)))) ≤
      ((δ : ℝ) / 4 * (RegularizationRates.bridgeRate K T ((j : ℝ)*δ))^2) * displacementSq h.1 := by
  have hd : (δ : ℝ) ≠ 0 := by exact_mod_cast hδ
  have he : (∑ i, (ordinaryMean v δ j h i - shiftedMean v T δ j h i)^2 / (2 * (2 * (δ : ℝ)))) =
      (δ : ℝ)/4 * ∑ i, (v ((j : ℝ)*δ) (state j h) i -
        EulerBridge.shiftedDrift v h.1.1 h.1.2 T ((j : ℝ)*δ) (state j h) i)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [ordinaryMean, shiftedMean, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  rw [he, mul_assoc]
  exact mul_le_mul_of_nonneg_left (drift_difference_square_le h.1.1 h.1.2 (state j h)
    (hl _) hT ⟨by positivity, hj⟩) (by positivity)

/-- The genuine first Gaussian history law of the two meeting-bridge schemes. -/
def ordinaryLaw {d : ℕ} (γ : Measure (Labels d))
    (v : ℝ → Position d → Position d) (hv : ∀ t, Measurable (v t)) (δ : ℝ≥0) (j : ℕ) :=
  gaussianHistoryLaw (gaussianInitialHistory d γ) (ordinaryMean v δ)
    (measurable_ordinaryMean hv δ) (fun _ ↦ 2 * δ) j

/-- The comparison uses the same initial labels and the shifted drift. -/
def shiftedLaw {d : ℕ} (γ : Measure (Labels d))
    (v : ℝ → Position d → Position d) (hv : ∀ t, Measurable (v t)) (T : ℝ) (δ : ℝ≥0) (j : ℕ) :=
  gaussianHistoryLaw (gaussianInitialHistory d γ) (shiftedMean v T δ)
    (measurable_shiftedMean hv T δ) (fun _ ↦ 2 * δ) j

def transitionCost {d : ℕ} (v : ℝ → Position d → Position d) (T : ℝ) (δ : ℝ≥0)
    (j : ℕ) (h : History d j) : ℝ :=
  ∑ i, (ordinaryMean v δ j h i - shiftedMean v T δ j h i)^2 / (2 * (2 * (δ : ℝ)))

theorem measurable_transitionCost {d : ℕ} {v : ℝ → Position d → Position d}
    (hv : ∀ t, Measurable (v t)) (T : ℝ) (δ : ℝ≥0) (j : ℕ) :
    Measurable (transitionCost v T δ j) := by
  have ha := measurable_ordinaryMean hv δ j
  have hb := measurable_shiftedMean hv T δ j
  unfold transitionCost
  fun_prop

/-- Finite second moment of the initial displacement suffices for every
transition control cost; no trajectory moment bound is assumed. -/
theorem transitionCost_integrable {d : ℕ} (γ : Measure (Labels d)) [IsProbabilityMeasure γ]
    {v : ℝ → Position d → Position d} (hv : ∀ t, Measurable (v t))
    {T : ℝ} {δ : ℝ≥0} (hδ : δ ≠ 0) {K : ℝ≥0}
    (hl : ∀ t, LipschitzWith K (euclideanDrift v t)) (hT : 0 < T)
    (hi : Integrable displacementSq γ) (j : ℕ) (hj : (j : ℝ)*δ ≤ T) :
    Integrable (transitionCost v T δ j) (ordinaryLaw γ v hv δ j) := by
  have hlabel := gaussianHistory_label_integrable γ (ordinaryMean v δ)
    (measurable_ordinaryMean hv δ) (fun _ ↦ 2*δ) j (measurable_displacementSq d) hi
  refine (hlabel.const_mul ((δ : ℝ)/4 * (RegularizationRates.bridgeRate K T ((j : ℝ)*δ))^2)).mono'
    (measurable_transitionCost hv T δ j).aestronglyMeasurable (Filter.Eventually.of_forall fun h ↦ ?_)
  rw [norm_eq_abs, abs_of_nonneg (show 0 ≤ transitionCost v T δ j h from
    Finset.sum_nonneg fun _ _ ↦ by positivity)]
  exact transition_cost_le hδ hl hT j hj h

/-- Every cost expectation is bounded under the first law by the unchanged
initial coupling displacement. -/
theorem integral_transitionCost_le {d : ℕ} (γ : Measure (Labels d)) [IsProbabilityMeasure γ]
    {v : ℝ → Position d → Position d} (hv : ∀ t, Measurable (v t))
    {T : ℝ} {δ : ℝ≥0} (hδ : δ ≠ 0) {K : ℝ≥0}
    (hl : ∀ t, LipschitzWith K (euclideanDrift v t)) (hT : 0 < T)
    (hi : Integrable displacementSq γ) (j : ℕ) (hj : (j : ℝ)*δ ≤ T) :
    (∫ h, transitionCost v T δ j h ∂ordinaryLaw γ v hv δ j) ≤
      ((δ : ℝ)/4 * (RegularizationRates.bridgeRate K T ((j : ℝ)*δ))^2) * ∫ z, displacementSq z ∂γ := by
  have hlabel := gaussianHistory_label_integrable γ (ordinaryMean v δ)
    (measurable_ordinaryMean hv δ) (fun _ ↦ 2*δ) j (measurable_displacementSq d) hi
  calc
    _ ≤ ∫ h, ((δ : ℝ)/4 * (RegularizationRates.bridgeRate K T ((j : ℝ)*δ))^2) *
        displacementSq h.1 ∂ordinaryLaw γ v hv δ j :=
      integral_mono (transitionCost_integrable γ hv hδ hl hT hi j hj)
        (hlabel.const_mul _) (transition_cost_le hδ hl hT j hj)
    _ = _ := by
      rw [integral_const_mul]
      congr 1
      exact gaussianHistory_label_integral γ (ordinaryMean v δ)
        (measurable_ordinaryMean hv δ) (fun _ ↦ 2*δ) j (measurable_displacementSq d)

/-- Full finite Gaussian history entropy is bounded by the quarter Riemann sum
of the squared bridge rate times the initial coupling's Euclidean displacement. -/
theorem history_entropy_le {d : ℕ} (γ : Measure (Labels d)) [IsProbabilityMeasure γ]
    {v : ℝ → Position d → Position d} (hv : ∀ t, Measurable (v t))
    {T : ℝ} {δ : ℝ≥0} (hδ : δ ≠ 0) {K : ℝ≥0}
    (hl : ∀ t, LipschitzWith K (euclideanDrift v t)) (hT : 0 < T)
    (hi : Integrable displacementSq γ) (n : ℕ) (hgrid : (n : ℝ)*δ ≤ T) :
    klDiv (ordinaryLaw γ v hv δ n) (shiftedLaw γ v hv T δ n) ≤
      ENNReal.ofReal (((δ : ℝ)/4 * ∑ j ∈ Finset.range n,
        (RegularizationRates.bridgeRate K T ((j : ℝ)*δ))^2) * ∫ z, displacementSq z ∂γ) := by
  have hj (j : ℕ) (hjn : j < n) : (j : ℝ)*δ ≤ T :=
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hjn.le) δ.coe_nonneg).trans hgrid
  have hcost (j : ℕ) (hjn : j < n) : Integrable
      (fun h ↦ ∑ i, (ordinaryMean v δ j h i - shiftedMean v T δ j h i)^2 /
        (2 * ((fun _ : ℕ ↦ 2*δ) j : ℝ)))
      (gaussianHistoryLaw (gaussianInitialHistory d γ) (ordinaryMean v δ)
        (measurable_ordinaryMean hv δ) (fun _ ↦ 2*δ) j) := by
    simp only [NNReal.coe_mul, NNReal.coe_ofNat]
    exact transitionCost_integrable γ hv hδ hl hT hi j (hj j hjn)
  have he := klDiv_gaussianHistoryLaw_same_initial (gaussianInitialHistory d γ)
    (ordinaryMean v δ) (shiftedMean v T δ) (measurable_ordinaryMean hv δ)
    (measurable_shiftedMean hv T δ) (fun _ ↦ 2*δ) (fun _ ↦ mul_ne_zero (by norm_num) hδ) n hcost
  change klDiv (gaussianHistoryLaw _ _ _ _ _) (gaussianHistoryLaw _ _ _ _ _) ≤ _
  rw [he]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∑ j ∈ Finset.range n, ((δ : ℝ)/4 * (RegularizationRates.bridgeRate K T ((j : ℝ)*δ))^2) *
        ∫ z, displacementSq z ∂γ := by
      apply Finset.sum_le_sum
      intro j hjn
      simpa only [NNReal.coe_mul, NNReal.coe_ofNat, transitionCost, ordinaryLaw] using
        integral_transitionCost_le γ hv hδ hl hT hi j (hj j (Finset.mem_range.mp hjn))
    _ = _ := by simp only [Finset.sum_mul, Finset.mul_sum]

/-- Any measurable endpoint observation obeys the proved history bound. -/
theorem observation_entropy_le {E : Type*} [MeasurableSpace E] {d : ℕ}
    (γ : Measure (Labels d)) [IsProbabilityMeasure γ]
    {v : ℝ → Position d → Position d} (hv : ∀ t, Measurable (v t))
    {T : ℝ} {δ : ℝ≥0} (hδ : δ ≠ 0) {K : ℝ≥0}
    (hl : ∀ t, LipschitzWith K (euclideanDrift v t)) (hT : 0 < T)
    (hi : Integrable displacementSq γ) (n : ℕ) (hgrid : (n : ℝ)*δ ≤ T)
    (f : History d n → E) (hf : Measurable f) :
    klDiv ((ordinaryLaw γ v hv δ n).map f) ((shiftedLaw γ v hv T δ n).map f) ≤
      ENNReal.ofReal (((δ : ℝ)/4 * ∑ j ∈ Finset.range n,
        (RegularizationRates.bridgeRate K T ((j : ℝ)*δ))^2) * ∫ z, displacementSq z ∂γ) := by
  haveI : IsProbabilityMeasure (ordinaryLaw γ v hv δ n) := inferInstanceAs
    (IsProbabilityMeasure (gaussianHistoryLaw _ _ _ _ _))
  haveI : IsProbabilityMeasure (shiftedLaw γ v hv T δ n) := inferInstanceAs
    (IsProbabilityMeasure (gaussianHistoryLaw _ _ _ _ _))
  exact (klDiv_map_le hf).trans (history_entropy_le γ hv hδ hl hT hi n hgrid)

end SharpWasserstein.GaussianBridge
