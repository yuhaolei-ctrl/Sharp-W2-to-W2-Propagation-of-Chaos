import SharpWasserstein.RegularizedTrialEnergy
import SharpWasserstein.WeightedGradientApproximation

/-! A finite family of actual smooth potentials gives a bounded coefficient
map into the true weighted Euclidean L² space of any finite measure. This
construction retains duplicate and constant atoms and needs no density. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace BigOperators
namespace SharpWasserstein.FiniteGradientTrial
open WeightedTangent
variable {n : ℕ} {ι : Type*} [Fintype ι]
  [MeasurableSpace (Point n)] [BorelSpace (Point n)]
  (μ : Measure (Point n)) [IsFiniteMeasure μ]
  (a : ι → Point n → ℝ) (ha : ∀ i, ContDiff ℝ ∞ (a i))
  (hB : ∀ i, ∃ B : ℝ, ∀ x, ‖gradient (a i) x‖ ≤ B)

def atomGradient (i : ι) : Lp (Point n) 2 μ :=
  (bounded_smooth_gradient_memLp μ (a i) (ha i) (hB i)).toLp (gradient (a i))

omit [Fintype ι] in
theorem atomGradient_ae (i : ι) : atomGradient μ a ha hB i =ᵐ[μ] gradient (a i) :=
  (bounded_smooth_gradient_memLp μ (a i) (ha i) (hB i)).coeFn_toLp

def gradientMap : EuclideanSpace ℝ ι →L[ℝ] Lp (Point n) 2 μ :=
  ∑ i, (EuclideanSpace.proj i).smulRight (atomGradient μ a ha hB i)

theorem gradientMap_apply (c : EuclideanSpace ℝ ι) :
    gradientMap μ a ha hB c = ∑ i, c i • atomGradient μ a ha hB i := by
  simp only [gradientMap,sum_apply,ContinuousLinearMap.smulRight_apply]
  rfl

omit [MeasurableSpace (Point n)] [BorelSpace (Point n)] in
def potential (c : EuclideanSpace ℝ ι) : Point n → ℝ := ∑ i, c i • a i

include ha in
omit [MeasurableSpace (Point n)] [BorelSpace (Point n)] in
theorem potential_smooth (c : EuclideanSpace ℝ ι) : ContDiff ℝ ∞ (potential a c) := by
  convert (ContDiff.sum (s := Finset.univ) fun i _ => (ha i).const_smul (c i)) using 1
  funext x
  simp only [potential,Finset.sum_apply,Pi.smul_apply]

include ha in
omit [MeasurableSpace (Point n)] [BorelSpace (Point n)] in
theorem potential_gradient (c : EuclideanSpace ℝ ι) (x : Point n) :
    gradient (potential a c) x = ∑ i, c i • gradient (a i) x := by
  unfold potential gradient
  have hd (i : ι) (_ : i ∈ Finset.univ) : DifferentiableAt ℝ (c i • a i) x := by
    change DifferentiableAt ℝ (fun y => c i • a i y) x
    exact ((ha i).const_smul (c i)).differentiable (by simp) x
  rw [fderiv_sum hd]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [congrFun (fderiv_const_smul_field (𝕜 := ℝ) (c i)) x]
  simp only [Pi.smul_apply,map_smul]

theorem gradientMap_ae (c : EuclideanSpace ℝ ι) :
    gradientMap μ a ha hB c =ᵐ[μ] gradient (potential a c) := by
  rw [gradientMap_apply]
  have hsum := Lp.coeFn_fun_finsetSum Finset.univ (fun i : ι => c i • atomGradient μ a ha hB i)
  have hsm : ∀ᵐ x ∂μ, ∀ i : ι,
      (c i • atomGradient μ a ha hB i) x = c i • gradient (a i) x := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [Lp.coeFn_smul (c i) (atomGradient μ a ha hB i),atomGradient_ae μ a ha hB i] with x hx hy
    rw [hx,Pi.smul_apply,hy]
  filter_upwards [hsum,hsm] with x hx hy
  rw [hx,potential_gradient a ha]
  exact Finset.sum_congr rfl fun i _ => hy i

theorem gradientMap_norm_sq (c : EuclideanSpace ℝ ι) :
    ‖gradientMap μ a ha hB c‖^2 = ∫ x,‖gradient (potential a c) x‖^2 ∂μ := by
  rw [lp_norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [gradientMap_ae μ a ha hB c] with x hx
  rw [hx]

end SharpWasserstein.FiniteGradientTrial
